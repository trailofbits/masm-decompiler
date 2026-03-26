//! Intraprocedural type inference and mismatch checking.

use std::collections::HashMap;

use miden_assembly_syntax::debuginfo::SourceSpan;

use crate::ir::{BinOp, Constant, Expr, Stmt, UnOp, ValueId, Var};
use crate::symbol::path::SymbolPath;

use super::domain::{TypeFact, VarKey};
use super::summary::{TypeDiagnostic, TypeSummary, TypeSummaryMap};

/// Maximum number of fixed-point iterations for local type inference.
const MAX_TYPE_PASSES: usize = 128;

/// Upper bound (exclusive) of the valid Miden VM memory address range.
///
/// Memory addresses must be in `[0, 2^32)`. Operations like `mem_load`
/// and `mem_store` trap at runtime if the address is `>= 2^32`.
const MAX_MEMORY_ADDRESS: u64 = 1u64 << 32;

/// Abstract memory address identity for type tracking.
///
/// Two memory operations target the same logical address when they share
/// the same `MemAddressKey`. This is necessary because the lifter creates
/// distinct SSA variables for each address operand, even when they refer
/// to the same constant or `locaddr` result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum MemAddressKey {
    /// Constant address known to be in the valid memory range `[0, 2^32)`.
    ///
    /// Stored as `u32` to enforce the range invariant at the type level.
    /// Created from `Constant::Felt(n)` assignments where `n < 2^32`.
    Constant(u32),
    /// Local-mapped address (from `locaddr.N`).
    LocalAddr(u16),
    /// Local-mapped address offset by a known constant (from `locaddr.N + k`).
    ///
    /// Only created for `Add` operations (not `Sub`), because field `sub`
    /// computes `(a - b) mod p` which can wrap to addresses outside the
    /// procedure's local frame.
    ///
    /// The absolute address is not known at analysis time, but two operations
    /// sharing the same `(local_index, offset)` target the same location.
    LocalAddrOffset(u16, u32),
}

/// Output of type analysis for a single procedure.
#[derive(Debug, Clone)]
pub struct ProcTypeAnalysisResult {
    /// Inferred procedure summary.
    pub summary: TypeSummary,
    /// Type mismatch diagnostics found in the procedure body.
    pub diagnostics: Vec<TypeDiagnostic>,
}

/// Analyze a single procedure body and infer its [TypeSummary].
pub fn analyze_proc_types(
    proc_path: &SymbolPath,
    input_count: usize,
    output_count: usize,
    stmts: &[Stmt],
    callee_summaries: &TypeSummaryMap,
) -> ProcTypeAnalysisResult {
    let mut analyzer = ProcTypeAnalyzer::new(
        proc_path.clone(),
        input_count,
        output_count,
        callee_summaries,
    );
    analyzer.analyze(stmts)
}

/// Internal fixed-point analyzer for one procedure.
struct ProcTypeAnalyzer<'a> {
    /// Fully-qualified procedure name.
    proc_path: SymbolPath,
    /// Number of stack inputs.
    input_count: usize,
    /// Number of stack outputs.
    output_count: usize,
    /// Previously inferred summaries for callees.
    callee_summaries: &'a TypeSummaryMap,
    /// Inferred type guarantees for variables.
    inferred: HashMap<VarKey, TypeFact>,
    /// Inferred requirements for variables.
    required: HashMap<VarKey, TypeFact>,
    /// Collected diagnostics.
    diagnostics: Vec<TypeDiagnostic>,
    /// Inferred types for local variable slots.
    ///
    /// Updated on `LocalStore`/`LocalStoreW` and read on `LocalLoad`.
    /// The fixed-point loop ensures convergence when stored types change
    /// across iterations.
    local_types: HashMap<u16, TypeFact>,
    /// Maps SSA variables to their abstract memory address identity.
    ///
    /// Populated during inference when a variable is defined as a constant
    /// (`Assign { expr: Constant(Felt(n)) }`) or a `locaddr.N` intrinsic
    /// result. Also propagated through variable copies
    /// (`Assign { expr: Var(src) }`).
    var_address_keys: HashMap<VarKey, MemAddressKey>,
    /// Inferred types for memory locations, keyed by abstract address.
    mem_types: HashMap<MemAddressKey, TypeFact>,
    /// Requirements propagated backward to local variable slots.
    local_requirements: HashMap<u16, TypeFact>,
    /// Requirements propagated backward to memory locations.
    mem_requirements: HashMap<MemAddressKey, TypeFact>,
}

impl<'a> ProcTypeAnalyzer<'a> {
    /// Construct a new analyzer.
    fn new(
        proc_path: SymbolPath,
        input_count: usize,
        output_count: usize,
        callee_summaries: &'a TypeSummaryMap,
    ) -> Self {
        Self {
            proc_path,
            input_count,
            output_count,
            callee_summaries,
            inferred: HashMap::new(),
            required: HashMap::new(),
            diagnostics: Vec::new(),
            local_types: HashMap::new(),
            var_address_keys: HashMap::new(),
            mem_types: HashMap::new(),
            local_requirements: HashMap::new(),
            mem_requirements: HashMap::new(),
        }
    }

    /// Run fixed-point inference and mismatch checks.
    fn analyze(&mut self, stmts: &[Stmt]) -> ProcTypeAnalysisResult {
        for _ in 0..MAX_TYPE_PASSES {
            let prev_inferred = self.inferred.clone();
            let prev_required = self.required.clone();
            let prev_local_types = self.local_types.clone();
            let prev_mem_types = self.mem_types.clone();
            let prev_local_req = self.local_requirements.clone();
            let prev_mem_req = self.mem_requirements.clone();
            let prev_addr_keys = self.var_address_keys.clone();

            // Return values are intentionally discarded: convergence is
            // detected by comparing full state snapshots (below), not by
            // per-call `changed` flags, which can oscillate within a pass.
            let _ = self.infer_types_in_block(stmts);
            let _ = self.seed_requirements_in_block(stmts);
            let _ = self.propagate_requirements_in_block(stmts);

            if self.inferred == prev_inferred
                && self.required == prev_required
                && self.local_types == prev_local_types
                && self.mem_types == prev_mem_types
                && self.local_requirements == prev_local_req
                && self.mem_requirements == prev_mem_req
                && self.var_address_keys == prev_addr_keys
            {
                break;
            }
        }

        self.collect_diagnostics_in_block(stmts);
        let summary = self.build_summary(stmts);
        let diagnostics = std::mem::take(&mut self.diagnostics);

        ProcTypeAnalysisResult {
            summary,
            diagnostics,
        }
    }

    /// Build the final procedure summary from inferred state.
    fn build_summary(&self, stmts: &[Stmt]) -> TypeSummary {
        let mut inputs = Vec::with_capacity(self.input_count);
        for index in (0..self.input_count).rev() {
            let key = Self::input_var_key(index);
            let req = self.required.get(&key).copied().unwrap_or(TypeFact::Felt);
            inputs.push(req.to_requirement());
        }

        let mut outputs = Vec::with_capacity(self.output_count);
        let return_values = Self::find_return_values(stmts);
        for index in (0..self.output_count).rev() {
            let ty = return_values
                .and_then(|values| values.get(index))
                .map(|var| self.inferred_type_for_var(var))
                .unwrap_or(TypeFact::Felt);
            outputs.push(ty.to_inferred_type());
        }

        TypeSummary::new(inputs, outputs)
    }

    /// Find the top-level return statement values.
    fn find_return_values(stmts: &[Stmt]) -> Option<&[Var]> {
        for stmt in stmts {
            if let Stmt::Return { values, .. } = stmt {
                return Some(values);
            }
        }
        None
    }

    /// Build the canonical key for an input variable by stack index.
    fn input_var_key(index: usize) -> VarKey {
        let var = Var::new(ValueId::new(index as u64), index);
        VarKey::from_var(&var)
    }

    /// Infer type guarantees in a statement block.
    fn infer_types_in_block(&mut self, stmts: &[Stmt]) -> bool {
        let mut changed = false;
        for stmt in stmts {
            changed |= self.infer_types_in_stmt(stmt);
        }
        changed
    }

    /// Infer type guarantees for one statement.
    fn infer_types_in_stmt(&mut self, stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Assign { dest, expr, .. } => {
                let changed = self.set_inferred_type_for_var(dest, self.infer_expr_type(expr));
                // Track abstract address keys for memory type tracking.
                match expr {
                    Expr::Constant(Constant::Felt(n)) if *n < MAX_MEMORY_ADDRESS => {
                        self.var_address_keys
                            .insert(VarKey::from_var(dest), MemAddressKey::Constant(*n as u32));
                    }
                    Expr::Var(src) => {
                        if let Some(key) =
                            self.var_address_keys.get(&VarKey::from_var(src)).copied()
                        {
                            self.var_address_keys.insert(VarKey::from_var(dest), key);
                        }
                    }
                    Expr::Binary(BinOp::Add, lhs, rhs) => {
                        // Propagate MemAddressKey through locaddr + constant offset.
                        // Try both operand orderings since addition is commutative.
                        // Sub is excluded: field sub computes (a - b) mod p, which
                        // wraps to addresses outside the procedure's local frame.
                        //
                        // Uses `or` (eager) instead of `or_else` (lazy) because
                        // a closure capturing `&self` conflicts with the outer
                        // `&mut self` borrow.
                        let key = self
                            .resolve_addr_offset_key(lhs, rhs)
                            .or(self.resolve_addr_offset_key(rhs, lhs));
                        if let Some(key) = key {
                            self.var_address_keys.insert(VarKey::from_var(dest), key);
                        }
                    }
                    _ => {}
                }
                changed
            }
            Stmt::MemLoad { load, .. } => {
                let stored_ty = load
                    .address
                    .first()
                    .and_then(|v| self.mem_address_key_for_var(v))
                    .and_then(|key| self.mem_types.get(&key).copied())
                    .unwrap_or(TypeFact::Felt);
                let mut changed = false;
                for output in &load.outputs {
                    changed |= self.set_inferred_type_for_var(output, stored_ty);
                }
                changed
            }
            Stmt::LocalLoad { load, .. } => {
                let stored_ty = self
                    .local_types
                    .get(&load.index)
                    .copied()
                    .unwrap_or(TypeFact::Felt);
                let mut changed = false;
                for output in &load.outputs {
                    changed |= self.set_inferred_type_for_var(output, stored_ty);
                }
                changed
            }
            Stmt::AdvLoad { load, .. } => {
                let mut changed = false;
                for output in &load.outputs {
                    changed |= self.set_inferred_type_for_var(output, TypeFact::Felt);
                }
                changed
            }
            Stmt::Call { call, .. } | Stmt::Exec { call, .. } | Stmt::SysCall { call, .. } => {
                self.assign_call_result_types(&call.target, &call.results)
            }
            Stmt::DynCall { results, .. } => {
                let mut changed = false;
                for result in results {
                    changed |= self.set_inferred_type_for_var(result, TypeFact::Felt);
                }
                changed
            }
            Stmt::Intrinsic { intrinsic, .. } => {
                let result_ty = self.intrinsic_result_type(&intrinsic.name);
                let mut changed = false;
                for result in &intrinsic.results {
                    changed |= self.set_inferred_type_for_var(result, result_ty);
                }
                if Self::intrinsic_asserts_u32_args(&intrinsic.name) {
                    for arg in &intrinsic.args {
                        changed |= self.set_inferred_type_for_var(arg, TypeFact::U32);
                    }
                }
                // Track locaddr results for memory address key mapping.
                if let Some(index_str) = intrinsic.name.strip_prefix("locaddr.")
                    && let Ok(index) = index_str.parse::<u16>()
                {
                    for result in &intrinsic.results {
                        self.var_address_keys
                            .insert(VarKey::from_var(result), MemAddressKey::LocalAddr(index));
                    }
                }
                changed
            }
            Stmt::If {
                then_body,
                else_body,
                phis,
                ..
            } => {
                let mut changed = false;
                changed |= self.infer_types_in_block(then_body);
                changed |= self.infer_types_in_block(else_body);
                for phi in phis {
                    let then_ty = self.inferred_type_for_var(&phi.then_var);
                    let else_ty = self.inferred_type_for_var(&phi.else_var);
                    changed |= self.set_inferred_type_for_var(&phi.dest, then_ty.join(else_ty));
                    self.propagate_phi_address_key(&phi.dest, &phi.then_var, &phi.else_var);
                }
                changed
            }
            Stmt::While { body, phis, .. } | Stmt::Repeat { body, phis, .. } => {
                let mut changed = false;
                changed |= self.infer_types_in_block(body);
                for phi in phis {
                    let init_ty = self.inferred_type_for_var(&phi.init);
                    let step_ty = self.inferred_type_for_var(&phi.step);
                    changed |= self.set_inferred_type_for_var(&phi.dest, init_ty.join(step_ty));
                    self.propagate_phi_address_key(&phi.dest, &phi.init, &phi.step);
                }
                changed
            }
            Stmt::LocalStore { store, .. } => {
                self.record_local_store_type(store.index, &store.values)
            }
            Stmt::LocalStoreW { store, .. } => {
                self.record_local_store_type(store.index, &store.values)
            }
            Stmt::MemStore { store, .. } => {
                let mut changed = false;
                if let Some(addr_key) = store
                    .address
                    .first()
                    .and_then(|v| self.mem_address_key_for_var(v))
                {
                    let stored_ty = store
                        .values
                        .iter()
                        .map(|v| self.inferred_type_for_var(v))
                        .reduce(TypeFact::glb)
                        .unwrap_or(TypeFact::Felt);
                    let current = self.mem_types.get(&addr_key).copied();
                    let updated = match current {
                        Some(existing) => existing.join(stored_ty),
                        None => stored_ty,
                    };
                    if current != Some(updated) {
                        self.mem_types.insert(addr_key, updated);
                        changed = true;
                    }
                }
                changed
            }
            Stmt::AdvStore { .. } | Stmt::Return { .. } => false,
        }
    }

    /// Assign types to call results from a known callee summary.
    fn assign_call_result_types(&mut self, target: &str, results: &[Var]) -> bool {
        let mut changed = false;
        let Some(summary) = self.summary_for_target(target).cloned() else {
            return false;
        };
        for (idx, result) in results.iter().enumerate() {
            let ty = if summary.is_opaque() {
                TypeFact::Felt
            } else {
                summary
                    .outputs
                    .get(idx)
                    .map(|t| TypeFact::from_inferred_type(*t))
                    .unwrap_or(TypeFact::Felt)
            };
            changed |= self.set_inferred_type_for_var(result, ty);
        }
        changed
    }

    /// Infer result type for an intrinsic operation.
    fn intrinsic_result_type(&self, name: &str) -> TypeFact {
        if name.starts_with("u32") || name == "sdepth" || name.starts_with("locaddr.") {
            TypeFact::U32
        } else if name == "is_odd" {
            TypeFact::Bool
        } else {
            TypeFact::Felt
        }
    }

    /// Return intrinsic base name without suffixes such as `.err=*` or immediates.
    fn intrinsic_base_name(name: &str) -> &str {
        name.split_once('.').map_or(name, |(base, _)| base)
    }

    /// Return true if intrinsic arguments require a caller-side u32 precondition.
    fn intrinsic_requires_u32_precondition(name: &str) -> bool {
        if !name.starts_with("u32") {
            return false;
        }

        !matches!(
            Self::intrinsic_base_name(name),
            "u32assert" | "u32assert2" | "u32assertw" | "u32split" | "u32cast"
        )
    }

    /// Return true if this intrinsic asserts that all arguments are valid u32 values.
    fn intrinsic_asserts_u32_args(name: &str) -> bool {
        matches!(
            Self::intrinsic_base_name(name),
            "u32assert" | "u32assert2" | "u32assertw"
        )
    }

    /// Infer type for an expression.
    fn infer_expr_type(&self, expr: &Expr) -> TypeFact {
        match expr {
            Expr::True | Expr::False => TypeFact::Bool,
            Expr::Var(var) => self.inferred_type_for_var(var),
            Expr::Constant(constant) => self.infer_constant_type(constant),
            Expr::Unary(op, inner) => self.infer_unary_expr_type(*op, inner),
            Expr::Binary(op, lhs, rhs) => self.infer_binary_expr_type(*op, lhs, rhs),
            Expr::EqW { .. } => TypeFact::Bool,
            Expr::Ternary {
                then_expr,
                else_expr,
                ..
            } => {
                let then_ty = self.infer_expr_type(then_expr);
                let else_ty = self.infer_expr_type(else_expr);
                then_ty.join(else_ty)
            }
        }
    }

    /// Infer type for a constant expression.
    ///
    /// `Felt(0)` and `Felt(1)` are inferred as `Bool` since they are the
    /// most precise type for these values. Constants in the u32 range are
    /// inferred as `U32`. The chain lattice ensures they widen correctly
    /// in arithmetic or felt contexts.
    fn infer_constant_type(&self, constant: &Constant) -> TypeFact {
        match constant {
            Constant::Felt(0 | 1) => TypeFact::Bool,
            Constant::Felt(n) if *n < MAX_MEMORY_ADDRESS => TypeFact::U32,
            Constant::Felt(_) | Constant::Defined(_) => TypeFact::Felt,
            Constant::Word(_) => TypeFact::Felt,
        }
    }

    /// Infer type for a unary expression.
    fn infer_unary_expr_type(&self, op: UnOp, _inner: &Expr) -> TypeFact {
        match op {
            UnOp::Not => TypeFact::Bool,
            UnOp::U32Test => TypeFact::Bool,
            UnOp::U32Cast
            | UnOp::U32Not
            | UnOp::U32Clz
            | UnOp::U32Ctz
            | UnOp::U32Clo
            | UnOp::U32Cto => TypeFact::U32,
            UnOp::Neg | UnOp::Inv | UnOp::Pow2 => TypeFact::Felt,
        }
    }

    /// Infer type for a binary expression.
    fn infer_binary_expr_type(&self, op: BinOp, _lhs: &Expr, _rhs: &Expr) -> TypeFact {
        match op {
            BinOp::Eq
            | BinOp::Neq
            | BinOp::Lt
            | BinOp::Lte
            | BinOp::Gt
            | BinOp::Gte
            | BinOp::And
            | BinOp::Or
            | BinOp::Xor
            | BinOp::U32Lt
            | BinOp::U32Lte
            | BinOp::U32Gt
            | BinOp::U32Gte => TypeFact::Bool,
            BinOp::U32And
            | BinOp::U32Or
            | BinOp::U32Xor
            | BinOp::U32Shl
            | BinOp::U32Shr
            | BinOp::U32Rotr
            | BinOp::U32WrappingAdd
            | BinOp::U32WrappingSub
            | BinOp::U32WrappingMul => TypeFact::U32,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::U32Exp => TypeFact::Felt,
        }
    }

    /// Read inferred type for a variable.
    fn inferred_type_for_var(&self, var: &Var) -> TypeFact {
        self.inferred
            .get(&VarKey::from_var(var))
            .copied()
            .unwrap_or(TypeFact::Felt)
    }

    /// Resolve the abstract memory address key for a variable, if known.
    fn mem_address_key_for_var(&self, var: &Var) -> Option<MemAddressKey> {
        self.var_address_keys.get(&VarKey::from_var(var)).copied()
    }

    /// Propagate a `MemAddressKey` through a phi node when both incoming
    /// values share the same key. If the keys disagree or either is absent,
    /// no key is assigned (conservative).
    fn propagate_phi_address_key(&mut self, dest: &Var, lhs: &Var, rhs: &Var) {
        let lhs_key = self.mem_address_key_for_var(lhs);
        let rhs_key = self.mem_address_key_for_var(rhs);
        if let (Some(lk), Some(rk)) = (lhs_key, rhs_key)
            && lk == rk
        {
            self.var_address_keys.insert(VarKey::from_var(dest), lk);
        }
    }

    /// Resolve a `MemAddressKey` for an address-plus-offset expression.
    ///
    /// Returns `Some(LocalAddrOffset(index, offset))` when `base_expr`
    /// resolves to a `LocalAddr` or `LocalAddrOffset` key and `offset_expr`
    /// is a constant in `[0, 2^32)`. Returns `None` if the accumulated
    /// offset overflows `u32` or the base is not a local address.
    fn resolve_addr_offset_key(
        &self,
        base_expr: &Expr,
        offset_expr: &Expr,
    ) -> Option<MemAddressKey> {
        let base_key = match base_expr {
            Expr::Var(v) => self.mem_address_key_for_var(v)?,
            _ => return None,
        };
        let offset: u32 = match offset_expr {
            Expr::Constant(Constant::Felt(n)) if *n < MAX_MEMORY_ADDRESS => *n as u32,
            Expr::Var(v) => match self.mem_address_key_for_var(v)? {
                MemAddressKey::Constant(n) => n,
                _ => return None,
            },
            _ => return None,
        };
        match base_key {
            MemAddressKey::LocalAddr(index) => Some(MemAddressKey::LocalAddrOffset(index, offset)),
            MemAddressKey::LocalAddrOffset(index, base_offset) => {
                let total = base_offset.checked_add(offset)?;
                Some(MemAddressKey::LocalAddrOffset(index, total))
            }
            MemAddressKey::Constant(_) => None,
        }
    }

    /// Record the inferred type for a local variable slot from stored values.
    ///
    /// Combines the types of all stored values via [`TypeFact::glb`] and
    /// joins with the existing slot type. Returns `true` if the type changed.
    fn record_local_store_type(&mut self, index: u16, values: &[Var]) -> bool {
        let stored_ty = values
            .iter()
            .map(|v| self.inferred_type_for_var(v))
            .reduce(TypeFact::glb)
            .unwrap_or(TypeFact::Felt);
        let current = self.local_types.get(&index).copied();
        let updated = match current {
            Some(existing) => existing.join(stored_ty),
            None => stored_ty,
        };
        if current != Some(updated) {
            self.local_types.insert(index, updated);
            true
        } else {
            false
        }
    }

    /// Propagate a local slot's accumulated requirement to stored values.
    ///
    /// Looks up the requirement for `index` in [`local_requirements`] and
    /// applies it to each stored value. Returns `true` if any requirement
    /// changed.
    fn propagate_local_store_requirement(&mut self, index: u16, values: &[Var]) -> bool {
        let req = self
            .local_requirements
            .get(&index)
            .copied()
            .unwrap_or(TypeFact::Felt);
        if req == TypeFact::Felt {
            return false;
        }
        let mut changed = false;
        for value in values {
            changed |= self.apply_requirement_to_var(value, req);
        }
        changed
    }

    /// Update inferred type for a variable.
    fn set_inferred_type_for_var(&mut self, var: &Var, new_type: TypeFact) -> bool {
        let key = VarKey::from_var(var);
        let current = self.inferred.get(&key).copied().unwrap_or(TypeFact::Felt);
        let updated = current.glb(new_type);
        if updated != current {
            self.inferred.insert(key, updated);
            true
        } else {
            false
        }
    }

    /// Seed type requirements from direct statement semantics.
    fn seed_requirements_in_block(&mut self, stmts: &[Stmt]) -> bool {
        let mut changed = false;
        for stmt in stmts {
            changed |= self.seed_requirements_in_stmt(stmt);
        }
        changed
    }

    /// Seed type requirements from one statement.
    fn seed_requirements_in_stmt(&mut self, stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Assign { expr, .. } => self.seed_requirements_in_expr(expr),
            Stmt::MemLoad { load, .. } => {
                let mut changed = false;
                for address in &load.address {
                    if self.mem_address_key_for_var(address).is_some() {
                        continue;
                    }
                    changed |= self.apply_requirement_to_var(address, TypeFact::U32);
                }
                changed
            }
            Stmt::MemStore { store, .. } => {
                let mut changed = false;
                for address in &store.address {
                    if self.mem_address_key_for_var(address).is_some() {
                        continue;
                    }
                    changed |= self.apply_requirement_to_var(address, TypeFact::U32);
                }
                changed
            }
            Stmt::Call { call, .. } | Stmt::Exec { call, .. } | Stmt::SysCall { call, .. } => {
                self.seed_call_arg_requirements(&call.target, &call.args)
            }
            Stmt::Intrinsic { intrinsic, .. } => self.seed_intrinsic_arg_requirements(intrinsic),
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
            } => {
                let mut changed = self.require_bool_expr(cond);
                changed |= self.seed_requirements_in_block(then_body);
                changed |= self.seed_requirements_in_block(else_body);
                changed
            }
            Stmt::While { cond, body, .. } => {
                let mut changed = self.require_bool_expr(cond);
                changed |= self.seed_requirements_in_block(body);
                changed
            }
            Stmt::Repeat { body, .. } => self.seed_requirements_in_block(body),
            Stmt::AdvLoad { .. }
            | Stmt::AdvStore { .. }
            | Stmt::LocalLoad { .. }
            | Stmt::LocalStore { .. }
            | Stmt::LocalStoreW { .. }
            | Stmt::DynCall { .. }
            | Stmt::Return { .. } => false,
        }
    }

    /// Seed requirements from a call argument list.
    fn seed_call_arg_requirements(&mut self, target: &str, args: &[Var]) -> bool {
        let Some(summary) = self.summary_for_target(target).cloned() else {
            return false;
        };
        if summary.is_opaque() {
            return false;
        }
        let mut changed = false;
        for (arg, expected) in args.iter().zip(summary.inputs.iter().copied()) {
            changed |= self.apply_requirement_to_var(arg, TypeFact::from_requirement(expected));
        }
        changed
    }

    /// Seed requirements for intrinsic arguments.
    fn seed_intrinsic_arg_requirements(&mut self, intrinsic: &crate::ir::Intrinsic) -> bool {
        if !Self::intrinsic_requires_u32_precondition(&intrinsic.name) {
            return false;
        }

        let mut changed = false;
        for arg in &intrinsic.args {
            changed |= self.require_u32_var_if_not_guaranteed(arg);
        }
        changed
    }

    /// Seed requirements from expression semantics.
    fn seed_requirements_in_expr(&mut self, expr: &Expr) -> bool {
        match expr {
            Expr::True | Expr::False | Expr::Var(_) | Expr::Constant(_) => false,
            Expr::Unary(op, inner) => {
                let mut changed = self.seed_requirements_in_expr(inner);
                match op {
                    UnOp::Not => changed |= self.require_bool_expr(inner),
                    UnOp::U32Cast | UnOp::U32Test => {}
                    UnOp::U32Not | UnOp::U32Clz | UnOp::U32Ctz | UnOp::U32Clo | UnOp::U32Cto => {
                        changed |= self.require_u32_expr_if_not_guaranteed(inner);
                    }
                    UnOp::Neg | UnOp::Inv | UnOp::Pow2 => {
                        changed |= self.require_felt_expr(inner);
                    }
                }
                changed
            }
            Expr::Binary(op, lhs, rhs) => {
                let mut changed = self.seed_requirements_in_expr(lhs);
                changed |= self.seed_requirements_in_expr(rhs);
                match op {
                    BinOp::U32And
                    | BinOp::U32Or
                    | BinOp::U32Xor
                    | BinOp::U32Shl
                    | BinOp::U32Shr
                    | BinOp::U32Rotr
                    | BinOp::U32Lt
                    | BinOp::U32Lte
                    | BinOp::U32Gt
                    | BinOp::U32Gte
                    | BinOp::U32WrappingAdd
                    | BinOp::U32WrappingSub
                    | BinOp::U32WrappingMul => {
                        changed |= self.require_u32_expr_if_not_guaranteed(lhs);
                        changed |= self.require_u32_expr_if_not_guaranteed(rhs);
                    }
                    BinOp::U32Exp => {
                        changed |= self.require_felt_expr(lhs);
                        changed |= self.require_u32_expr_if_not_guaranteed(rhs);
                    }
                    BinOp::And | BinOp::Or | BinOp::Xor => {
                        changed |= self.require_bool_expr(lhs);
                        changed |= self.require_bool_expr(rhs);
                    }
                    BinOp::Add
                    | BinOp::Sub
                    | BinOp::Mul
                    | BinOp::Div
                    | BinOp::Eq
                    | BinOp::Neq
                    | BinOp::Lt
                    | BinOp::Lte
                    | BinOp::Gt
                    | BinOp::Gte => {
                        changed |= self.require_felt_expr(lhs);
                        changed |= self.require_felt_expr(rhs);
                    }
                }
                changed
            }
            Expr::EqW { lhs, rhs } => {
                let mut changed = false;
                for var in lhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeFact::Felt);
                }
                for var in rhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeFact::Felt);
                }
                changed
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                let mut changed = self.require_bool_expr(cond);
                changed |= self.seed_requirements_in_expr(then_expr);
                changed |= self.seed_requirements_in_expr(else_expr);
                changed
            }
        }
    }

    /// Propagate requirements through copy-like dataflow.
    fn propagate_requirements_in_block(&mut self, stmts: &[Stmt]) -> bool {
        let mut changed = false;
        for stmt in stmts {
            changed |= self.propagate_requirements_in_stmt(stmt);
        }
        changed
    }

    /// Propagate requirements through one statement.
    fn propagate_requirements_in_stmt(&mut self, stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Assign { dest, expr, .. } => {
                let req = self.requirement_for_var(dest);
                if req == TypeFact::Felt {
                    return false;
                }
                self.apply_requirement_to_expr(expr, req)
            }
            Stmt::If {
                then_body,
                else_body,
                phis,
                ..
            } => {
                let mut changed = false;
                changed |= self.propagate_requirements_in_block(then_body);
                changed |= self.propagate_requirements_in_block(else_body);
                for phi in phis {
                    let req = self.requirement_for_var(&phi.dest);
                    if req == TypeFact::Felt {
                        continue;
                    }
                    changed |= self.apply_requirement_to_var(&phi.then_var, req);
                    changed |= self.apply_requirement_to_var(&phi.else_var, req);
                }
                changed
            }
            Stmt::While { body, phis, .. } | Stmt::Repeat { body, phis, .. } => {
                let mut changed = false;
                changed |= self.propagate_requirements_in_block(body);
                for phi in phis {
                    let req = self.requirement_for_var(&phi.dest);
                    if req == TypeFact::Felt {
                        continue;
                    }
                    changed |= self.apply_requirement_to_var(&phi.init, req);
                    changed |= self.apply_requirement_to_var(&phi.step, req);
                }
                changed
            }
            Stmt::LocalLoad { load, .. } => {
                let mut changed = false;
                for output in &load.outputs {
                    let req = self.requirement_for_var(output);
                    if req == TypeFact::Felt {
                        continue;
                    }
                    let current = self
                        .local_requirements
                        .get(&load.index)
                        .copied()
                        .unwrap_or(TypeFact::Felt);
                    let updated = current.glb(req);
                    if updated != current {
                        self.local_requirements.insert(load.index, updated);
                        changed = true;
                    }
                }
                changed
            }
            Stmt::LocalStore { store, .. } => {
                self.propagate_local_store_requirement(store.index, &store.values)
            }
            Stmt::LocalStoreW { store, .. } => {
                self.propagate_local_store_requirement(store.index, &store.values)
            }
            Stmt::MemLoad { load, .. } => {
                let mut changed = false;
                if let Some(addr_key) = load
                    .address
                    .first()
                    .and_then(|v| self.mem_address_key_for_var(v))
                {
                    for output in &load.outputs {
                        let req = self.requirement_for_var(output);
                        if req == TypeFact::Felt {
                            continue;
                        }
                        let current = self
                            .mem_requirements
                            .get(&addr_key)
                            .copied()
                            .unwrap_or(TypeFact::Felt);
                        let updated = current.glb(req);
                        if updated != current {
                            self.mem_requirements.insert(addr_key, updated);
                            changed = true;
                        }
                    }
                }
                changed
            }
            Stmt::MemStore { store, .. } => {
                let mut changed = false;
                if let Some(addr_key) = store
                    .address
                    .first()
                    .and_then(|v| self.mem_address_key_for_var(v))
                {
                    let req = self
                        .mem_requirements
                        .get(&addr_key)
                        .copied()
                        .unwrap_or(TypeFact::Felt);
                    if req != TypeFact::Felt {
                        for value in &store.values {
                            changed |= self.apply_requirement_to_var(value, req);
                        }
                    }
                }
                changed
            }
            Stmt::AdvLoad { .. }
            | Stmt::AdvStore { .. }
            | Stmt::Call { .. }
            | Stmt::Exec { .. }
            | Stmt::SysCall { .. }
            | Stmt::DynCall { .. }
            | Stmt::Intrinsic { .. }
            | Stmt::Return { .. } => false,
        }
    }

    /// Apply a requirement to an expression from a required destination.
    fn apply_requirement_to_expr(&mut self, expr: &Expr, req: TypeFact) -> bool {
        match expr {
            Expr::Var(var) => self.apply_requirement_to_var(var, req),
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                let mut changed = self.require_bool_expr(cond);
                changed |= self.apply_requirement_to_expr(then_expr, req);
                changed |= self.apply_requirement_to_expr(else_expr, req);
                changed
            }
            Expr::EqW { .. } => false,
            Expr::True | Expr::False | Expr::Constant(_) | Expr::Binary(..) | Expr::Unary(..) => {
                false
            }
        }
    }

    /// Read the current requirement for a variable.
    fn requirement_for_var(&self, var: &Var) -> TypeFact {
        self.required
            .get(&VarKey::from_var(var))
            .copied()
            .unwrap_or(TypeFact::Felt)
    }

    /// Apply a requirement to a variable.
    fn apply_requirement_to_var(&mut self, var: &Var, req: TypeFact) -> bool {
        if req == TypeFact::Felt {
            return false;
        }
        let key = VarKey::from_var(var);
        let current = self.required.get(&key).copied().unwrap_or(TypeFact::Felt);
        let updated = current.glb(req);
        if updated != current {
            self.required.insert(key, updated);
            true
        } else {
            false
        }
    }

    /// Require a variable to be u32 only if it is not already guaranteed u32.
    fn require_u32_var_if_not_guaranteed(&mut self, var: &Var) -> bool {
        let actual = self.inferred_type_for_var(var);
        if actual.satisfies(TypeFact::U32) {
            false
        } else {
            self.apply_requirement_to_var(var, TypeFact::U32)
        }
    }

    /// Require that an expression is boolean.
    fn require_bool_expr(&mut self, expr: &Expr) -> bool {
        match expr {
            Expr::Var(var) => self.apply_requirement_to_var(var, TypeFact::Bool),
            Expr::Unary(UnOp::Not, inner) => self.require_bool_expr(inner),
            Expr::Binary(BinOp::And | BinOp::Or, lhs, rhs) => {
                self.require_bool_expr(lhs) | self.require_bool_expr(rhs)
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.require_bool_expr(cond)
                    | self.require_bool_expr(then_expr)
                    | self.require_bool_expr(else_expr)
            }
            Expr::EqW { lhs, rhs } => {
                let mut changed = false;
                for var in lhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeFact::Felt);
                }
                for var in rhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeFact::Felt);
                }
                changed
            }
            Expr::True | Expr::False | Expr::Constant(_) | Expr::Binary(..) | Expr::Unary(..) => {
                false
            }
        }
    }

    /// Require that an expression is U32.
    fn require_u32_expr(&mut self, expr: &Expr) -> bool {
        match expr {
            Expr::Var(var) => self.apply_requirement_to_var(var, TypeFact::U32),
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.require_bool_expr(cond)
                    | self.require_u32_expr(then_expr)
                    | self.require_u32_expr(else_expr)
            }
            Expr::EqW { .. } => false,
            Expr::True | Expr::False | Expr::Constant(_) | Expr::Binary(..) | Expr::Unary(..) => {
                false
            }
        }
    }

    /// Require an expression to be u32 only if it is not already guaranteed u32.
    fn require_u32_expr_if_not_guaranteed(&mut self, expr: &Expr) -> bool {
        let actual = self.infer_expr_type(expr);
        if actual.satisfies(TypeFact::U32) {
            false
        } else {
            self.require_u32_expr(expr)
        }
    }

    /// Require that an expression is Felt-compatible.
    fn require_felt_expr(&mut self, expr: &Expr) -> bool {
        match expr {
            Expr::Var(var) => self.apply_requirement_to_var(var, TypeFact::Felt),
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.require_bool_expr(cond)
                    | self.require_felt_expr(then_expr)
                    | self.require_felt_expr(else_expr)
            }
            Expr::EqW { lhs, rhs } => {
                let mut changed = false;
                for var in lhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeFact::Felt);
                }
                for var in rhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeFact::Felt);
                }
                changed
            }
            Expr::True | Expr::False | Expr::Constant(_) | Expr::Binary(..) | Expr::Unary(..) => {
                false
            }
        }
    }

    /// Collect all mismatch diagnostics in a statement block.
    fn collect_diagnostics_in_block(&mut self, stmts: &[Stmt]) {
        for stmt in stmts {
            self.collect_diagnostics_in_stmt(stmt);
        }
    }

    /// Collect mismatch diagnostics for one statement.
    fn collect_diagnostics_in_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Assign { span, expr, .. } => {
                self.collect_expr_diagnostics(expr, *span);
            }
            Stmt::MemLoad { span, load } => {
                for address in &load.address {
                    // Skip the address check if the variable is a known abstract
                    // address (constant immediate or locaddr result) — these are
                    // always valid memory addresses regardless of their inferred
                    // scalar type.
                    if self.mem_address_key_for_var(address).is_some() {
                        continue;
                    }
                    self.check_var_requirement(
                        address,
                        TypeFact::U32,
                        *span,
                        "memory load address is not guaranteed U32",
                    );
                }
            }
            Stmt::MemStore { span, store } => {
                for address in &store.address {
                    // Skip the address check if the variable is a known abstract
                    // address (constant immediate or locaddr result).
                    if self.mem_address_key_for_var(address).is_some() {
                        continue;
                    }
                    self.check_var_requirement(
                        address,
                        TypeFact::U32,
                        *span,
                        "memory store address is not guaranteed U32",
                    );
                }
            }
            Stmt::Call { span, call }
            | Stmt::Exec { span, call }
            | Stmt::SysCall { span, call } => {
                self.collect_call_arg_diagnostics(*span, &call.target, &call.args);
            }
            Stmt::Intrinsic { span, intrinsic } => {
                if Self::intrinsic_requires_u32_precondition(&intrinsic.name) {
                    for arg in &intrinsic.args {
                        self.check_var_requirement(
                            arg,
                            TypeFact::U32,
                            *span,
                            "u32 instruction argument is not guaranteed U32",
                        );
                    }
                }
            }
            Stmt::If {
                span,
                cond,
                then_body,
                else_body,
                ..
            } => {
                self.check_expr_requirement(
                    cond,
                    TypeFact::Bool,
                    *span,
                    "if-condition is not guaranteed Bool",
                );
                self.collect_diagnostics_in_block(then_body);
                self.collect_diagnostics_in_block(else_body);
            }
            Stmt::While {
                span, cond, body, ..
            } => {
                self.check_expr_requirement(
                    cond,
                    TypeFact::Bool,
                    *span,
                    "while-condition is not guaranteed Bool",
                );
                self.collect_diagnostics_in_block(body);
            }
            Stmt::Repeat { body, .. } => {
                self.collect_diagnostics_in_block(body);
            }
            Stmt::AdvLoad { .. }
            | Stmt::AdvStore { .. }
            | Stmt::LocalLoad { .. }
            | Stmt::LocalStore { .. }
            | Stmt::LocalStoreW { .. }
            | Stmt::DynCall { .. }
            | Stmt::Return { .. } => {}
        }
    }

    /// Collect diagnostics for call arguments.
    ///
    /// In the current four-point chain lattice, no scalar type pair is
    /// definitively incompatible. Call-argument mismatch diagnostics are
    /// therefore disabled. Stronger diagnostics require richer facts
    /// (exact constants, numeric ranges, or provenance tracking).
    fn collect_call_arg_diagnostics(&mut self, _span: SourceSpan, _target: &str, _args: &[Var]) {}

    /// Collect diagnostics for ternary conditions nested in expressions.
    fn collect_expr_diagnostics(&mut self, expr: &Expr, span: SourceSpan) {
        match expr {
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.check_expr_requirement(
                    cond,
                    TypeFact::Bool,
                    span,
                    "ternary condition is not guaranteed Bool",
                );
                self.collect_expr_diagnostics(then_expr, span);
                self.collect_expr_diagnostics(else_expr, span);
            }
            Expr::Binary(_, lhs, rhs) => {
                self.collect_expr_diagnostics(lhs, span);
                self.collect_expr_diagnostics(rhs, span);
            }
            Expr::EqW { .. } => {}
            Expr::Unary(_, inner) => self.collect_expr_diagnostics(inner, span),
            Expr::True | Expr::False | Expr::Var(_) | Expr::Constant(_) => {}
        }
    }

    /// Check whether an expression satisfies a requirement.
    fn check_expr_requirement(
        &mut self,
        expr: &Expr,
        expected: TypeFact,
        span: SourceSpan,
        context: &str,
    ) {
        let actual = self.infer_expr_type(expr);
        if !actual.satisfies(expected) {
            self.diagnostics.push(TypeDiagnostic::new(
                self.proc_path.clone(),
                span,
                format!("{context} (inferred {})", actual.to_inferred_type()),
            ));
        }
    }

    /// Check whether a variable satisfies a requirement.
    fn check_var_requirement(
        &mut self,
        var: &Var,
        expected: TypeFact,
        span: SourceSpan,
        context: &str,
    ) {
        let actual = self.inferred_type_for_var(var);
        if !actual.satisfies(expected) {
            self.diagnostics.push(TypeDiagnostic::new(
                self.proc_path.clone(),
                span,
                format!("{context} (inferred {})", actual.to_inferred_type()),
            ));
        }
    }

    /// Look up a callee summary by target string.
    fn summary_for_target(&self, target: &str) -> Option<&TypeSummary> {
        let key = SymbolPath::new(target.to_string());
        self.callee_summaries.get(&key)
    }
}
