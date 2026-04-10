//! Intraprocedural type inference and mismatch checking.

use std::{collections::HashMap, hash::Hash};

use miden_assembly_syntax::ast::Visibility;
use miden_assembly_syntax::debuginfo::SourceSpan;

use crate::ir::{BinOp, Call, Constant, Expr, Stmt, UnOp, ValueId, Var};
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

/// Requirement fact paired with provenance metadata.
type RequirementEntry = (TypeFact, RequirementOrigin);

/// Origin of a non-`Felt` type requirement.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct RequirementOrigin {
    /// Span of the use site that imposed the requirement.
    span: SourceSpan,
    /// Kind of use that imposed the requirement.
    kind: RequirementOriginKind,
}

impl RequirementOrigin {
    /// Construct an origin for a boolean-only use site.
    fn bool_use(span: SourceSpan) -> Self {
        Self {
            span,
            kind: RequirementOriginKind::BoolUse,
        }
    }

    /// Construct an origin for a U32-only operation.
    fn u32_operation(span: SourceSpan) -> Self {
        Self {
            span,
            kind: RequirementOriginKind::U32Operation,
        }
    }

    /// Construct an origin for a memory-address use.
    fn memory_address(span: SourceSpan) -> Self {
        Self {
            span,
            kind: RequirementOriginKind::MemoryAddress,
        }
    }

    /// Construct an origin for a call argument requirement.
    fn call_argument(span: SourceSpan, target: &str) -> Self {
        Self {
            span,
            kind: RequirementOriginKind::CallArgument {
                target: SymbolPath::new(target).name().to_string(),
            },
        }
    }

    /// Construct an origin for an intrinsic argument requirement.
    fn intrinsic_argument(span: SourceSpan, name: &str, role: Option<&'static str>) -> Self {
        let display_name = name.split_once('.').map_or(name, |(base, _)| base);
        Self {
            span,
            kind: RequirementOriginKind::IntrinsicArgument {
                name: display_name.to_string(),
                role,
            },
        }
    }

    /// Render a user-facing description of the requirement site.
    fn description(&self, req: TypeFact) -> String {
        match &self.kind {
            RequirementOriginKind::U32Operation => {
                format!("this U32 operation requires {}", req.to_requirement())
            }
            RequirementOriginKind::BoolUse => {
                format!("this use requires {}", req.to_requirement())
            }
            RequirementOriginKind::MemoryAddress => "this memory address must be U32".to_string(),
            RequirementOriginKind::CallArgument { target } => {
                format!(
                    "call to {} expects a {} value here",
                    target,
                    req.to_requirement()
                )
            }
            RequirementOriginKind::IntrinsicArgument { name, role } => {
                if let Some(role) = role {
                    format!(
                        "{} requires its {} to be {}",
                        name,
                        role,
                        req.to_requirement()
                    )
                } else {
                    format!("{} expects a {} value here", name, req.to_requirement())
                }
            }
        }
    }
}

/// Category of use that imposed a requirement.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum RequirementOriginKind {
    /// Requirement imposed by a U32-only operation.
    U32Operation,
    /// Requirement imposed by a boolean-only use.
    BoolUse,
    /// Requirement imposed by using a value as a memory address.
    MemoryAddress,
    /// Requirement imported from a callee signature.
    CallArgument {
        /// Display name of the callee.
        target: String,
    },
    /// Requirement imposed by an intrinsic argument.
    IntrinsicArgument {
        /// Display name of the intrinsic.
        name: String,
        /// Optional semantic role of the argument.
        role: Option<&'static str>,
    },
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
    visibility: Visibility,
    proc_span: SourceSpan,
    stmts: &[Stmt],
    callee_summaries: &TypeSummaryMap,
) -> ProcTypeAnalysisResult {
    let mut analyzer = ProcTypeAnalyzer::new(
        proc_path.clone(),
        input_count,
        output_count,
        visibility,
        proc_span,
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
    /// Visibility of the procedure (public or private).
    visibility: Visibility,
    /// Source span of the procedure definition.
    proc_span: SourceSpan,
    /// Previously inferred summaries for callees.
    callee_summaries: &'a TypeSummaryMap,
    /// Inferred type guarantees for variables.
    inferred: HashMap<VarKey, TypeFact>,
    /// Inferred requirements for variables.
    required: HashMap<VarKey, RequirementEntry>,
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
    local_requirements: HashMap<u16, RequirementEntry>,
    /// Requirements propagated backward to memory locations.
    mem_requirements: HashMap<MemAddressKey, RequirementEntry>,
}

impl<'a> ProcTypeAnalyzer<'a> {
    /// Construct a new analyzer.
    fn new(
        proc_path: SymbolPath,
        input_count: usize,
        output_count: usize,
        visibility: Visibility,
        proc_span: SourceSpan,
        callee_summaries: &'a TypeSummaryMap,
    ) -> Self {
        Self {
            proc_path,
            input_count,
            output_count,
            visibility,
            proc_span,
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
        self.collect_input_diagnostics();
        let passthrough_map = crate::passthrough::compute_passthrough_map(
            stmts,
            self.input_count,
            self.output_count,
            Some(self.callee_summaries),
        );
        let summary = self.build_summary(stmts, passthrough_map);
        let diagnostics = std::mem::take(&mut self.diagnostics);

        ProcTypeAnalysisResult {
            summary,
            diagnostics,
        }
    }

    /// Build the final procedure summary from inferred state.
    ///
    /// `output_input_map` is a pre-computed passthrough map where
    /// `output_input_map[i] == Some(j)` means output `i` is an unmodified
    /// copy of input `j`.
    fn build_summary(&self, stmts: &[Stmt], output_input_map: Vec<Option<usize>>) -> TypeSummary {
        let mut inputs = Vec::with_capacity(self.input_count);
        for index in (0..self.input_count).rev() {
            let key = Self::input_var_key(index);
            let req = self
                .required
                .get(&key)
                .map(|(fact, _)| *fact)
                .unwrap_or(TypeFact::Felt);
            inputs.push(req.to_requirement());
        }

        let mut outputs = Vec::with_capacity(self.output_count);
        let return_values = Self::find_return_values(stmts);
        for (map_idx, origin_input) in output_input_map.iter().enumerate() {
            // The passthrough map is built in the same order as the output
            // positions (reversed stack depth), so map_idx corresponds to
            // the reverse-depth index used by find_return_values.
            let index = self.output_count.saturating_sub(1 + map_idx);
            let ty = return_values
                .and_then(|values| values.get(index))
                .map(|var| {
                    let inferred = self.inferred_type_for_var(var);
                    if let Some(input_idx) = origin_input {
                        let input_key = Self::input_var_key(*input_idx);
                        let input_req = self
                            .required
                            .get(&input_key)
                            .map(|(fact, _)| *fact)
                            .unwrap_or(TypeFact::Felt);
                        inferred.glb(input_req)
                    } else {
                        inferred
                    }
                })
                .unwrap_or(TypeFact::Felt);
            outputs.push(ty.to_inferred_type());
        }

        TypeSummary::new_with_map(inputs, outputs, output_input_map)
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
                self.assign_call_result_types(&call.target, &call.args, &call.results)
            }
            Stmt::DynCall { results, .. } => {
                let mut changed = false;
                for result in results {
                    changed |= self.set_inferred_type_for_var(result, TypeFact::Felt);
                }
                changed
            }
            Stmt::Intrinsic { intrinsic, .. } => {
                let output_count = intrinsic.results.len();
                let mut changed = false;
                for (idx, result) in intrinsic.results.iter().enumerate() {
                    let result_ty = Self::intrinsic_output_type(&intrinsic.name, idx, output_count);
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
    ///
    /// For outputs that trace back to a callee input (`output_input_map`),
    /// the result type is resolved from the caller's argument type rather
    /// than the callee's fixed output type. This eliminates false positives
    /// for passthrough procedures that only permute their inputs.
    fn assign_call_result_types(&mut self, target: &str, args: &[Var], results: &[Var]) -> bool {
        let mut changed = false;
        let Some(summary) = self.summary_for_target(target).cloned() else {
            return false;
        };
        for (idx, result) in results.iter().enumerate() {
            let ty = if summary.is_opaque() {
                TypeFact::Felt
            } else if let Some(Some(input_idx)) = summary.output_input_map.get(idx) {
                // Passthrough output: resolve type from the caller's argument.
                // Origin::Input uses 0=deepest, but args uses 0=topmost (inverted).
                args.len()
                    .checked_sub(1 + *input_idx)
                    .and_then(|i| args.get(i))
                    .map(|arg| self.inferred_type_for_var(arg))
                    .unwrap_or(TypeFact::Felt)
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

    /// Infer result type for an intrinsic output at a given position.
    ///
    /// Position 0 is the first pushed result (deepest on stack for multi-output
    /// intrinsics). The last position is the topmost result on the stack.
    fn intrinsic_output_type(name: &str, output_index: usize, output_count: usize) -> TypeFact {
        let base = Self::intrinsic_base_name(name);
        match base {
            // Multi-output intrinsics with Bool carry/borrow flag as last output.
            "u32overflowing_add"
            | "u32overflowing_sub"
            | "u32overflowing_add3"
            | "u32widening_add" => {
                if output_index == output_count - 1 {
                    TypeFact::Bool
                } else {
                    TypeFact::U32
                }
            }
            // Multi-output intrinsics where all outputs are U32.
            "u32widening_add3" | "u32widening_mul" | "u32widening_madd" | "u32divmod"
            | "u32split" | "u32mod" | "u32wrapping_add3" => TypeFact::U32,
            // Other u32 intrinsics and sdepth: all outputs U32.
            _ if base.starts_with("u32") || name == "sdepth" => TypeFact::U32,
            // locaddr: U32. Note: uses `name` (not `base`) because
            // `intrinsic_base_name` strips at the first dot, turning
            // `locaddr.0` into `locaddr`. The match on `base` above
            // intentionally falls through to these wildcard arms for dotted
            // intrinsics.
            _ if name.starts_with("locaddr.") => TypeFact::U32,
            // is_odd: Bool.
            "is_odd" => TypeFact::Bool,
            // All other intrinsics (crypto, extension field, mem_stream,
            // adv_pipe, etc.): Felt.
            _ => TypeFact::Felt,
        }
    }

    /// Return intrinsic base name without suffixes such as `.err=*` or immediates.
    fn intrinsic_base_name(name: &str) -> &str {
        name.split_once('.').map_or(name, |(base, _)| base)
    }

    /// Return true if the intrinsic is an advice-sourced operation.
    ///
    /// Advice intrinsics (`adv_push`, `adv_pipe`) have a separate analysis
    /// pass and should not generate type-widening diagnostics.
    fn is_advice_intrinsic(name: &str) -> bool {
        let base = Self::intrinsic_base_name(name);
        matches!(base, "adv_push" | "adv_pipe")
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
        let Some((req, origin)) = self.local_requirements.get(&index).cloned() else {
            return false;
        };
        if req == TypeFact::Felt {
            return false;
        }
        let mut changed = false;
        for value in values {
            changed |= self.apply_requirement_to_var(value, req, origin.clone());
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
            Stmt::Assign { span, expr, .. } => self.seed_requirements_in_expr(expr, *span),
            Stmt::MemLoad { span, load } => {
                let mut changed = false;
                for address in &load.address {
                    if self.mem_address_key_for_var(address).is_some() {
                        continue;
                    }
                    changed |= self.apply_requirement_to_var(
                        address,
                        TypeFact::U32,
                        RequirementOrigin::memory_address(*span),
                    );
                }
                changed
            }
            Stmt::MemStore { span, store } => {
                let mut changed = false;
                for address in &store.address {
                    if self.mem_address_key_for_var(address).is_some() {
                        continue;
                    }
                    changed |= self.apply_requirement_to_var(
                        address,
                        TypeFact::U32,
                        RequirementOrigin::memory_address(*span),
                    );
                }
                changed
            }
            Stmt::Call { span, call }
            | Stmt::Exec { span, call }
            | Stmt::SysCall { span, call } => {
                self.seed_call_arg_requirements(&call.target, &call.args, *span)
            }
            Stmt::Intrinsic { span, intrinsic } => {
                self.seed_intrinsic_arg_requirements(intrinsic, *span)
            }
            Stmt::If {
                span,
                cond,
                then_body,
                else_body,
                ..
            } => {
                let mut changed = self.require_bool_expr(cond, RequirementOrigin::bool_use(*span));
                changed |= self.seed_requirements_in_block(then_body);
                changed |= self.seed_requirements_in_block(else_body);
                changed
            }
            Stmt::While {
                span, cond, body, ..
            } => {
                let mut changed = self.require_bool_expr(cond, RequirementOrigin::bool_use(*span));
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
    fn seed_call_arg_requirements(&mut self, target: &str, args: &[Var], span: SourceSpan) -> bool {
        let Some(summary) = self.summary_for_target(target).cloned() else {
            return false;
        };
        if summary.is_opaque() {
            return false;
        }
        let mut changed = false;
        let origin = RequirementOrigin::call_argument(span, target);
        for (arg, expected) in args.iter().zip(summary.inputs.iter().copied()) {
            changed |= self.apply_requirement_to_var(
                arg,
                TypeFact::from_requirement(expected),
                origin.clone(),
            );
        }
        changed
    }

    /// Seed requirements for intrinsic arguments.
    fn seed_intrinsic_arg_requirements(
        &mut self,
        intrinsic: &crate::ir::Intrinsic,
        span: SourceSpan,
    ) -> bool {
        let mut changed = false;

        // Blanket u32 precondition for u32 arithmetic intrinsics.
        if Self::intrinsic_requires_u32_precondition(&intrinsic.name) {
            let origin = RequirementOrigin::intrinsic_argument(span, &intrinsic.name, None);
            for arg in &intrinsic.args {
                changed |= self.require_u32_var_if_not_guaranteed(arg, origin.clone());
            }
        }

        // Per-intrinsic positional requirements.
        let base = Self::intrinsic_base_name(&intrinsic.name);
        match base {
            // mtree_get: [d, i, R, ...] — depth (arg 0) and index (arg 1) are U32.
            "mtree_get" => {
                for (role, arg) in ["depth", "index"]
                    .into_iter()
                    .zip(intrinsic.args.iter().take(2))
                {
                    changed |= self.require_u32_var_if_not_guaranteed(
                        arg,
                        RequirementOrigin::intrinsic_argument(span, &intrinsic.name, Some(role)),
                    );
                }
            }
            // mtree_set: [d, i, R, V', ...] — depth (arg 0) and index (arg 1) are U32.
            "mtree_set" => {
                for (role, arg) in ["depth", "index"]
                    .into_iter()
                    .zip(intrinsic.args.iter().take(2))
                {
                    changed |= self.require_u32_var_if_not_guaranteed(
                        arg,
                        RequirementOrigin::intrinsic_argument(span, &intrinsic.name, Some(role)),
                    );
                }
            }
            // mtree_verify: [V, d, i, R, ...] — depth (arg 4) and index (arg 5) are U32.
            "mtree_verify" => {
                for (role, arg) in ["depth", "index"]
                    .into_iter()
                    .zip(intrinsic.args.iter().skip(4).take(2))
                {
                    changed |= self.require_u32_var_if_not_guaranteed(
                        arg,
                        RequirementOrigin::intrinsic_argument(span, &intrinsic.name, Some(role)),
                    );
                }
            }
            // mem_stream / adv_pipe: address is the last argument.
            "mem_stream" | "adv_pipe" => {
                if let Some(addr) = intrinsic.args.last() {
                    changed |= self.require_u32_var_if_not_guaranteed(
                        addr,
                        RequirementOrigin::intrinsic_argument(
                            span,
                            &intrinsic.name,
                            Some("address"),
                        ),
                    );
                }
            }
            _ => {}
        }

        changed
    }

    /// Seed requirements from expression semantics.
    fn seed_requirements_in_expr(&mut self, expr: &Expr, span: SourceSpan) -> bool {
        match expr {
            Expr::True | Expr::False | Expr::Var(_) | Expr::Constant(_) => false,
            Expr::Unary(op, inner) => {
                let mut changed = self.seed_requirements_in_expr(inner, span);
                match op {
                    UnOp::Not => {
                        changed |= self.require_bool_expr(inner, RequirementOrigin::bool_use(span));
                    }
                    UnOp::U32Cast | UnOp::U32Test => {}
                    UnOp::U32Not | UnOp::U32Clz | UnOp::U32Ctz | UnOp::U32Clo | UnOp::U32Cto => {
                        changed |= self.require_u32_expr_if_not_guaranteed(
                            inner,
                            RequirementOrigin::u32_operation(span),
                        );
                    }
                    UnOp::Neg | UnOp::Inv | UnOp::Pow2 => {
                        changed |= self.require_felt_expr(inner, span);
                    }
                }
                changed
            }
            Expr::Binary(op, lhs, rhs) => {
                let mut changed = self.seed_requirements_in_expr(lhs, span);
                changed |= self.seed_requirements_in_expr(rhs, span);
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
                        let origin = RequirementOrigin::u32_operation(span);
                        changed |= self.require_u32_expr_if_not_guaranteed(lhs, origin.clone());
                        changed |= self.require_u32_expr_if_not_guaranteed(rhs, origin);
                    }
                    BinOp::U32Exp => {
                        changed |= self.require_felt_expr(lhs, span);
                        changed |= self.require_u32_expr_if_not_guaranteed(
                            rhs,
                            RequirementOrigin::u32_operation(span),
                        );
                    }
                    BinOp::And | BinOp::Or | BinOp::Xor => {
                        let origin = RequirementOrigin::bool_use(span);
                        changed |= self.require_bool_expr(lhs, origin.clone());
                        changed |= self.require_bool_expr(rhs, origin);
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
                        changed |= self.require_felt_expr(lhs, span);
                        changed |= self.require_felt_expr(rhs, span);
                    }
                }
                changed
            }
            Expr::EqW { lhs, rhs } => {
                let mut changed = false;
                for var in lhs.iter() {
                    changed |= self.apply_requirement_to_var(
                        var,
                        TypeFact::Felt,
                        RequirementOrigin::bool_use(span),
                    );
                }
                for var in rhs.iter() {
                    changed |= self.apply_requirement_to_var(
                        var,
                        TypeFact::Felt,
                        RequirementOrigin::bool_use(span),
                    );
                }
                changed
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                let mut changed = self.require_bool_expr(cond, RequirementOrigin::bool_use(span));
                changed |= self.seed_requirements_in_expr(then_expr, span);
                changed |= self.seed_requirements_in_expr(else_expr, span);
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
            Stmt::Assign {
                span, dest, expr, ..
            } => {
                let Some((req, origin)) = self.requirement_with_origin_for_var(dest) else {
                    return false;
                };
                if req == TypeFact::Felt {
                    return false;
                }
                self.apply_requirement_to_expr(expr, req, origin, *span)
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
                    let Some((req, origin)) = self.requirement_with_origin_for_var(&phi.dest)
                    else {
                        continue;
                    };
                    if req == TypeFact::Felt {
                        continue;
                    }
                    changed |= self.apply_requirement_to_var(&phi.then_var, req, origin.clone());
                    changed |= self.apply_requirement_to_var(&phi.else_var, req, origin);
                }
                changed
            }
            Stmt::While { body, phis, .. } | Stmt::Repeat { body, phis, .. } => {
                let mut changed = false;
                changed |= self.propagate_requirements_in_block(body);
                for phi in phis {
                    let Some((req, origin)) = self.requirement_with_origin_for_var(&phi.dest)
                    else {
                        continue;
                    };
                    if req == TypeFact::Felt {
                        continue;
                    }
                    changed |= self.apply_requirement_to_var(&phi.init, req, origin.clone());
                    changed |= self.apply_requirement_to_var(&phi.step, req, origin);
                }
                changed
            }
            Stmt::LocalLoad { load, .. } => {
                let mut changed = false;
                for output in &load.outputs {
                    let Some((req, origin)) = self.requirement_with_origin_for_var(output) else {
                        continue;
                    };
                    if req == TypeFact::Felt {
                        continue;
                    }
                    changed |= self.apply_requirement_to_local(load.index, req, origin);
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
                        let Some((req, origin)) = self.requirement_with_origin_for_var(output)
                        else {
                            continue;
                        };
                        if req == TypeFact::Felt {
                            continue;
                        }
                        changed |= self.apply_requirement_to_mem(addr_key, req, origin);
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
                    let Some((req, origin)) = self.mem_requirements.get(&addr_key).cloned() else {
                        return false;
                    };
                    if req != TypeFact::Felt {
                        for value in &store.values {
                            changed |= self.apply_requirement_to_var(value, req, origin.clone());
                        }
                    }
                }
                changed
            }
            Stmt::Call { call, .. } | Stmt::Exec { call, .. } | Stmt::SysCall { call, .. } => {
                let mut changed = false;
                if let Some(summary) = self.summary_for_target(&call.target).cloned() {
                    for (idx, result) in call.results.iter().enumerate() {
                        let Some((req, origin)) = self.requirement_with_origin_for_var(result)
                        else {
                            continue;
                        };
                        if req == TypeFact::Felt {
                            continue;
                        }
                        if let Some(Some(input_idx)) = summary.output_input_map.get(idx)
                            && let Some(arg) = call
                                .args
                                .len()
                                .checked_sub(1 + *input_idx)
                                .and_then(|i| call.args.get(i))
                        {
                            changed |= self.apply_requirement_to_var(arg, req, origin);
                        }
                    }
                }
                changed
            }
            Stmt::AdvLoad { .. }
            | Stmt::AdvStore { .. }
            | Stmt::DynCall { .. }
            | Stmt::Intrinsic { .. }
            | Stmt::Return { .. } => false,
        }
    }

    /// Apply a requirement to an expression from a required destination.
    fn apply_requirement_to_expr(
        &mut self,
        expr: &Expr,
        req: TypeFact,
        origin: RequirementOrigin,
        expr_span: SourceSpan,
    ) -> bool {
        match expr {
            Expr::Var(var) => self.apply_requirement_to_var(var, req, origin),
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                let mut changed =
                    self.require_bool_expr(cond, RequirementOrigin::bool_use(expr_span));
                changed |=
                    self.apply_requirement_to_expr(then_expr, req, origin.clone(), expr_span);
                changed |= self.apply_requirement_to_expr(else_expr, req, origin, expr_span);
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
            .map(|(fact, _)| *fact)
            .unwrap_or(TypeFact::Felt)
    }

    /// Read the current requirement and origin for a variable.
    fn requirement_with_origin_for_var(&self, var: &Var) -> Option<RequirementEntry> {
        self.required.get(&VarKey::from_var(var)).cloned()
    }

    /// Update a requirement map entry, preserving the original origin when the
    /// incoming fact is equal to the existing one.
    fn update_requirement_map<K>(
        map: &mut HashMap<K, RequirementEntry>,
        key: K,
        req: TypeFact,
        origin: RequirementOrigin,
    ) -> bool
    where
        K: Eq + Hash,
    {
        if req == TypeFact::Felt {
            return false;
        }
        match map.get(&key).cloned() {
            Some((current_fact, _)) => {
                let updated = current_fact.glb(req);
                if updated != current_fact {
                    map.insert(key, (updated, origin));
                    true
                } else {
                    false
                }
            }
            None => {
                map.insert(key, (req, origin));
                true
            }
        }
    }

    /// Apply a requirement to a variable.
    fn apply_requirement_to_var(
        &mut self,
        var: &Var,
        req: TypeFact,
        origin: RequirementOrigin,
    ) -> bool {
        Self::update_requirement_map(&mut self.required, VarKey::from_var(var), req, origin)
    }

    /// Apply a requirement to a local slot.
    fn apply_requirement_to_local(
        &mut self,
        index: u16,
        req: TypeFact,
        origin: RequirementOrigin,
    ) -> bool {
        Self::update_requirement_map(&mut self.local_requirements, index, req, origin)
    }

    /// Apply a requirement to a memory location.
    fn apply_requirement_to_mem(
        &mut self,
        key: MemAddressKey,
        req: TypeFact,
        origin: RequirementOrigin,
    ) -> bool {
        Self::update_requirement_map(&mut self.mem_requirements, key, req, origin)
    }

    /// Require a variable to be u32 only if it is not already guaranteed u32.
    fn require_u32_var_if_not_guaranteed(&mut self, var: &Var, origin: RequirementOrigin) -> bool {
        let actual = self.inferred_type_for_var(var);
        if actual.satisfies(TypeFact::U32) {
            false
        } else {
            self.apply_requirement_to_var(var, TypeFact::U32, origin)
        }
    }

    /// Require that an expression is boolean.
    fn require_bool_expr(&mut self, expr: &Expr, origin: RequirementOrigin) -> bool {
        match expr {
            Expr::Var(var) => self.apply_requirement_to_var(var, TypeFact::Bool, origin),
            Expr::Unary(UnOp::Not, inner) => self.require_bool_expr(inner, origin),
            Expr::Binary(BinOp::And | BinOp::Or, lhs, rhs) => {
                self.require_bool_expr(lhs, origin.clone()) | self.require_bool_expr(rhs, origin)
            }
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.require_bool_expr(cond, RequirementOrigin::bool_use(origin.span))
                    | self.require_bool_expr(then_expr, origin.clone())
                    | self.require_bool_expr(else_expr, origin)
            }
            Expr::EqW { lhs, rhs } => {
                let mut changed = false;
                for var in lhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeFact::Felt, origin.clone());
                }
                for var in rhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeFact::Felt, origin.clone());
                }
                changed
            }
            Expr::True | Expr::False | Expr::Constant(_) | Expr::Binary(..) | Expr::Unary(..) => {
                false
            }
        }
    }

    /// Require that an expression is U32.
    fn require_u32_expr(&mut self, expr: &Expr, origin: RequirementOrigin) -> bool {
        match expr {
            Expr::Var(var) => self.apply_requirement_to_var(var, TypeFact::U32, origin),
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.require_bool_expr(cond, RequirementOrigin::bool_use(origin.span))
                    | self.require_u32_expr(then_expr, origin.clone())
                    | self.require_u32_expr(else_expr, origin)
            }
            Expr::EqW { .. } => false,
            Expr::True | Expr::False | Expr::Constant(_) | Expr::Binary(..) | Expr::Unary(..) => {
                false
            }
        }
    }

    /// Require an expression to be u32 only if it is not already guaranteed u32.
    fn require_u32_expr_if_not_guaranteed(
        &mut self,
        expr: &Expr,
        origin: RequirementOrigin,
    ) -> bool {
        let actual = self.infer_expr_type(expr);
        if actual.satisfies(TypeFact::U32) {
            false
        } else {
            self.require_u32_expr(expr, origin)
        }
    }

    /// Require that an expression is Felt-compatible.
    fn require_felt_expr(&mut self, expr: &Expr, span: SourceSpan) -> bool {
        match expr {
            Expr::Var(_) => false,
            Expr::Ternary {
                cond,
                then_expr,
                else_expr,
            } => {
                self.require_bool_expr(cond, RequirementOrigin::bool_use(span))
                    | self.require_felt_expr(then_expr, span)
                    | self.require_felt_expr(else_expr, span)
            }
            Expr::EqW { .. } => false,
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
            Stmt::Assign {
                span, dest, expr, ..
            } => {
                // Wider-output operation. If the destination has a
                // requirement stricter than what the RHS expression produces,
                // and the expression is not a simple variable copy (which just
                // propagates, not originates), emit a diagnostic.
                let req = self.requirement_for_var(dest);
                if req != TypeFact::Felt {
                    let actual = self.infer_expr_type(expr);
                    if !actual.satisfies(req) && !matches!(expr, Expr::Var(_)) {
                        let (_, origin) = self
                            .requirement_with_origin_for_var(dest)
                            .expect("non-Felt assignment requirement must carry an origin");
                        let mut diag = TypeDiagnostic::new(
                            self.proc_path.clone(),
                            *span,
                            format!(
                                "expression produces {} but {} is required",
                                actual.to_inferred_type(),
                                req.to_requirement(),
                            ),
                        );
                        diag.expected = Some(req.to_requirement());
                        diag.actual = Some(actual.to_inferred_type());
                        diag.source_span = Some(origin.span);
                        diag.source_description = Some(origin.description(req));
                        self.diagnostics.push(diag);
                    }
                }
            }
            Stmt::MemLoad { .. } | Stmt::MemStore { .. } => {
                // Address requirements back-propagate to callers via
                // TypeSummary.inputs — no interior diagnostic needed.
            }
            Stmt::Call { span, call }
            | Stmt::Exec { span, call }
            | Stmt::SysCall { span, call } => {
                let (is_opaque, suppress) = self.call_result_suppression(call);
                if !is_opaque {
                    self.collect_result_widening_diagnostics(
                        *span,
                        &call.results,
                        &format!("call to {}", call.target),
                        &suppress,
                    );
                }
            }
            Stmt::Intrinsic { span, intrinsic } => {
                // Advice-sourced intrinsics have a separate analysis pass;
                // skip result-widening diagnostics for them.
                if !Self::is_advice_intrinsic(&intrinsic.name) {
                    self.collect_result_widening_diagnostics(
                        *span,
                        &intrinsic.results,
                        &format!("{} intrinsic", intrinsic.name),
                        &[],
                    );
                }
            }
            Stmt::DynCall { span, results, .. } => {
                self.collect_result_widening_diagnostics(*span, results, "dynamic call", &[]);
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                self.collect_diagnostics_in_block(then_body);
                self.collect_diagnostics_in_block(else_body);
            }
            Stmt::While { body, .. } | Stmt::Repeat { body, .. } => {
                self.collect_diagnostics_in_block(body);
            }
            Stmt::AdvLoad { .. }
            | Stmt::AdvStore { .. }
            | Stmt::LocalLoad { .. }
            | Stmt::LocalStore { .. }
            | Stmt::LocalStoreW { .. }
            | Stmt::Return { .. } => {}
        }
    }

    /// Emit diagnostics for public procedure inputs that don't satisfy their requirements.
    fn collect_input_diagnostics(&mut self) {
        if self.visibility != Visibility::Public {
            return;
        }
        for index in (0..self.input_count).rev() {
            let key = Self::input_var_key(index);
            let Some((req, origin)) = self.required.get(&key).cloned() else {
                continue;
            };
            if req == TypeFact::Felt {
                continue; // No specific requirement.
            }
            let inferred = self.inferred.get(&key).copied().unwrap_or(TypeFact::Felt);
            if !inferred.satisfies(req) {
                let mut diag = TypeDiagnostic::new(
                    self.proc_path.clone(),
                    self.proc_span,
                    format!(
                        "public procedure input {} must be validated as {} before a use that requires it",
                        index + 1,
                        req.to_requirement(),
                    ),
                );
                diag.expected = Some(req.to_requirement());
                diag.actual = Some(inferred.to_inferred_type());
                diag.source_span = Some(origin.span);
                diag.source_description = Some(origin.description(req));
                self.diagnostics.push(diag);
            }
        }
    }

    /// Compute suppression flags for call result-widening diagnostics.
    ///
    /// Returns `(is_opaque, suppress)` where `suppress[i]` is `true` when
    /// result `i` is a passthrough whose requirement was propagated backward
    /// to the caller's argument. Suppressed results should not produce
    /// result-widening diagnostics because a root-cause diagnostic will
    /// fire at the argument's origin instead.
    fn call_result_suppression(&self, call: &Call) -> (bool, Vec<bool>) {
        let Some(summary) = self.summary_for_target(&call.target) else {
            return (false, Vec::new());
        };
        if summary.is_opaque() {
            return (true, Vec::new());
        }
        let suppress = call
            .results
            .iter()
            .enumerate()
            .map(|(idx, result)| {
                let req = self.requirement_for_var(result);
                if req == TypeFact::Felt {
                    return false;
                }
                if let Some(input_idx) = summary.output_input_map.get(idx).copied().flatten()
                    && let Some(arg) = call
                        .args
                        .len()
                        .checked_sub(1 + input_idx)
                        .and_then(|i| call.args.get(i))
                {
                    let arg_req = self.requirement_for_var(arg);
                    return arg_req.satisfies(req);
                }
                false
            })
            .collect();
        (false, suppress)
    }

    /// Emit diagnostics for result variables whose inferred type is wider than
    /// the back-propagated requirement.
    ///
    /// Call, intrinsic, and dynamic-call results are terminal points for
    /// backward propagation: their type is determined by the callee or
    /// instruction, not by upstream data flow. When a result carries a
    /// requirement stricter than its inferred type, the mismatch is reported
    /// here.
    fn collect_result_widening_diagnostics(
        &mut self,
        span: SourceSpan,
        results: &[Var],
        label: &str,
        suppress: &[bool],
    ) {
        for (idx, result) in results.iter().enumerate() {
            if suppress.get(idx).copied().unwrap_or(false) {
                continue;
            }
            let req = self.requirement_for_var(result);
            if req == TypeFact::Felt {
                continue;
            }
            let actual = self.inferred_type_for_var(result);
            if !actual.satisfies(req) {
                let (_, origin) = self
                    .requirement_with_origin_for_var(result)
                    .expect("non-Felt result requirement must carry an origin");
                let mut diag = TypeDiagnostic::new(
                    self.proc_path.clone(),
                    span,
                    format!(
                        "{} result {} produces {} but {} is required",
                        label,
                        idx,
                        actual.to_inferred_type(),
                        req.to_requirement(),
                    ),
                );
                diag.expected = Some(req.to_requirement());
                diag.actual = Some(actual.to_inferred_type());
                diag.source_span = Some(origin.span);
                diag.source_description = Some(origin.description(req));
                self.diagnostics.push(diag);
            }
        }
    }

    /// Look up a callee summary by target string.
    fn summary_for_target(&self, target: &str) -> Option<&TypeSummary> {
        let key = SymbolPath::new(target.to_string());
        self.callee_summaries.get(&key)
    }
}

#[cfg(test)]
mod tests {
    // Origin-tracing tests have been moved to `crate::passthrough::tests`,
    // which provides equivalent (and broader) coverage using the standalone
    // `compute_passthrough_map` function.
}
