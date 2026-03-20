//! Intraprocedural type inference and mismatch checking.

use std::collections::HashMap;

use miden_assembly_syntax::debuginfo::SourceSpan;

use crate::ir::{BinOp, Constant, Expr, Stmt, UnOp, ValueId, Var};
use crate::symbol::path::SymbolPath;

use super::domain::{Compatibility, InferredType, TypeRequirement, VarKey, check_compatibility};
use super::summary::{TypeDiagnostic, TypeSummary, TypeSummaryMap};

/// Maximum number of fixed-point iterations for local type inference.
const MAX_TYPE_PASSES: usize = 128;

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
    inferred: HashMap<VarKey, InferredType>,
    /// Inferred requirements for variables.
    required: HashMap<VarKey, TypeRequirement>,
    /// Collected diagnostics.
    diagnostics: Vec<TypeDiagnostic>,
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
        }
    }

    /// Run fixed-point inference and mismatch checks.
    fn analyze(&mut self, stmts: &[Stmt]) -> ProcTypeAnalysisResult {
        for _ in 0..MAX_TYPE_PASSES {
            let mut changed = false;
            changed |= self.infer_types_in_block(stmts);
            changed |= self.seed_requirements_in_block(stmts);
            changed |= self.propagate_requirements_in_block(stmts);
            if !changed {
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
            let req = self
                .required
                .get(&key)
                .copied()
                .unwrap_or(TypeRequirement::Unknown);
            inputs.push(req);
        }

        let mut outputs = Vec::with_capacity(self.output_count);
        let return_values = Self::find_return_values(stmts);
        for index in (0..self.output_count).rev() {
            let ty = return_values
                .and_then(|values| values.get(index))
                .map(|var| self.inferred_type_for_var(var))
                .unwrap_or(InferredType::Unknown);
            outputs.push(ty);
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
                self.set_inferred_type_for_var(dest, self.infer_expr_type(expr))
            }
            Stmt::MemLoad { load, .. } => {
                let mut changed = false;
                for output in &load.outputs {
                    changed |= self.set_inferred_type_for_var(output, InferredType::Felt);
                }
                changed
            }
            Stmt::LocalLoad { load, .. } => {
                let mut changed = false;
                for output in &load.outputs {
                    changed |= self.set_inferred_type_for_var(output, InferredType::Felt);
                }
                changed
            }
            Stmt::AdvLoad { load, .. } => {
                let mut changed = false;
                for output in &load.outputs {
                    changed |= self.set_inferred_type_for_var(output, InferredType::Felt);
                }
                changed
            }
            Stmt::Call { call, .. } | Stmt::Exec { call, .. } | Stmt::SysCall { call, .. } => {
                self.assign_call_result_types(&call.target, &call.results)
            }
            Stmt::DynCall { results, .. } => {
                let mut changed = false;
                for result in results {
                    changed |= self.set_inferred_type_for_var(result, InferredType::Unknown);
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
                        changed |= self.set_inferred_type_for_var(arg, InferredType::U32);
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
                    changed |=
                        self.set_inferred_type_for_var(&phi.dest, then_ty.combine_paths(else_ty));
                }
                changed
            }
            Stmt::While { body, phis, .. } | Stmt::Repeat { body, phis, .. } => {
                let mut changed = false;
                changed |= self.infer_types_in_block(body);
                for phi in phis {
                    let init_ty = self.inferred_type_for_var(&phi.init);
                    let step_ty = self.inferred_type_for_var(&phi.step);
                    changed |=
                        self.set_inferred_type_for_var(&phi.dest, init_ty.combine_paths(step_ty));
                }
                changed
            }
            Stmt::MemStore { .. }
            | Stmt::AdvStore { .. }
            | Stmt::LocalStore { .. }
            | Stmt::LocalStoreW { .. }
            | Stmt::Return { .. } => false,
        }
    }

    /// Assign types to call results from a known callee summary.
    fn assign_call_result_types(&mut self, target: &str, results: &[Var]) -> bool {
        let mut changed = false;
        let Some(summary) = self.summary_for_target(target).cloned() else {
            return false;
        };
        for (idx, result) in results.iter().enumerate() {
            let ty = if summary.is_unknown() {
                InferredType::Unknown
            } else {
                summary
                    .outputs
                    .get(idx)
                    .copied()
                    .unwrap_or(InferredType::Unknown)
            };
            changed |= self.set_inferred_type_for_var(result, ty);
        }
        changed
    }

    /// Infer result type for an intrinsic operation.
    fn intrinsic_result_type(&self, name: &str) -> InferredType {
        if name.starts_with("u32") || name == "sdepth" {
            InferredType::U32
        } else if name.starts_with("locaddr.") {
            InferredType::Address
        } else {
            InferredType::Unknown
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
    fn infer_expr_type(&self, expr: &Expr) -> InferredType {
        match expr {
            Expr::True | Expr::False => InferredType::Bool,
            Expr::Var(var) => self.inferred_type_for_var(var),
            Expr::Constant(constant) => self.infer_constant_type(constant),
            Expr::Unary(op, inner) => self.infer_unary_expr_type(*op, inner),
            Expr::Binary(op, lhs, rhs) => self.infer_binary_expr_type(*op, lhs, rhs),
            Expr::EqW { .. } => InferredType::Bool,
            Expr::Ternary {
                then_expr,
                else_expr,
                ..
            } => {
                let then_ty = self.infer_expr_type(then_expr);
                let else_ty = self.infer_expr_type(else_expr);
                then_ty.combine_paths(else_ty)
            }
        }
    }

    /// Infer type for a constant expression.
    ///
    /// `Felt(0)` and `Felt(1)` are inferred as `Bool` since they are the
    /// most precise type for these values. The lattice `Bool <: U32 <: Felt`
    /// ensures they widen correctly in arithmetic or u32 contexts.
    fn infer_constant_type(&self, constant: &Constant) -> InferredType {
        match constant {
            Constant::Felt(0 | 1) => InferredType::Bool,
            Constant::Felt(_) | Constant::Defined(_) => InferredType::Felt,
            Constant::Word(_) => InferredType::Unknown,
        }
    }

    /// Infer type for a unary expression.
    fn infer_unary_expr_type(&self, op: UnOp, _inner: &Expr) -> InferredType {
        match op {
            UnOp::Not => InferredType::Bool,
            UnOp::U32Test => InferredType::Bool,
            UnOp::U32Cast
            | UnOp::U32Not
            | UnOp::U32Clz
            | UnOp::U32Ctz
            | UnOp::U32Clo
            | UnOp::U32Cto => InferredType::U32,
            UnOp::Neg | UnOp::Inv | UnOp::Pow2 => InferredType::Felt,
        }
    }

    /// Infer type for a binary expression.
    fn infer_binary_expr_type(&self, op: BinOp, _lhs: &Expr, _rhs: &Expr) -> InferredType {
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
            | BinOp::U32Gte => InferredType::Bool,
            BinOp::U32And
            | BinOp::U32Or
            | BinOp::U32Xor
            | BinOp::U32Shl
            | BinOp::U32Shr
            | BinOp::U32Rotr
            | BinOp::U32WrappingAdd
            | BinOp::U32WrappingSub
            | BinOp::U32WrappingMul => InferredType::U32,
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::U32Exp => InferredType::Felt,
        }
    }

    /// Read inferred type for a variable.
    fn inferred_type_for_var(&self, var: &Var) -> InferredType {
        self.inferred
            .get(&VarKey::from_var(var))
            .copied()
            .unwrap_or(InferredType::Unknown)
    }

    /// Update inferred type for a variable.
    fn set_inferred_type_for_var(&mut self, var: &Var, new_type: InferredType) -> bool {
        let key = VarKey::from_var(var);
        let current = self
            .inferred
            .get(&key)
            .copied()
            .unwrap_or(InferredType::Unknown);
        let updated = current.refine(new_type);
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
                    changed |= self.apply_requirement_to_var(address, TypeRequirement::Address);
                }
                changed
            }
            Stmt::MemStore { store, .. } => {
                let mut changed = false;
                for address in &store.address {
                    changed |= self.apply_requirement_to_var(address, TypeRequirement::Address);
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
        if summary.is_unknown() {
            return false;
        }
        let mut changed = false;
        for (arg, expected) in args.iter().zip(summary.inputs.iter().copied()) {
            changed |= self.apply_requirement_to_var(arg, expected);
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
                    changed |= self.apply_requirement_to_var(var, TypeRequirement::Felt);
                }
                for var in rhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeRequirement::Felt);
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
                if req == TypeRequirement::Unknown {
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
                    if req == TypeRequirement::Unknown {
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
                    if req == TypeRequirement::Unknown {
                        continue;
                    }
                    changed |= self.apply_requirement_to_var(&phi.init, req);
                    changed |= self.apply_requirement_to_var(&phi.step, req);
                }
                changed
            }
            Stmt::MemLoad { .. }
            | Stmt::MemStore { .. }
            | Stmt::AdvLoad { .. }
            | Stmt::AdvStore { .. }
            | Stmt::LocalLoad { .. }
            | Stmt::LocalStore { .. }
            | Stmt::LocalStoreW { .. }
            | Stmt::Call { .. }
            | Stmt::Exec { .. }
            | Stmt::SysCall { .. }
            | Stmt::DynCall { .. }
            | Stmt::Intrinsic { .. }
            | Stmt::Return { .. } => false,
        }
    }

    /// Apply a requirement to an expression from a required destination.
    fn apply_requirement_to_expr(&mut self, expr: &Expr, req: TypeRequirement) -> bool {
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
    fn requirement_for_var(&self, var: &Var) -> TypeRequirement {
        self.required
            .get(&VarKey::from_var(var))
            .copied()
            .unwrap_or(TypeRequirement::Unknown)
    }

    /// Apply a requirement to a variable.
    fn apply_requirement_to_var(&mut self, var: &Var, req: TypeRequirement) -> bool {
        if req == TypeRequirement::Unknown {
            return false;
        }
        let key = VarKey::from_var(var);
        let current = self
            .required
            .get(&key)
            .copied()
            .unwrap_or(TypeRequirement::Unknown);
        let updated = current.meet(req);
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
        match check_compatibility(actual, TypeRequirement::U32) {
            Compatibility::Compatible => false,
            Compatibility::Incompatible | Compatibility::Indeterminate => {
                self.apply_requirement_to_var(var, TypeRequirement::U32)
            }
        }
    }

    /// Require that an expression is boolean.
    fn require_bool_expr(&mut self, expr: &Expr) -> bool {
        match expr {
            Expr::Var(var) => self.apply_requirement_to_var(var, TypeRequirement::Bool),
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
                    changed |= self.apply_requirement_to_var(var, TypeRequirement::Felt);
                }
                for var in rhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeRequirement::Felt);
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
            Expr::Var(var) => self.apply_requirement_to_var(var, TypeRequirement::U32),
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
        match check_compatibility(actual, TypeRequirement::U32) {
            Compatibility::Compatible => false,
            Compatibility::Incompatible | Compatibility::Indeterminate => {
                self.require_u32_expr(expr)
            }
        }
    }

    /// Require that an expression is Felt-compatible.
    fn require_felt_expr(&mut self, expr: &Expr) -> bool {
        match expr {
            Expr::Var(var) => self.apply_requirement_to_var(var, TypeRequirement::Felt),
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
                    changed |= self.apply_requirement_to_var(var, TypeRequirement::Felt);
                }
                for var in rhs.iter() {
                    changed |= self.apply_requirement_to_var(var, TypeRequirement::Felt);
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
                    self.check_var_requirement(
                        address,
                        TypeRequirement::Address,
                        *span,
                        "memory load address is not guaranteed Address",
                    );
                }
            }
            Stmt::MemStore { span, store } => {
                for address in &store.address {
                    self.check_var_requirement(
                        address,
                        TypeRequirement::Address,
                        *span,
                        "memory store address is not guaranteed Address",
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
                            TypeRequirement::U32,
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
                    TypeRequirement::Bool,
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
                    TypeRequirement::Bool,
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
    fn collect_call_arg_diagnostics(&mut self, span: SourceSpan, target: &str, args: &[Var]) {
        let Some(summary) = self.summary_for_target(target).cloned() else {
            return;
        };
        if summary.is_unknown() {
            return;
        }
        let callee = SymbolPath::new(target.to_string());
        for (index, (arg, expected)) in args.iter().zip(summary.inputs.iter()).enumerate() {
            let actual = self.inferred_type_for_var(arg);
            match check_compatibility(actual, *expected) {
                Compatibility::Compatible | Compatibility::Indeterminate => {}
                Compatibility::Incompatible => {
                    let mut diagnostic = TypeDiagnostic::new(
                        self.proc_path.clone(),
                        span,
                        format!(
                            "argument {index} to `{callee}` expects {expected}, but inferred {actual}"
                        ),
                    );
                    diagnostic.callee = Some(callee.clone());
                    diagnostic.arg_index = Some(index);
                    diagnostic.expected = Some(*expected);
                    diagnostic.actual = Some(actual);
                    self.diagnostics.push(diagnostic);
                }
            }
        }
    }

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
                    TypeRequirement::Bool,
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
        expected: TypeRequirement,
        span: SourceSpan,
        context: &str,
    ) {
        let actual = self.infer_expr_type(expr);
        match check_compatibility(actual, expected) {
            Compatibility::Compatible | Compatibility::Indeterminate => {}
            Compatibility::Incompatible => {
                self.diagnostics.push(TypeDiagnostic::new(
                    self.proc_path.clone(),
                    span,
                    format!("{context} (inferred {actual})"),
                ));
            }
        }
    }

    /// Check whether a variable satisfies a requirement.
    fn check_var_requirement(
        &mut self,
        var: &Var,
        expected: TypeRequirement,
        span: SourceSpan,
        context: &str,
    ) {
        let actual = self.inferred_type_for_var(var);
        match check_compatibility(actual, expected) {
            Compatibility::Compatible | Compatibility::Indeterminate => {}
            Compatibility::Incompatible => {
                self.diagnostics.push(TypeDiagnostic::new(
                    self.proc_path.clone(),
                    span,
                    format!("{context} (inferred {actual})"),
                ));
            }
        }
    }

    /// Look up a callee summary by target string.
    fn summary_for_target(&self, target: &str) -> Option<&TypeSummary> {
        let key = SymbolPath::new(target.to_string());
        self.callee_summaries.get(&key)
    }
}
