//! Expression propagation for structured code.
//!
//! This module performs expression propagation on structured code (after flattening).
//! Unlike CFG-based propagation, this version correctly handles loop boundaries by
//! never propagating expressions into loops that might modify variables used by
//! the expression.
//!
//! # Safety Invariant
//!
//! An expression `e` can be propagated from definition `d` to use `u` only if:
//! 1. The use is in an `Assign` statement (expressions can be substituted)
//! 2. The variable is used exactly once in the target expression
//! 3. No intervening statement redefines variables used by `e`
//! 4. The use is NOT inside a loop that defines any variable used by `e`

use std::collections::{HashMap, HashSet};

use crate::ssa::{Expr, Stmt};

/// Maximum number of propagation passes to avoid infinite loops.
const MAX_PROPAGATION_PASSES: usize = 100;

/// Maximum expression complexity for propagation (prevents blowup).
const MAX_EXPR_COMPLEXITY: usize = 4;

/// Maximum combined complexity of expression + use site.
const MAX_COMBINED_COMPLEXITY: usize = 7;

// ============================================================================
// Public API
// ============================================================================

/// Propagate expressions in structured code.
///
/// This replaces variable uses with their defining expressions where safe,
/// respecting loop boundaries to ensure semantic correctness.
pub fn propagate_expressions(code: &mut Vec<Stmt>) {
    for _ in 0..MAX_PROPAGATION_PASSES {
        if !propagate_one_pass(code) {
            break;
        }
    }
}

// ============================================================================
// Single Propagation Pass
// ============================================================================

/// Perform one pass of expression propagation.
/// Returns true if any propagation was performed.
fn propagate_one_pass(code: &mut Vec<Stmt>) -> bool {
    // Collect all definitions at the top level (not inside loops).
    let defs = collect_top_level_defs(code);

    // Try to propagate each definition.
    for (var_index, (def_idx, def_expr)) in defs {
        let props = ExprProperties::compute(&def_expr);
        if props.contains_unknown || props.complexity > MAX_EXPR_COMPLEXITY {
            continue;
        }

        // Find uses of this variable that can be propagated.
        if let Some(use_info) = find_propagatable_use(code, var_index, def_idx, &def_expr, &props) {
            // Perform the substitution.
            substitute_at_path(code, &use_info.path, var_index, &def_expr);
            return true;
        }
    }

    false
}

/// Information about a use site that can receive propagation.
struct UseInfo {
    /// Path to the statement containing the use.
    path: Vec<usize>,
}

/// Collect definitions at the top level of the code (not inside loops).
/// Returns a map from variable index to (statement index, expression).
fn collect_top_level_defs(code: &[Stmt]) -> HashMap<usize, (usize, Expr)> {
    let mut defs = HashMap::new();

    for (idx, stmt) in code.iter().enumerate() {
        if let Stmt::Assign { dest, expr } = stmt {
            // Only collect simple assignments (not inside control flow).
            defs.insert(dest.index, (idx, expr.clone()));
        }
    }

    defs
}

/// Find a use of `var_index` that can be safely propagated.
fn find_propagatable_use(
    code: &[Stmt],
    var_index: usize,
    def_idx: usize,
    def_expr: &Expr,
    props: &ExprProperties,
) -> Option<UseInfo> {
    let used_vars: HashSet<usize> = expr_uses_vars(def_expr).into_iter().collect();

    // Search for uses after the definition.
    for (idx, stmt) in code.iter().enumerate().skip(def_idx + 1) {
        // Check if this statement uses the variable and can receive propagation.
        if let Some(path) = can_propagate_into(stmt, var_index, &used_vars, props, vec![idx]) {
            return Some(UseInfo { path });
        }

        // Check if this statement kills propagation (redefines used vars or is a barrier).
        if is_propagation_barrier(stmt, &used_vars) {
            return None;
        }
    }

    None
}

/// Check if propagation can proceed into this statement.
/// Returns the path to the use site if propagation is valid.
fn can_propagate_into(
    stmt: &Stmt,
    var_index: usize,
    used_vars: &HashSet<usize>,
    props: &ExprProperties,
    current_path: Vec<usize>,
) -> Option<Vec<usize>> {
    match stmt {
        Stmt::Assign { dest, expr } => {
            // Can propagate if:
            // 1. This assignment uses the variable
            // 2. The variable appears exactly once
            // 3. Combined complexity is acceptable
            let occurrences = count_var_in_expr(expr, var_index);
            if occurrences == 1 {
                let use_complexity = expr_complexity(expr);
                if props.complexity + use_complexity <= MAX_COMBINED_COMPLEXITY {
                    return Some(current_path);
                }
            }

            // Can't propagate into this assignment, but check if it's a barrier.
            if used_vars.contains(&dest.index) {
                return None; // Variable redefined, stop searching.
            }
            None
        }

        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            // Can propagate into condition if variable is used there.
            let cond_uses = count_var_in_expr(cond, var_index);
            if cond_uses == 1 {
                let use_complexity = expr_complexity(cond);
                if props.complexity + use_complexity <= MAX_COMBINED_COMPLEXITY {
                    return Some(current_path);
                }
            }

            // Check branches - but only if neither branch defines variables we need.
            let then_defs = collect_defined_vars_in_block(then_body);
            let else_defs = collect_defined_vars_in_block(else_body);

            // If either branch defines a variable we use, we can't propagate past this If.
            if then_defs.intersection(used_vars).next().is_some()
                || else_defs.intersection(used_vars).next().is_some()
            {
                return None;
            }

            // Search in then branch.
            for (i, inner) in then_body.iter().enumerate() {
                let mut path = current_path.clone();
                path.push(i);
                if let Some(result) =
                    can_propagate_into_if_branch(inner, var_index, used_vars, props, path, true)
                {
                    return Some(result);
                }
            }

            // Search in else branch.
            for (i, inner) in else_body.iter().enumerate() {
                let mut path = current_path.clone();
                path.push(i);
                if let Some(result) =
                    can_propagate_into_if_branch(inner, var_index, used_vars, props, path, false)
                {
                    return Some(result);
                }
            }

            None
        }

        Stmt::Repeat { body, .. } => {
            // CRITICAL: Never propagate into a repeat loop if the loop body
            // defines any variable used by the expression being propagated.
            let loop_defs = collect_defined_vars_in_block(body);
            if loop_defs.intersection(used_vars).next().is_some() {
                return None; // Unsafe to propagate.
            }

            // Also don't propagate if the variable we're propagating is used inside,
            // as the loop might be modifying stack positions semantically.
            // Conservative: don't propagate into repeat loops at all.
            // This is safe and matches the expected behavior.
            None
        }

        Stmt::While { cond, body } => {
            // Similar to Repeat - don't propagate into while loops.
            let loop_defs = collect_defined_vars_in_block(body);
            if loop_defs.intersection(used_vars).next().is_some() {
                return None;
            }

            // Can propagate into condition if it doesn't involve loop-modified vars.
            let cond_uses = count_var_in_expr(cond, var_index);
            if cond_uses == 1 && loop_defs.intersection(used_vars).next().is_none() {
                let use_complexity = expr_complexity(cond);
                if props.complexity + use_complexity <= MAX_COMBINED_COMPLEXITY {
                    return Some(current_path);
                }
            }

            None
        }

        // These statements can't receive expression propagation.
        Stmt::Return(_)
        | Stmt::Phi { .. }
        | Stmt::MemLoad(_)
        | Stmt::MemStore(_)
        | Stmt::AdvLoad(_)
        | Stmt::AdvStore(_)
        | Stmt::LocalLoad(_)
        | Stmt::LocalStore(_)
        | Stmt::Call(_)
        | Stmt::Exec(_)
        | Stmt::SysCall(_)
        | Stmt::DynCall { .. }
        | Stmt::Intrinsic(_)
        | Stmt::Inst(_)
        | Stmt::Nop => None,

        // Branch markers should not exist in structured code.
        Stmt::IfBranch(_) | Stmt::WhileBranch(_) | Stmt::RepeatBranch(_) => None,
    }
}

/// Helper for propagating into if branches (marks which branch we're in).
fn can_propagate_into_if_branch(
    stmt: &Stmt,
    var_index: usize,
    used_vars: &HashSet<usize>,
    props: &ExprProperties,
    current_path: Vec<usize>,
    _is_then: bool,
) -> Option<Vec<usize>> {
    can_propagate_into(stmt, var_index, used_vars, props, current_path)
}

/// Check if a statement is a barrier that prevents further propagation.
fn is_propagation_barrier(stmt: &Stmt, used_vars: &HashSet<usize>) -> bool {
    match stmt {
        Stmt::Assign { dest, .. } => used_vars.contains(&dest.index),

        Stmt::Repeat { body, .. } | Stmt::While { body, .. } => {
            // A loop is a barrier if it defines any variable we're using.
            let loop_defs = collect_defined_vars_in_block(body);
            loop_defs.intersection(used_vars).next().is_some()
        }

        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            // An if is a barrier if either branch defines a variable we're using.
            let then_defs = collect_defined_vars_in_block(then_body);
            let else_defs = collect_defined_vars_in_block(else_body);
            then_defs.intersection(used_vars).next().is_some()
                || else_defs.intersection(used_vars).next().is_some()
        }

        // Side-effecting statements are barriers.
        Stmt::MemLoad(_)
        | Stmt::MemStore(_)
        | Stmt::AdvLoad(_)
        | Stmt::AdvStore(_)
        | Stmt::LocalLoad(_)
        | Stmt::LocalStore(_)
        | Stmt::Call(_)
        | Stmt::Exec(_)
        | Stmt::SysCall(_)
        | Stmt::DynCall { .. }
        | Stmt::Intrinsic(_) => true,

        _ => false,
    }
}

// ============================================================================
// Substitution
// ============================================================================

/// Substitute variable `var_index` with `expr` at the given path.
fn substitute_at_path(code: &mut Vec<Stmt>, path: &[usize], var_index: usize, expr: &Expr) {
    if path.is_empty() {
        return;
    }

    let idx = path[0];
    if path.len() == 1 {
        // This is the target statement.
        substitute_in_stmt(&mut code[idx], var_index, expr);
    } else {
        // Navigate into nested structure.
        match &mut code[idx] {
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                // For If, we need to determine which branch to descend into.
                // The path encoding here is simplified - we just try both.
                if path.len() > 1 {
                    let inner_path = &path[1..];
                    // Try then branch first.
                    if inner_path[0] < then_body.len() {
                        substitute_at_path(then_body, inner_path, var_index, expr);
                    } else {
                        // Adjust index for else branch.
                        let adjusted_idx = inner_path[0] - then_body.len();
                        if adjusted_idx < else_body.len() {
                            let mut adjusted_path = inner_path.to_vec();
                            adjusted_path[0] = adjusted_idx;
                            substitute_at_path(else_body, &adjusted_path, var_index, expr);
                        }
                    }
                }
                // Also substitute in condition if it contains the variable.
                substitute_in_expr(cond, var_index, expr);
            }
            Stmt::Repeat { body, .. } | Stmt::While { body, .. } => {
                substitute_at_path(body, &path[1..], var_index, expr);
            }
            _ => {
                // Direct statement - substitute in it.
                substitute_in_stmt(&mut code[idx], var_index, expr);
            }
        }
    }
}

/// Substitute variable in a statement.
fn substitute_in_stmt(stmt: &mut Stmt, var_index: usize, with: &Expr) {
    match stmt {
        Stmt::Assign { expr, .. } => {
            substitute_in_expr(expr, var_index, with);
        }
        Stmt::If { cond, .. } => {
            substitute_in_expr(cond, var_index, with);
        }
        Stmt::While { cond, .. } => {
            substitute_in_expr(cond, var_index, with);
        }
        _ => {}
    }
}

/// Substitute variable in an expression.
fn substitute_in_expr(expr: &mut Expr, var_index: usize, with: &Expr) {
    match expr {
        Expr::Var(v) if v.index == var_index => {
            *expr = with.clone();
        }
        Expr::Var(_) => {}
        Expr::Binary(_, a, b) => {
            substitute_in_expr(a, var_index, with);
            substitute_in_expr(b, var_index, with);
        }
        Expr::Unary(_, a) => {
            substitute_in_expr(a, var_index, with);
        }
        Expr::True | Expr::False | Expr::Constant(_) | Expr::Unknown => {}
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

/// Collect all variables defined in a block of statements.
fn collect_defined_vars_in_block(stmts: &[Stmt]) -> HashSet<usize> {
    let mut defs = HashSet::new();
    for stmt in stmts {
        collect_defined_vars(stmt, &mut defs);
    }
    defs
}

/// Recursively collect all variables defined by a statement.
fn collect_defined_vars(stmt: &Stmt, defs: &mut HashSet<usize>) {
    match stmt {
        Stmt::Assign { dest, .. } => {
            defs.insert(dest.index);
        }
        Stmt::Phi { var, .. } => {
            defs.insert(var.index);
        }
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            for s in then_body {
                collect_defined_vars(s, defs);
            }
            for s in else_body {
                collect_defined_vars(s, defs);
            }
        }
        Stmt::Repeat { body, .. } | Stmt::While { body, .. } => {
            for s in body {
                collect_defined_vars(s, defs);
            }
        }
        Stmt::MemLoad(load) => {
            for v in &load.outputs {
                defs.insert(v.index);
            }
        }
        Stmt::AdvLoad(load) => {
            for v in &load.outputs {
                defs.insert(v.index);
            }
        }
        Stmt::LocalLoad(load) => {
            for v in &load.outputs {
                defs.insert(v.index);
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in &call.results {
                defs.insert(v.index);
            }
        }
        Stmt::DynCall { results, .. } => {
            for v in results {
                defs.insert(v.index);
            }
        }
        Stmt::Intrinsic(intr) => {
            for v in &intr.results {
                defs.insert(v.index);
            }
        }
        _ => {}
    }
}

/// Get all variables used by an expression.
fn expr_uses_vars(expr: &Expr) -> Vec<usize> {
    let mut vars = Vec::new();
    collect_expr_vars(expr, &mut vars);
    vars
}

fn collect_expr_vars(expr: &Expr, vars: &mut Vec<usize>) {
    match expr {
        Expr::Var(v) => vars.push(v.index),
        Expr::Binary(_, a, b) => {
            collect_expr_vars(a, vars);
            collect_expr_vars(b, vars);
        }
        Expr::Unary(_, a) => collect_expr_vars(a, vars),
        Expr::True | Expr::False | Expr::Constant(_) | Expr::Unknown => {}
    }
}

/// Count occurrences of a variable in an expression.
fn count_var_in_expr(expr: &Expr, var_index: usize) -> usize {
    match expr {
        Expr::Var(v) if v.index == var_index => 1,
        Expr::Var(_) => 0,
        Expr::Binary(_, a, b) => count_var_in_expr(a, var_index) + count_var_in_expr(b, var_index),
        Expr::Unary(_, a) => count_var_in_expr(a, var_index),
        Expr::True | Expr::False | Expr::Constant(_) | Expr::Unknown => 0,
    }
}

/// Compute expression complexity.
fn expr_complexity(expr: &Expr) -> usize {
    match expr {
        Expr::True | Expr::False | Expr::Var(_) | Expr::Constant(_) => 1,
        Expr::Unary(_, a) => 1 + expr_complexity(a),
        Expr::Binary(_, a, b) => 1 + expr_complexity(a) + expr_complexity(b),
        Expr::Unknown => 100,
    }
}

/// Check if an expression contains Unknown.
fn expr_contains_unknown(expr: &Expr) -> bool {
    match expr {
        Expr::Unknown => true,
        Expr::Binary(_, a, b) => expr_contains_unknown(a) || expr_contains_unknown(b),
        Expr::Unary(_, a) => expr_contains_unknown(a),
        Expr::Var(_) | Expr::Constant(_) | Expr::True | Expr::False => false,
    }
}

/// Properties of an expression that affect propagation decisions.
#[derive(Debug, Clone, Copy)]
struct ExprProperties {
    complexity: usize,
    contains_unknown: bool,
}

impl ExprProperties {
    fn compute(expr: &Expr) -> Self {
        Self {
            complexity: expr_complexity(expr),
            contains_unknown: expr_contains_unknown(expr),
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ssa::{BinOp, Constant, Subscript, Var};

    fn make_var(index: usize) -> Var {
        Var {
            index,
            subscript: Subscript::None,
        }
    }

    fn make_const(val: u64) -> Expr {
        Expr::Constant(Constant::Felt(val))
    }

    #[test]
    fn test_simple_propagation() {
        // v_0 = 1
        // v_1 = v_0 + 2
        // -> should become v_1 = 1 + 2
        let mut code = vec![
            Stmt::Assign {
                dest: make_var(0),
                expr: make_const(1),
            },
            Stmt::Assign {
                dest: make_var(1),
                expr: Expr::Binary(
                    BinOp::Add,
                    Box::new(Expr::Var(make_var(0))),
                    Box::new(make_const(2)),
                ),
            },
        ];

        propagate_expressions(&mut code);

        // Check that v_0 was propagated into v_1's expression.
        if let Stmt::Assign { expr, .. } = &code[1] {
            if let Expr::Binary(BinOp::Add, left, _) = expr {
                assert!(
                    matches!(left.as_ref(), Expr::Constant(Constant::Felt(1))),
                    "Expected constant 1, got {:?}",
                    left
                );
            } else {
                panic!("Expected binary add");
            }
        } else {
            panic!("Expected assign");
        }
    }

    #[test]
    fn test_no_propagation_into_loop_with_modified_var() {
        // v_0 = 1
        // repeat.4 {
        //   v_0 = v_0 + v_0  // v_0 is modified inside loop
        // }
        // -> v_0 = 1 should NOT be propagated into the loop
        let mut code = vec![
            Stmt::Assign {
                dest: make_var(0),
                expr: make_const(1),
            },
            Stmt::Repeat {
                loop_var: make_var(99),
                loop_count: 4,
                body: vec![Stmt::Assign {
                    dest: make_var(0),
                    expr: Expr::Binary(
                        BinOp::Add,
                        Box::new(Expr::Var(make_var(0))),
                        Box::new(Expr::Var(make_var(0))),
                    ),
                }],
            },
        ];

        let original = code.clone();
        propagate_expressions(&mut code);

        // The loop body should be unchanged.
        assert_eq!(code, original, "Should not propagate into loop");
    }

    #[test]
    fn test_propagation_after_loop() {
        // v_0 = 1
        // repeat.4 { v_1 = v_1 + 1 }  // v_0 not used in loop
        // v_2 = v_0 + 2
        // -> v_0 should be propagated into v_2's expression
        let mut code = vec![
            Stmt::Assign {
                dest: make_var(0),
                expr: make_const(1),
            },
            Stmt::Repeat {
                loop_var: make_var(99),
                loop_count: 4,
                body: vec![Stmt::Assign {
                    dest: make_var(1),
                    expr: Expr::Binary(
                        BinOp::Add,
                        Box::new(Expr::Var(make_var(1))),
                        Box::new(make_const(1)),
                    ),
                }],
            },
            Stmt::Assign {
                dest: make_var(2),
                expr: Expr::Binary(
                    BinOp::Add,
                    Box::new(Expr::Var(make_var(0))),
                    Box::new(make_const(2)),
                ),
            },
        ];

        propagate_expressions(&mut code);

        // Check that v_0 was propagated into v_2's expression.
        if let Stmt::Assign { expr, .. } = &code[2] {
            if let Expr::Binary(BinOp::Add, left, _) = expr {
                assert!(
                    matches!(left.as_ref(), Expr::Constant(Constant::Felt(1))),
                    "Expected constant 1, got {:?}",
                    left
                );
            } else {
                panic!("Expected binary add");
            }
        } else {
            panic!("Expected assign");
        }
    }
}
