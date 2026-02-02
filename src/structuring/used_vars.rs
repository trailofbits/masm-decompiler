//! Forward liveness analysis for dead code elimination.
//!
//! This module implements a forward dataflow analysis that tracks which definitions
//! are live (have a subsequent use) and which are dead (redefined or never used).
//!
//! ## Algorithm
//!
//! Walk statements in execution order, tracking "active" definitions (definitions
//! that haven't been used yet). When a variable is used, its active definition(s)
//! become live. When a variable is redefined before being used, the old definition
//! is dead.
//!
//! ## Loop Handling
//!
//! For loops (`repeat` and `while`), a definition inside the loop is live if the
//! variable is used anywhere inside the loop body (since later iterations may use
//! values from earlier iterations).
//!
//! ## Subscript Resolution
//!
//! Variables may have symbolic subscripts like `v_(3-i)` inside repeat loops.
//! These are resolved to concrete values by enumerating all loop variable bindings.

use std::collections::{HashMap, HashSet};

use crate::ssa::{Expr, IndexExpr, Stmt, Subscript, Var};

/// A path identifying a statement's location in the AST.
///
/// Paths are built hierarchically: `[Index(0), Then, Index(2)]` means
/// "top-level statement 0, then-branch, statement 2".
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PathSegment {
    /// Index into a statement list.
    Index(usize),
    /// Inside the then-branch of an if statement.
    Then,
    /// Inside the else-branch of an if statement.
    Else,
    /// Inside a repeat loop body.
    Repeat,
    /// Inside a while loop body.
    While,
}

/// A complete path to a statement.
pub type StmtPath = Vec<PathSegment>;

/// A concrete variable with a resolved subscript value.
///
/// In structured code, variables at different SSA indices may refer to the same
/// logical stack position via their subscript values. For example:
/// - Pre-loop: `Var { index: 5, subscript: Const(1) }` defines v_1
/// - Loop body: `Var { index: 7, subscript: (3-i) }` uses v_1 when i=2
///
/// These have different SSA indices but represent the same logical variable v_1.
/// Therefore, ConcreteVar only stores the subscript value for identity purposes.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ConcreteVar {
    /// Resolved subscript value, or `None` if the variable has no subscript.
    pub subscript: Option<i64>,
}

impl ConcreteVar {
    /// Create a concrete variable from a subscript value.
    pub fn new(subscript: Option<i64>) -> Self {
        Self { subscript }
    }
}

/// Loop variable binding: var_index -> iteration count.
#[derive(Debug, Clone)]
pub struct LoopBinding {
    /// Loop variable index.
    pub var_index: usize,
    /// Number of iterations (0..count).
    pub count: usize,
}

/// Result of liveness analysis.
#[derive(Debug, Clone)]
pub struct LivenessResult {
    /// Paths of statements that are dead (all defined variables are dead).
    pub dead_paths: HashSet<StmtPath>,
}

/// State maintained during forward liveness analysis.
#[derive(Debug, Clone, Default)]
struct LivenessState {
    /// For each variable, the path(s) of its current active definition(s).
    /// Multiple paths occur when definitions come from different control flow branches.
    active_defs: HashMap<ConcreteVar, HashSet<StmtPath>>,
    /// Paths that are known to be live (at least one defined variable was used).
    live_paths: HashSet<StmtPath>,
}

impl LivenessState {
    /// Create a new empty liveness state.
    fn new() -> Self {
        Self::default()
    }

    /// Mark a variable as used, making its active definition(s) live.
    fn mark_used(&mut self, var: &ConcreteVar) {
        if let Some(paths) = self.active_defs.remove(var) {
            self.live_paths.extend(paths);
        }
    }

    /// Add a definition of a variable at the given path.
    /// If there's already an active definition for this variable, it means the variable
    /// was redefined without being used - the old definition is dead (remains in
    /// all_def_paths but won't be added to live_paths).
    fn add_definition(&mut self, var: ConcreteVar, path: StmtPath) {
        // Replace, not add. The old definition (if any) is dead.
        // For branches (if/else), we use merge() which unions the active sets.
        let mut paths = HashSet::new();
        paths.insert(path);
        self.active_defs.insert(var, paths);
    }

    /// Merge another state into this one (union of active definitions and live paths).
    fn merge(&mut self, other: LivenessState) {
        for (var, paths) in other.active_defs {
            self.active_defs.entry(var).or_default().extend(paths);
        }
        self.live_paths.extend(other.live_paths);
    }
}

/// Perform forward liveness analysis on structured statements.
///
/// Returns the set of statement paths that are dead and can be eliminated.
pub fn analyze_liveness(stmts: &[Stmt]) -> LivenessResult {
    let loop_stack: Vec<LoopBinding> = Vec::new();
    let mut path = StmtPath::new();
    let mut all_def_paths: HashSet<StmtPath> = HashSet::new();

    let state = analyze_stmts(stmts, &loop_stack, &mut path, &mut all_def_paths);

    // Any path that defines something but is not in live_paths is dead.
    let dead_paths: HashSet<StmtPath> = all_def_paths
        .difference(&state.live_paths)
        .cloned()
        .collect();

    LivenessResult { dead_paths }
}

/// Analyze a sequence of statements, returning the final liveness state.
fn analyze_stmts(
    stmts: &[Stmt],
    loop_stack: &[LoopBinding],
    path: &mut StmtPath,
    all_def_paths: &mut HashSet<StmtPath>,
) -> LivenessState {
    let mut state = LivenessState::new();

    for (i, stmt) in stmts.iter().enumerate() {
        path.push(PathSegment::Index(i));
        analyze_stmt(stmt, loop_stack, path, &mut state, all_def_paths);
        path.pop();
    }

    state
}

/// Analyze a single statement, updating the liveness state.
fn analyze_stmt(
    stmt: &Stmt,
    loop_stack: &[LoopBinding],
    path: &mut StmtPath,
    state: &mut LivenessState,
    all_def_paths: &mut HashSet<StmtPath>,
) {
    match stmt {
        Stmt::Assign { dest, expr } => {
            // First: process uses (makes definitions live).
            for var in expr_used_vars(expr, loop_stack) {
                state.mark_used(&var);
            }

            // Then: process definition.
            let current_path = path.clone();
            for var in var_defined_vars(dest, loop_stack) {
                state.add_definition(var, current_path.clone());
            }
            all_def_paths.insert(current_path);
        }

        Stmt::Phi { var, sources } => {
            // First: process uses from sources.
            for src in sources {
                for var in var_used_vars(src, loop_stack) {
                    state.mark_used(&var);
                }
            }

            // Then: process definition.
            let current_path = path.clone();
            for v in var_defined_vars(var, loop_stack) {
                state.add_definition(v, current_path.clone());
            }
            all_def_paths.insert(current_path);
        }

        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            // Process uses in condition.
            for var in expr_used_vars(cond, loop_stack) {
                state.mark_used(&var);
            }

            // Analyze both branches starting from the current state.
            // Each branch inherits the current active definitions.
            let then_initial = state.clone();
            let else_initial = state.clone();

            // Analyze then branch.
            path.push(PathSegment::Then);
            let then_state =
                analyze_stmts_with_initial(then_body, loop_stack, path, all_def_paths, then_initial);
            path.pop();

            // Analyze else branch.
            path.push(PathSegment::Else);
            let else_state =
                analyze_stmts_with_initial(else_body, loop_stack, path, all_def_paths, else_initial);
            path.pop();

            // Merge results: active defs are the union (either branch could provide the value).
            // Live paths are also unioned.
            *state = LivenessState::new();
            state.merge(then_state);
            state.merge(else_state);
        }

        Stmt::Repeat {
            loop_var,
            loop_count,
            body,
        } => {
            // For repeat loops: a definition is live if the variable is used
            // anywhere in the loop body (cross-iteration use).
            let mut inner_stack = loop_stack.to_vec();
            inner_stack.push(LoopBinding {
                var_index: loop_var.index,
                count: *loop_count,
            });

            path.push(PathSegment::Repeat);
            analyze_loop_body(body, &inner_stack, path, state, all_def_paths);
            path.pop();
        }

        Stmt::While { cond, body } => {
            // Process uses in condition (condition is evaluated before each iteration).
            for var in expr_used_vars(cond, loop_stack) {
                state.mark_used(&var);
            }

            // For while loops: same as repeat - if defined and used anywhere in body, it's live.
            // No loop binding is pushed since while loops are stack-neutral.
            path.push(PathSegment::While);
            analyze_loop_body(body, loop_stack, path, state, all_def_paths);
            path.pop();
        }

        // Statements that only use variables (no definitions).
        Stmt::Return(vars) => {
            for v in vars {
                for var in var_used_vars(v, loop_stack) {
                    state.mark_used(&var);
                }
            }
        }

        Stmt::MemLoad(load) => {
            // Uses: address.
            for v in &load.address {
                for var in var_used_vars(v, loop_stack) {
                    state.mark_used(&var);
                }
            }
            // Defines: outputs. MemLoad has side effects, so we don't track for elimination.
        }

        Stmt::MemStore(store) => {
            for v in &store.address {
                for var in var_used_vars(v, loop_stack) {
                    state.mark_used(&var);
                }
            }
            for v in &store.values {
                for var in var_used_vars(v, loop_stack) {
                    state.mark_used(&var);
                }
            }
        }

        Stmt::AdvLoad(_) => {
            // No uses, defines outputs. Side-effectful.
        }

        Stmt::AdvStore(store) => {
            for v in &store.values {
                for var in var_used_vars(v, loop_stack) {
                    state.mark_used(&var);
                }
            }
        }

        Stmt::LocalLoad(_) => {
            // No uses, defines outputs. Side-effectful.
        }

        Stmt::LocalStore(store) => {
            for v in &store.values {
                for var in var_used_vars(v, loop_stack) {
                    state.mark_used(&var);
                }
            }
        }

        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in &call.args {
                for var in var_used_vars(v, loop_stack) {
                    state.mark_used(&var);
                }
            }
            // Results are defined but calls have side effects, not tracked for elimination.
        }

        Stmt::DynCall { args, .. } => {
            for v in args {
                for var in var_used_vars(v, loop_stack) {
                    state.mark_used(&var);
                }
            }
        }

        Stmt::Intrinsic(intr) => {
            for v in &intr.args {
                for var in var_used_vars(v, loop_stack) {
                    state.mark_used(&var);
                }
            }
            // Results are defined but intrinsics have side effects.
        }

        // These statement types are removed before/during flattening or are no-ops.
        Stmt::IfBranch(_)
        | Stmt::WhileBranch(_)
        | Stmt::RepeatBranch(_)
        | Stmt::Inst(_)
        | Stmt::Nop => {}
    }
}

/// Analyze statements with an initial state (used for branches).
fn analyze_stmts_with_initial(
    stmts: &[Stmt],
    loop_stack: &[LoopBinding],
    path: &mut StmtPath,
    all_def_paths: &mut HashSet<StmtPath>,
    mut state: LivenessState,
) -> LivenessState {
    for (i, stmt) in stmts.iter().enumerate() {
        path.push(PathSegment::Index(i));
        analyze_stmt(stmt, loop_stack, path, &mut state, all_def_paths);
        path.pop();
    }
    state
}

/// Analyze a loop body with special handling for cross-iteration uses.
///
/// For loops, a definition is live if the variable is used anywhere in the loop body,
/// because later iterations may use values from earlier iterations.
fn analyze_loop_body(
    body: &[Stmt],
    loop_stack: &[LoopBinding],
    path: &mut StmtPath,
    state: &mut LivenessState,
    all_def_paths: &mut HashSet<StmtPath>,
) {
    // Collect all definitions and uses in the loop body.
    let (body_defs, body_uses) = collect_loop_defs_uses(body, loop_stack, path);

    // Register all definition paths.
    for (def_path, _) in &body_defs {
        all_def_paths.insert(def_path.clone());
    }

    // A definition in the loop is live if its variable is used anywhere in the loop.
    let mut loop_live_paths: HashSet<StmtPath> = HashSet::new();
    let mut remaining_defs: HashMap<ConcreteVar, HashSet<StmtPath>> = HashMap::new();

    for (def_path, def_var) in body_defs {
        if body_uses.contains(&def_var) {
            // Used inside the loop - definitely live.
            loop_live_paths.insert(def_path);
        } else {
            // Not used inside the loop, but might be used after.
            // Add to active definitions for post-loop uses.
            remaining_defs
                .entry(def_var)
                .or_default()
                .insert(def_path);
        }
    }

    // Uses in the loop body also consume definitions from before the loop.
    for use_var in &body_uses {
        state.mark_used(use_var);
    }

    // Add remaining definitions (not used in loop) to the state.
    // These might be used after the loop.
    for (var, paths) in remaining_defs {
        state.active_defs.entry(var).or_default().extend(paths);
    }

    // Add loop-internal live paths to the state.
    state.live_paths.extend(loop_live_paths);
}

/// Collect all definitions and uses in a loop body.
fn collect_loop_defs_uses(
    stmts: &[Stmt],
    loop_stack: &[LoopBinding],
    base_path: &StmtPath,
) -> (Vec<(StmtPath, ConcreteVar)>, HashSet<ConcreteVar>) {
    let mut defs: Vec<(StmtPath, ConcreteVar)> = Vec::new();
    let mut uses: HashSet<ConcreteVar> = HashSet::new();

    collect_defs_uses_recursive(stmts, loop_stack, base_path, &mut defs, &mut uses);

    (defs, uses)
}

/// Recursively collect definitions and uses from statements.
fn collect_defs_uses_recursive(
    stmts: &[Stmt],
    loop_stack: &[LoopBinding],
    base_path: &StmtPath,
    defs: &mut Vec<(StmtPath, ConcreteVar)>,
    uses: &mut HashSet<ConcreteVar>,
) {
    for (i, stmt) in stmts.iter().enumerate() {
        let mut path = base_path.clone();
        path.push(PathSegment::Index(i));

        match stmt {
            Stmt::Assign { dest, expr } => {
                uses.extend(expr_used_vars(expr, loop_stack));
                for var in var_defined_vars(dest, loop_stack) {
                    defs.push((path.clone(), var));
                }
            }

            Stmt::Phi { var, sources } => {
                for src in sources {
                    uses.extend(var_used_vars(src, loop_stack));
                }
                for v in var_defined_vars(var, loop_stack) {
                    defs.push((path.clone(), v));
                }
            }

            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                uses.extend(expr_used_vars(cond, loop_stack));

                let mut then_path = path.clone();
                then_path.push(PathSegment::Then);
                collect_defs_uses_recursive(then_body, loop_stack, &then_path, defs, uses);

                let mut else_path = path.clone();
                else_path.push(PathSegment::Else);
                collect_defs_uses_recursive(else_body, loop_stack, &else_path, defs, uses);
            }

            Stmt::Repeat {
                loop_var,
                loop_count,
                body,
            } => {
                let mut inner_stack = loop_stack.to_vec();
                inner_stack.push(LoopBinding {
                    var_index: loop_var.index,
                    count: *loop_count,
                });

                let mut repeat_path = path.clone();
                repeat_path.push(PathSegment::Repeat);
                collect_defs_uses_recursive(body, &inner_stack, &repeat_path, defs, uses);
            }

            Stmt::While { cond, body } => {
                uses.extend(expr_used_vars(cond, loop_stack));

                let mut while_path = path.clone();
                while_path.push(PathSegment::While);
                collect_defs_uses_recursive(body, loop_stack, &while_path, defs, uses);
            }

            Stmt::Return(vars) => {
                for v in vars {
                    uses.extend(var_used_vars(v, loop_stack));
                }
            }

            Stmt::MemLoad(load) => {
                for v in &load.address {
                    uses.extend(var_used_vars(v, loop_stack));
                }
            }

            Stmt::MemStore(store) => {
                for v in &store.address {
                    uses.extend(var_used_vars(v, loop_stack));
                }
                for v in &store.values {
                    uses.extend(var_used_vars(v, loop_stack));
                }
            }

            Stmt::AdvStore(store) => {
                for v in &store.values {
                    uses.extend(var_used_vars(v, loop_stack));
                }
            }

            Stmt::LocalStore(store) => {
                for v in &store.values {
                    uses.extend(var_used_vars(v, loop_stack));
                }
            }

            Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
                for v in &call.args {
                    uses.extend(var_used_vars(v, loop_stack));
                }
            }

            Stmt::DynCall { args, .. } => {
                for v in args {
                    uses.extend(var_used_vars(v, loop_stack));
                }
            }

            Stmt::Intrinsic(intr) => {
                for v in &intr.args {
                    uses.extend(var_used_vars(v, loop_stack));
                }
            }

            Stmt::AdvLoad(_) | Stmt::LocalLoad(_) => {
                // No uses (defines outputs but those are side-effectful).
            }

            Stmt::IfBranch(_)
            | Stmt::WhileBranch(_)
            | Stmt::RepeatBranch(_)
            | Stmt::Inst(_)
            | Stmt::Nop => {}
        }
    }
}

/// Get concrete variables used by an expression.
fn expr_used_vars(expr: &Expr, loop_stack: &[LoopBinding]) -> Vec<ConcreteVar> {
    match expr {
        Expr::Var(v) => expand_var(v, loop_stack),
        Expr::Binary(_, lhs, rhs) => {
            let mut result = expr_used_vars(lhs, loop_stack);
            result.extend(expr_used_vars(rhs, loop_stack));
            result
        }
        Expr::Unary(_, inner) => expr_used_vars(inner, loop_stack),
        Expr::Constant(_) | Expr::True | Expr::False | Expr::Unknown => Vec::new(),
    }
}

/// Get concrete variables used by a variable reference.
fn var_used_vars(var: &Var, loop_stack: &[LoopBinding]) -> Vec<ConcreteVar> {
    expand_var(var, loop_stack)
}

/// Get concrete variables defined by a variable.
fn var_defined_vars(var: &Var, loop_stack: &[LoopBinding]) -> Vec<ConcreteVar> {
    expand_var(var, loop_stack)
}

/// Expand a variable with potentially symbolic subscript to all concrete instances.
///
/// For a variable `v_(3 - i)` inside a `repeat.4` loop with loop variable i,
/// this returns `[v_3, v_2, v_1, v_0]` corresponding to `i = 0, 1, 2, 3`.
fn expand_var(var: &Var, loop_stack: &[LoopBinding]) -> Vec<ConcreteVar> {
    match &var.subscript {
        Subscript::None => {
            // No subscript - single concrete variable.
            vec![ConcreteVar::new(None)]
        }
        Subscript::Expr(expr) => {
            // Enumerate all combinations of loop variable values.
            let mut result = Vec::new();
            enumerate_all_values(loop_stack, &mut Vec::new(), &mut |bindings| {
                if let Some(val) = eval_index_expr(expr, bindings) {
                    result.push(ConcreteVar::new(Some(val)));
                }
            });
            result
        }
    }
}

/// Enumerate all combinations of loop variable values.
fn enumerate_all_values(
    remaining_stack: &[LoopBinding],
    current_bindings: &mut Vec<(usize, i64)>,
    callback: &mut impl FnMut(&[(usize, i64)]),
) {
    if remaining_stack.is_empty() {
        callback(current_bindings);
        return;
    }
    let first = &remaining_stack[0];
    let rest = &remaining_stack[1..];

    for v in 0..first.count {
        current_bindings.push((first.var_index, v as i64));
        enumerate_all_values(rest, current_bindings, callback);
        current_bindings.pop();
    }
}

/// Evaluate an index expression with known loop variable values.
///
/// Returns `None` if the expression contains unbound loop variables.
fn eval_index_expr(expr: &IndexExpr, bindings: &[(usize, i64)]) -> Option<i64> {
    match expr {
        IndexExpr::Const(c) => Some(*c),
        IndexExpr::LoopVar(i) => bindings.iter().find(|(j, _)| i == j).map(|(_, v)| *v),
        IndexExpr::Add(lhs, rhs) => {
            let l = eval_index_expr(lhs, bindings)?;
            let r = eval_index_expr(rhs, bindings)?;
            Some(l + r)
        }
        IndexExpr::Mul(lhs, rhs) => {
            let l = eval_index_expr(lhs, bindings)?;
            let r = eval_index_expr(rhs, bindings)?;
            Some(l * r)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ssa::{BinOp, Constant};

    fn var_with_subscript(index: usize, sub: i64) -> Var {
        Var {
            index,
            subscript: Subscript::Expr(IndexExpr::Const(sub)),
        }
    }

    fn path(segments: &[usize]) -> StmtPath {
        segments.iter().map(|&i| PathSegment::Index(i)).collect()
    }

    #[test]
    fn test_simple_dead_assign() {
        // v_0 = 1;  // DEAD - never used
        // v_1 = 2;  // LIVE
        // return v_1;
        let stmts = vec![
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(1)),
            },
            Stmt::Assign {
                dest: var_with_subscript(1, 1),
                expr: Expr::Constant(Constant::Felt(2)),
            },
            Stmt::Return(vec![var_with_subscript(1, 1)]),
        ];

        let result = analyze_liveness(&stmts);

        assert!(result.dead_paths.contains(&path(&[0])));
        assert!(!result.dead_paths.contains(&path(&[1])));
    }

    #[test]
    fn test_redefinition_kills_previous() {
        // v_0 = 1;  // DEAD - redefined before use
        // v_0 = 2;  // LIVE
        // return v_0;
        let stmts = vec![
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(1)),
            },
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(2)),
            },
            Stmt::Return(vec![var_with_subscript(0, 0)]),
        ];

        let result = analyze_liveness(&stmts);

        assert!(result.dead_paths.contains(&path(&[0])));
        assert!(!result.dead_paths.contains(&path(&[1])));
    }

    #[test]
    fn test_use_before_redefine() {
        // v_0 = 1;  // LIVE - used before redefinition
        // v_1 = v_0 + 1;  // LIVE
        // v_0 = 2;  // DEAD - never used after
        // return v_1;
        let stmts = vec![
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(1)),
            },
            Stmt::Assign {
                dest: var_with_subscript(1, 1),
                expr: Expr::Binary(
                    BinOp::Add,
                    Box::new(Expr::Var(var_with_subscript(0, 0))),
                    Box::new(Expr::Constant(Constant::Felt(1))),
                ),
            },
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(2)),
            },
            Stmt::Return(vec![var_with_subscript(1, 1)]),
        ];

        let result = analyze_liveness(&stmts);

        assert!(!result.dead_paths.contains(&path(&[0]))); // v_0 = 1 is live
        assert!(!result.dead_paths.contains(&path(&[1]))); // v_1 = ... is live
        assert!(result.dead_paths.contains(&path(&[2]))); // v_0 = 2 is dead
    }

    #[test]
    fn test_chain_of_dead() {
        // v_0 = 1;        // DEAD (v_1 is dead, so this becomes dead too after iteration)
        // v_1 = v_0 + 1;  // DEAD
        // v_2 = 3;        // LIVE
        // return v_2;
        let stmts = vec![
            Stmt::Assign {
                dest: var_with_subscript(0, 0),
                expr: Expr::Constant(Constant::Felt(1)),
            },
            Stmt::Assign {
                dest: var_with_subscript(1, 1),
                expr: Expr::Binary(
                    BinOp::Add,
                    Box::new(Expr::Var(var_with_subscript(0, 0))),
                    Box::new(Expr::Constant(Constant::Felt(1))),
                ),
            },
            Stmt::Assign {
                dest: var_with_subscript(2, 2),
                expr: Expr::Constant(Constant::Felt(3)),
            },
            Stmt::Return(vec![var_with_subscript(2, 2)]),
        ];

        let result = analyze_liveness(&stmts);

        // After one pass, v_1 is dead but v_0 appears used.
        // The DCE iteration will handle the chain.
        assert!(result.dead_paths.contains(&path(&[1]))); // v_1 = ... is dead
        assert!(!result.dead_paths.contains(&path(&[2]))); // v_2 = 3 is live
    }

    #[test]
    fn test_if_both_branches_define() {
        // if cond {
        //   v_0 = 1;  // LIVE (used after if)
        // } else {
        //   v_0 = 2;  // LIVE (used after if)
        // }
        // return v_0;
        let stmts = vec![
            Stmt::If {
                cond: Expr::True,
                then_body: vec![Stmt::Assign {
                    dest: var_with_subscript(0, 0),
                    expr: Expr::Constant(Constant::Felt(1)),
                }],
                else_body: vec![Stmt::Assign {
                    dest: var_with_subscript(0, 0),
                    expr: Expr::Constant(Constant::Felt(2)),
                }],
            },
            Stmt::Return(vec![var_with_subscript(0, 0)]),
        ];

        let result = analyze_liveness(&stmts);

        // Both definitions should be live.
        let then_path = vec![PathSegment::Index(0), PathSegment::Then, PathSegment::Index(0)];
        let else_path = vec![PathSegment::Index(0), PathSegment::Else, PathSegment::Index(0)];

        assert!(!result.dead_paths.contains(&then_path));
        assert!(!result.dead_paths.contains(&else_path));
    }

    #[test]
    fn test_if_one_branch_dead() {
        // v_0 = 1;  // LIVE (used after if via else path)
        // if cond {
        //   v_0 = 2;  // DEAD (redefined in else, and else's v_0 is used)
        // } else {
        //   // uses inherited v_0
        // }
        // Actually this is tricky - both paths to the return use v_0.
        // Let me make a clearer test.
        //
        // if cond {
        //   v_0 = 1;  // DEAD - v_1 is what's returned
        // } else {
        //   v_1 = 2;  // LIVE
        // }
        // return v_1;
        let stmts = vec![
            Stmt::If {
                cond: Expr::True,
                then_body: vec![Stmt::Assign {
                    dest: var_with_subscript(0, 0),
                    expr: Expr::Constant(Constant::Felt(1)),
                }],
                else_body: vec![Stmt::Assign {
                    dest: var_with_subscript(1, 1),
                    expr: Expr::Constant(Constant::Felt(2)),
                }],
            },
            Stmt::Return(vec![var_with_subscript(1, 1)]),
        ];

        let result = analyze_liveness(&stmts);

        let then_path = vec![PathSegment::Index(0), PathSegment::Then, PathSegment::Index(0)];
        let else_path = vec![PathSegment::Index(0), PathSegment::Else, PathSegment::Index(0)];

        assert!(result.dead_paths.contains(&then_path)); // v_0 = 1 is dead
        assert!(!result.dead_paths.contains(&else_path)); // v_1 = 2 is live
    }

    #[test]
    fn test_loop_cross_iteration_use() {
        // repeat.4 {
        //   v_(3-i) = v_(4-i);  // Reads from "previous" subscript
        // }
        // The assignments should be live because v_(4-i) in iteration 1 reads v_3
        // which was defined in iteration 0.

        let loop_var = Var::new(100);

        // dest = v_(3-i), src = v_(4-i)
        let dest_subscript = IndexExpr::Add(
            Box::new(IndexExpr::Const(3)),
            Box::new(IndexExpr::Mul(
                Box::new(IndexExpr::Const(-1)),
                Box::new(IndexExpr::LoopVar(100)),
            )),
        );
        let src_subscript = IndexExpr::Add(
            Box::new(IndexExpr::Const(4)),
            Box::new(IndexExpr::Mul(
                Box::new(IndexExpr::Const(-1)),
                Box::new(IndexExpr::LoopVar(100)),
            )),
        );

        let stmts = vec![Stmt::Repeat {
            loop_var,
            loop_count: 4,
            body: vec![Stmt::Assign {
                dest: Var {
                    index: 0,
                    subscript: Subscript::Expr(dest_subscript),
                },
                expr: Expr::Var(Var {
                    index: 0,
                    subscript: Subscript::Expr(src_subscript),
                }),
            }],
        }];

        let result = analyze_liveness(&stmts);

        // The assignment inside the loop should be live because:
        // - It defines v_3, v_2, v_1, v_0
        // - It uses v_4, v_3, v_2, v_1
        // - v_3, v_2, v_1 are both defined and used in the loop
        let assign_path = vec![
            PathSegment::Index(0),
            PathSegment::Repeat,
            PathSegment::Index(0),
        ];
        assert!(!result.dead_paths.contains(&assign_path));
    }

    #[test]
    fn test_loop_def_used_after() {
        // repeat.4 {
        //   v_(3-i) = const;  // Defines v_3, v_2, v_1, v_0
        // }
        // return v_0;  // Uses v_0 from the last iteration

        let loop_var = Var::new(100);
        let subscript_expr = IndexExpr::Add(
            Box::new(IndexExpr::Const(3)),
            Box::new(IndexExpr::Mul(
                Box::new(IndexExpr::Const(-1)),
                Box::new(IndexExpr::LoopVar(100)),
            )),
        );

        let stmts = vec![
            Stmt::Repeat {
                loop_var,
                loop_count: 4,
                body: vec![Stmt::Assign {
                    dest: Var {
                        index: 0,
                        subscript: Subscript::Expr(subscript_expr),
                    },
                    expr: Expr::Constant(Constant::Felt(42)),
                }],
            },
            Stmt::Return(vec![var_with_subscript(0, 0)]),
        ];

        let result = analyze_liveness(&stmts);

        // The assignment should be live because v_0 is used after the loop.
        let assign_path = vec![
            PathSegment::Index(0),
            PathSegment::Repeat,
            PathSegment::Index(0),
        ];
        assert!(!result.dead_paths.contains(&assign_path));
    }
}
