use crate::{
    cfg::{Cfg, LoopContext, NodeId, StmtPos},
    ssa::{Expr, Stmt, Var},
};
use std::collections::{HashMap, HashSet};

use super::used_vars::{DefUseMap, UsesVars};

/// Eliminate dead code from the CFG.
///
/// This pass removes assignments and phi nodes whose results are never used.
/// It uses index-based liveness to handle loop-produced variables correctly.
///
/// # Loop Variable Subscripts
///
/// During SSA lifting, loop body variables are defined without subscripts (or with
/// symbolic subscripts like `LoopVar(idx)`), but their uses outside the loop have
/// concrete subscripts (e.g., `Const(0)`, `Const(1)`). For example:
///
/// ```text
/// // Loop body defines: Var { index: 0, subscript: None }
/// // Return uses:       Var { index: 0, subscript: Const(0) },
/// //                    Var { index: 0, subscript: Const(1) }, ...
/// ```
///
/// The def-use map uses exact `Var` matching (including subscript) for expression
/// propagation, but DCE needs to recognize that these are the same logical variable.
/// We handle this by collecting all base indices that have ANY uses, then keeping
/// definitions alive if their base index appears in that set.
///
/// # Consuming Repeat Loops
///
/// Consuming repeat loops (negative stack effect) read from multiple stack positions
/// across iterations using symbolic subscripts. For example, `repeat.4 { add }` reads:
/// - Iteration 0: positions 4 and 3
/// - Iteration 1: positions 3 and 2
/// - Iteration 2: positions 2 and 1
/// - Iteration 3: positions 1 and 0
///
/// The SSA representation uses a single index with symbolic subscripts like `(4-i)`,
/// but all input values at positions 0..entry_depth are semantically used. We keep
/// all variables with birth depth < entry_depth alive for consuming loops.
pub fn eliminate_dead_code(cfg: &mut Cfg, def_use: &mut DefUseMap) {
    let (def_map, use_map) = def_use;

    // Collect base indices of all variables that have at least one use.
    // A variable with index N is considered live if ANY Var with index N is used,
    // regardless of subscript. This handles the subscript mismatch between loop
    // body definitions and their uses outside the loop.
    let used_indices: HashSet<usize> = use_map
        .keys()
        .filter(|var| !use_map.get(*var).map_or(true, |uses| uses.is_empty()))
        .map(|var| var.index)
        .collect();

    // For consuming repeat loops, keep all variables that feed into the loop's
    // entry stack positions alive. These are variables with birth_depth < entry_depth.
    let loop_protected_indices: HashSet<usize> =
        compute_loop_protected_indices(&cfg.var_depths, &cfg.loop_contexts);

    let mut todo: Vec<Var> = def_map
        .keys()
        .filter(|var| is_dead(var, use_map, &used_indices, &loop_protected_indices))
        .cloned()
        .collect();

    while let Some(var) = todo.pop() {
        let Some(pos) = def_map.get(&var) else {
            continue;
        };
        let stmt = cfg.stmt_mut(*pos);
        let mut removed = false;
        match stmt {
            Stmt::Assign { expr, .. } => {
                if can_remove_expr(expr) {
                    for v in expr.uses_vars() {
                        if let Some(uses) = use_map.get_mut(&v) {
                            uses.remove(pos);
                            if is_dead(&v, use_map, &used_indices, &loop_protected_indices) {
                                todo.push(v);
                            }
                        }
                    }
                    *stmt = Stmt::Nop;
                    removed = true;
                }
            }
            Stmt::Phi { sources, .. } => {
                for src_var in sources {
                    if let Some(uses) = use_map.get_mut(src_var) {
                        uses.remove(pos);
                        if is_dead(src_var, use_map, &used_indices, &loop_protected_indices) {
                            todo.push(src_var.clone());
                        }
                    }
                }
                *stmt = Stmt::Nop;
                removed = true;
            }
            _ => {}
        }

        if removed {
            def_map.remove(&var);
        }
    }
}

/// Check if a variable is dead (has no uses).
///
/// A variable is considered live if:
/// 1. It has direct uses (exact match including subscript), OR
/// 2. Any variable with the same base index is used (subscript-aware liveness), OR
/// 3. The variable feeds into a consuming repeat loop (protected by loop context).
///
/// The second condition handles loop-produced variables where the definition
/// has a symbolic subscript (e.g., LoopVar) but the uses have concrete subscripts.
///
/// The third condition handles consuming repeat loops where stack positions are
/// read across multiple iterations via symbolic subscripts.
fn is_dead(
    var: &Var,
    use_map: &HashMap<Var, HashSet<StmtPos>>,
    used_indices: &HashSet<usize>,
    loop_protected_indices: &HashSet<usize>,
) -> bool {
    // Check for direct uses.
    if let Some(uses) = use_map.get(var) {
        if !uses.is_empty() {
            return false;
        }
    }

    // Check if any variable with the same base index is used.
    // This keeps loop body assignments live when their concrete instantiations are used.
    if used_indices.contains(&var.index) {
        return false;
    }

    // Check if this variable feeds into a consuming repeat loop.
    if loop_protected_indices.contains(&var.index) {
        return false;
    }

    true
}

fn can_remove_expr(expr: &Expr) -> bool {
    match expr {
        Expr::True | Expr::False | Expr::Var(_) | Expr::Constant(_) => true,
        Expr::Unary(_, a) => can_remove_expr(a),
        Expr::Binary(_, a, b) => can_remove_expr(a) && can_remove_expr(b),
        Expr::Unknown => false,
    }
}

/// Compute the set of variable indices that should be protected from DCE
/// because they feed into consuming repeat loops.
///
/// For consuming loops (effect_per_iter < 0), all stack positions from 0 to
/// entry_depth-1 are potentially read across the loop's iterations. We identify
/// which variables occupy those positions and protect them from elimination.
fn compute_loop_protected_indices(
    var_depths: &HashMap<usize, usize>,
    loop_contexts: &HashMap<NodeId, LoopContext>,
) -> HashSet<usize> {
    let mut protected = HashSet::new();

    // Find the maximum entry depth across all consuming repeat loops.
    let max_consuming_depth = loop_contexts
        .values()
        .filter(|ctx| ctx.effect_per_iter < 0)
        .map(|ctx| ctx.entry_depth)
        .max()
        .unwrap_or(0);

    if max_consuming_depth == 0 {
        return protected;
    }

    // Protect all variables with birth_depth < max_consuming_depth.
    // These variables occupy stack positions that the consuming loop will read.
    for (&var_index, &birth_depth) in var_depths {
        if birth_depth < max_consuming_depth {
            protected.insert(var_index);
        }
    }

    protected
}
