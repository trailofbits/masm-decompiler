use crate::{
    cfg::{Cfg, StmtPos},
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

    let mut todo: Vec<Var> = def_map
        .keys()
        .filter(|var| is_dead(var, use_map, &used_indices))
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
                            if is_dead(&v, use_map, &used_indices) {
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
                        if is_dead(src_var, use_map, &used_indices) {
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
/// 2. Any variable with the same base index is used (subscript-aware liveness).
///
/// The second condition handles loop-produced variables where the definition
/// has a symbolic subscript (e.g., LoopVar) but the uses have concrete subscripts.
fn is_dead(
    var: &Var,
    use_map: &HashMap<Var, HashSet<StmtPos>>,
    used_indices: &HashSet<usize>,
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

    true
}

fn can_remove_expr(expr: &Expr) -> bool {
    match expr {
        Expr::True | Expr::Var(_) | Expr::Constant(_) => true,
        Expr::Unary(_, a) => can_remove_expr(a),
        Expr::Binary(_, a, b) => can_remove_expr(a) && can_remove_expr(b),
        Expr::Unknown => false,
    }
}
