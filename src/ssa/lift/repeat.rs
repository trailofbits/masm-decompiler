//! Repeat-loop pattern detection helpers.

use crate::ssa::{BinOp, Constant, Expr, Stmt, Var};

/// Extract a repeat loop count if the block matches the expected pattern.
pub(super) fn extract_repeat_count(code: &[Stmt]) -> Option<usize> {
    let (cond_var, count) = code.iter().find_map(|stmt| match stmt {
        Stmt::Branch(expr) => match_repeat_branch(expr),
        _ => None,
    })?;
    let has_phi = code.iter().any(|stmt| match stmt {
        Stmt::Phi { var, sources } => var == &cond_var && sources.len() == 2,
        _ => false,
    });
    if has_phi { Some(count) } else { None }
}

/// Match the canonical repeat-loop branch condition, if present.
fn match_repeat_branch(expr: &Expr) -> Option<(Var, usize)> {
    match expr {
        Expr::Binary(BinOp::Lt, lhs, rhs) => match (&**lhs, &**rhs) {
            (Expr::Var(v), Expr::Constant(Constant::Felt(n))) => {
                let count = usize::try_from(*n).ok()?;
                Some((v.clone(), count))
            }
            _ => None,
        },
        _ => None,
    }
}
