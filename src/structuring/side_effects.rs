use crate::ssa::{Expr, Stmt, UnOp};

/// Remove empty no-op statements to simplify structured output.
pub fn prune_nops(code: &mut Vec<Stmt>) {
    let mut i = 0;
    while i < code.len() {
        match &mut code[i] {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                prune_nops(then_body);
                prune_nops(else_body);
            }
            Stmt::Repeat { body, .. } => prune_nops(body),
            Stmt::While { body, .. } => prune_nops(body),
            _ => {}
        }
        if matches!(&code[i], Stmt::Nop) {
            code.remove(i);
        } else {
            i += 1;
        }
    }
}

/// Drop side-effect-free conditional scaffolding and fold trivial branches.
pub fn prune_side_effects(code: &mut Vec<Stmt>) {
    let mut i = 0;
    while i < code.len() {
        match &mut code[i] {
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                prune_side_effects(then_body);
                prune_side_effects(else_body);
                if block_side_effect_free(then_body)
                    && block_side_effect_free(else_body)
                    && is_side_effect_free(cond)
                {
                    code.remove(i);
                    continue;
                }
                if is_const_true(cond) {
                    let body = std::mem::take(then_body);
                    code.remove(i);
                    code.splice(i..i, body);
                    continue;
                }
                if is_const_false(cond) && block_side_effect_free(then_body) {
                    let body = std::mem::take(else_body);
                    code.remove(i);
                    code.splice(i..i, body);
                    continue;
                }
                if then_body.is_empty() && else_body.is_empty() && is_side_effect_free(cond) {
                    code.remove(i);
                    continue;
                }
            }
            Stmt::While { cond, body } => {
                prune_side_effects(body);
                let _ = cond;
            }
            Stmt::Repeat { body, .. } => prune_side_effects(body),
            _ => {}
        }
        i += 1;
    }
}

fn is_side_effect_free(expr: &crate::ssa::Expr) -> bool {
    match expr {
        crate::ssa::Expr::True | crate::ssa::Expr::Constant(_) | crate::ssa::Expr::Var(_) => true,
        crate::ssa::Expr::Unary(_, e) => is_side_effect_free(e),
        crate::ssa::Expr::Binary(_, a, b) => is_side_effect_free(a) && is_side_effect_free(b),
        crate::ssa::Expr::Unknown => false,
    }
}

fn is_const_true(expr: &Expr) -> bool {
    matches!(expr, Expr::True)
}

fn is_const_false(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(c) if matches!(const_value_expr(c), Some(0)))
        || matches!(expr, Expr::Unary(UnOp::Not, inner) if is_const_true(inner))
}

fn const_value_expr(c: &crate::ssa::Constant) -> Option<u64> {
    match c {
        crate::ssa::Constant::Felt(v) => Some(*v),
        crate::ssa::Constant::Word(_) | crate::ssa::Constant::Defined(_) => None,
    }
}

fn block_side_effect_free(body: &[Stmt]) -> bool {
    body.iter().all(|s| match s {
        Stmt::Nop => true,
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            is_side_effect_free(cond)
                && block_side_effect_free(then_body)
                && block_side_effect_free(else_body)
        }
        Stmt::Repeat { body, .. } => block_side_effect_free(body),
        Stmt::While { cond, body } => is_side_effect_free(cond) && block_side_effect_free(body),
        _ => false,
    })
}
