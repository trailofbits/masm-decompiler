use crate::ssa::{Expr, Stmt, UnOp};

/// Remove empty expr-only side-effect-free statements to simplify structured output.
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
            Stmt::Switch { cases, default, .. } => {
                for (_, body) in cases.iter_mut() {
                    prune_nops(body);
                }
                prune_nops(default);
            }
            Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => {}
            Stmt::While { body, .. } => prune_nops(body),
            _ => {}
        }
        if matches!(&code[i], Stmt::Expr(expr) | Stmt::Branch(expr) if is_side_effect_free(expr)) {
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
            Stmt::For {
                init,
                cond,
                step,
                body,
            } => {
                prune_side_effects(&mut vec![init.as_mut().clone()]);
                prune_side_effects(&mut vec![step.as_mut().clone()]);
                prune_side_effects(body);
                if block_side_effect_free(body) && is_side_effect_free(cond) {
                    code.remove(i);
                    continue;
                }
            }
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
            Stmt::Switch {
                expr,
                cases,
                default,
            } => {
                for (_, body) in cases.iter_mut() {
                    prune_side_effects(body);
                }
                prune_side_effects(default);
                if block_side_effect_free(default)
                    && cases.iter().all(|(_, body)| block_side_effect_free(body))
                    && is_side_effect_free(expr)
                {
                    code.remove(i);
                    continue;
                }
                if let Some(sel) = const_value(expr) {
                    if let Some((_, body)) =
                        cases.iter().find(|(c, _)| const_value_expr(c) == Some(sel))
                    {
                        let body = body.clone();
                        code.remove(i);
                        code.splice(i..i, body);
                        continue;
                    } else if !default.is_empty() {
                        let body = std::mem::take(default);
                        code.remove(i);
                        code.splice(i..i, body);
                        continue;
                    } else {
                        code.remove(i);
                        continue;
                    }
                }
                if cases.iter().all(|(_, body)| body.is_empty())
                    && default.is_empty()
                    && is_side_effect_free(expr)
                {
                    code.remove(i);
                    continue;
                }
            }
            Stmt::While { cond, body } => {
                prune_side_effects(body);
                if block_side_effect_free(body) && is_side_effect_free(cond) {
                    code.remove(i);
                    continue;
                }
            }
            Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => {}
            _ => {}
        }
        i += 1;
    }
}

fn is_side_effect_free(expr: &crate::ssa::Expr) -> bool {
    match expr {
        crate::ssa::Expr::True | crate::ssa::Expr::Constant(_) | crate::ssa::Expr::Var(_) => true,
        crate::ssa::Expr::Unary(_, e) => is_side_effect_free(e),
        crate::ssa::Expr::BinOp(_, a, b) => is_side_effect_free(a) && is_side_effect_free(b),
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

fn const_value(expr: &Expr) -> Option<u64> {
    match expr {
        Expr::Constant(c) => const_value_expr(c),
        Expr::Unary(UnOp::Not, inner) => const_value(inner).map(|v| if v == 0 { 1 } else { 0 }),
        _ => None,
    }
}

fn const_value_expr(c: &crate::ssa::Constant) -> Option<u64> {
    match c {
        crate::ssa::Constant::Felt(v) => Some(*v),
        crate::ssa::Constant::Word(_) | crate::ssa::Constant::Defined(_) => None,
    }
}

fn block_side_effect_free(body: &[Stmt]) -> bool {
    body.iter().all(|s| match s {
        Stmt::Expr(e) | Stmt::Branch(e) => is_side_effect_free(e),
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
        Stmt::Switch {
            expr,
            cases,
            default,
        } => {
            is_side_effect_free(expr)
                && cases.iter().all(|(_, b)| block_side_effect_free(b))
                && block_side_effect_free(default)
        }
        Stmt::For {
            init,
            cond,
            step,
            body,
        } => {
            block_side_effect_free(&[*init.clone(), *step.clone()])
                && is_side_effect_free(cond)
                && block_side_effect_free(body)
        }
        Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => false,
        Stmt::While { cond, body } => is_side_effect_free(cond) && block_side_effect_free(body),
        _ => false,
    })
}
