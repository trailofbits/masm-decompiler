use crate::ssa::{Expr, Stmt, UnOp};

/// Very small condition simplifier akin to rewasm's condition refinement.
pub fn refine(code: &mut Vec<Stmt>) {
    let mut i = 0;
    while i + 1 < code.len() {
        if let Some(Stmt::If {
            cond,
            then_body,
            else_body,
        }) = code.get(i).cloned()
        {
            // Merge chained identical conditions
            let mut j = i + 1;
            let mut merged = false;
            while j < code.len() {
                if let Some(Stmt::If {
                    cond: other,
                    then_body: t2,
                    else_body: e2,
                }) = code.get(j).cloned()
                {
                    if other == cond {
                        let mut combined = then_body.clone();
                        combined.extend(t2);
                        code.remove(j);
                        code[i] = Stmt::If {
                            cond: cond.clone(),
                            then_body: combined,
                            else_body: else_body.clone(),
                        };
                        merged = true;
                        break;
                    } else if is_opposite(&other, &cond) {
                        let mut then_block = then_body.clone();
                        let mut else_block = else_body.clone();
                        then_block.extend(t2);
                        else_block.extend(e2);
                        code.remove(j);
                        code[i] = Stmt::If {
                            cond: cond.clone(),
                            then_body: then_block,
                            else_body: else_block,
                        };
                        merged = true;
                        break;
                    }
                }
                if !is_side_effect_free(&code[j]) {
                    break;
                }
                j += 1;
            }
            if merged {
                continue;
            }
        }
        i += 1;
    }

    for stmt in code.iter_mut() {
        match stmt {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                refine(then_body);
                refine(else_body);
            }
            Stmt::For {
                init, step, body, ..
            } => {
                refine(&mut vec![init.as_ref().clone()]);
                refine(body);
                refine(&mut vec![step.as_ref().clone()]);
            }
            Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => {}
            Stmt::Switch { cases, default, .. } => {
                for (_, body) in cases {
                    refine(body);
                }
                refine(default);
            }
            Stmt::While { body, .. } => refine(body),
            _ => {}
        }
    }
}

fn is_opposite(a: &Expr, b: &Expr) -> bool {
    matches!(a, Expr::Unary(UnOp::Not, inner) if **inner == *b)
        || matches!(b, Expr::Unary(UnOp::Not, inner) if **inner == *a)
}

fn is_side_effect_free(stmt: &Stmt) -> bool {
    match stmt {
        Stmt::Assign { .. }
        | Stmt::StackOp(_)
        | Stmt::AdvLoad(_)
        | Stmt::AdvStore(_)
        | Stmt::LocalLoad(_)
        | Stmt::LocalStore(_)
        | Stmt::MemLoad(_)
        | Stmt::MemStore(_)
        | Stmt::Call(_)
        | Stmt::Exec(_)
        | Stmt::SysCall(_)
        | Stmt::DynCall { .. }
        | Stmt::Intrinsic(_)
        | Stmt::Instr(_)
        | Stmt::Unknown => false,
        Stmt::Expr(_)
        | Stmt::Branch(_)
        | Stmt::Phi { .. }
        | Stmt::Return(_)
        | Stmt::Nop
        | Stmt::Break
        | Stmt::Continue => true,
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            is_cond_side_effect_free(cond)
                && then_body.iter().all(is_side_effect_free)
                && else_body.iter().all(is_side_effect_free)
        }
        Stmt::Switch {
            expr,
            cases,
            default,
        } => {
            is_cond_side_effect_free(expr)
                && cases
                    .iter()
                    .all(|(_, body)| body.iter().all(is_side_effect_free))
                && default.iter().all(is_side_effect_free)
        }
        Stmt::For {
            init,
            cond,
            step,
            body,
        } => {
            is_side_effect_free(init)
                && is_cond_side_effect_free(cond)
                && is_side_effect_free(step)
                && body.iter().all(is_side_effect_free)
        }
        Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => false,
        Stmt::While { cond, body } => {
            is_cond_side_effect_free(cond) && body.iter().all(is_side_effect_free)
        }
    }
}

fn is_cond_side_effect_free(expr: &Expr) -> bool {
    match expr {
        Expr::Var(_) | Expr::Constant(_) | Expr::True => true,
        Expr::Unary(_, e) => is_cond_side_effect_free(e),
        Expr::BinOp(_, a, b) => is_cond_side_effect_free(a) && is_cond_side_effect_free(b),
        Expr::Unknown => false,
    }
}
