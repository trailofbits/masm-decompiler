use crate::ssa::Stmt;

/// Simplify structured statements: drop empty branches/loops and flatten trivially nested blocks.
pub fn apply(code: &mut Vec<Stmt>) {
    let mut i = 0;
    while i < code.len() {
        if let Stmt::Assign {
            dest: dst,
            expr: crate::ssa::Expr::Var(v),
        } = &code[i]
        {
            if dst == v {
                code.remove(i);
                continue;
            }
        }
        if let Stmt::Phi { var, sources } = &code[i] {
            if sources.iter().all(|s| *s == *var) {
                code.remove(i);
                continue;
            }
            if let Some(first) = sources.first() {
                if sources.iter().all(|s| s == first) {
                    code[i] = Stmt::Assign {
                        dest: var.clone(),
                        expr: crate::ssa::Expr::Var(first.clone()),
                    };
                    continue;
                }
            }
        }
        if matches!(code[i], Stmt::Nop) {
            code.remove(i);
            continue;
        }
        match &mut code[i] {
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                apply(then_body);
                apply(else_body);
                if then_body.is_empty() && else_body.is_empty() {
                    code.remove(i);
                    continue;
                }
                if then_body.is_empty() && !else_body.is_empty() {
                    // if (cond) {} else {E}  => if (!cond) {E}
                    invert_cond(cond);
                    std::mem::swap(then_body, else_body);
                }
                if is_trivially_false(cond) && else_body.is_empty() {
                    code.remove(i);
                    continue;
                }
                if is_trivially_true(cond) && else_body.is_empty() {
                    let mut body = std::mem::take(then_body);
                    code.splice(i..=i, body.drain(..));
                    continue;
                }
                if then_body.len() == 1 {
                    if let Stmt::If { .. } = then_body[0] {
                        // leave nested ifs
                    }
                }
            }
            Stmt::Repeat { body, .. } => {
                apply(body);
                if body.is_empty() {
                    code.remove(i);
                    continue;
                }
            }
            Stmt::While { cond, body } => {
                apply(body);
                if let Some(Stmt::If {
                    cond: guard,
                    then_body,
                    else_body,
                }) = body.first()
                {
                    if else_body.is_empty()
                        && then_body.len() == 1
                        && matches!(then_body[0], Stmt::Break)
                        && is_negation_of(cond, guard)
                    {
                        body.remove(0);
                    }
                }
            }
            _ => {}
        }
        i += 1;
    }
}

fn is_trivially_true(expr: &crate::ssa::Expr) -> bool {
    match expr {
        crate::ssa::Expr::True => true,
        crate::ssa::Expr::Constant(c) => const_truth(c) == Some(true),
        crate::ssa::Expr::Binary(crate::ssa::BinOp::And, a, b) => {
            is_trivially_true(a) && is_trivially_true(b)
        }
        crate::ssa::Expr::Binary(crate::ssa::BinOp::Or, a, b) => {
            is_trivially_true(a) || is_trivially_true(b)
        }
        _ => false,
    }
}

fn is_trivially_false(expr: &crate::ssa::Expr) -> bool {
    match expr {
        crate::ssa::Expr::Constant(c) => const_truth(c) == Some(false),
        crate::ssa::Expr::Binary(crate::ssa::BinOp::And, a, b) => {
            is_trivially_false(a) || is_trivially_false(b)
        }
        crate::ssa::Expr::Binary(crate::ssa::BinOp::Or, a, b) => {
            is_trivially_false(a) && is_trivially_false(b)
        }
        _ => false,
    }
}

fn invert_cond(cond: &mut crate::ssa::Expr) {
    *cond = crate::ssa::Expr::Unary(crate::ssa::UnOp::Not, Box::new(cond.clone()));
}

fn is_negation_of(loop_cond: &crate::ssa::Expr, guard: &crate::ssa::Expr) -> bool {
    matches!(guard, crate::ssa::Expr::Unary(crate::ssa::UnOp::Not, inner) if **inner == *loop_cond)
}

fn const_truth(c: &crate::ssa::Constant) -> Option<bool> {
    match c {
        crate::ssa::Constant::Felt(v) => Some(*v != 0),
        crate::ssa::Constant::Word(w) => Some(w.iter().any(|x| *x != 0)),
        crate::ssa::Constant::Defined(_) => None,
    }
}
