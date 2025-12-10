use crate::ssa::Stmt;

/// Simplify structured statements: drop empty branches/loops and flatten trivially nested blocks.
pub fn apply(code: &mut Vec<Stmt>) {
    let mut i = 0;
    while i < code.len() {
        if matches!(code[i], Stmt::Nop) {
            code.remove(i);
            continue;
        }
        match &mut code[i] {
            Stmt::If { cond, then_body, else_body } => {
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
                if then_body.len() == 1 {
                    if let Stmt::If { .. } = then_body[0] {
                        // leave nested ifs
                    }
                }
            }
            Stmt::Switch { expr: _, cases, default } => {
                for (_, body) in cases.iter_mut() {
                    apply(body);
                }
                apply(default);
                // Drop empty cases/default if everything is empty.
                if cases.iter().all(|(_, body)| body.is_empty()) && default.is_empty() {
                    code.remove(i);
                    continue;
                }
            }
            Stmt::While { cond: _, body } => {
                apply(body);
                if body.is_empty() {
                    code.remove(i);
                    continue;
                }
                if body.len() == 1 && matches!(body[0], Stmt::Break | Stmt::Continue) {
                    // Loop immediately breaks; drop it.
                    code.remove(i);
                    continue;
                }
            }
            _ => {}
        }
        i += 1;
    }
}

fn invert_cond(cond: &mut crate::ssa::Expr) {
    *cond = crate::ssa::Expr::Unary(crate::ssa::UnOp::Not, Box::new(cond.clone()));
}
