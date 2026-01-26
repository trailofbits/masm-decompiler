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
            // Merge adjacent identical conditions (skip Nop).
            let mut j = i + 1;
            while j < code.len() && matches!(code[j], Stmt::Nop) {
                j += 1;
            }
            if let Some(Stmt::If {
                cond: other,
                then_body: t2,
                else_body: e2,
            }) = code.get(j).cloned()
            {
                if other == cond {
                    let mut combined_then = then_body.clone();
                    combined_then.extend(t2);
                    let mut combined_else = else_body.clone();
                    combined_else.extend(e2);
                    code.remove(j);
                    code[i] = Stmt::If {
                        cond: cond.clone(),
                        then_body: combined_then,
                        else_body: combined_else,
                    };
                    continue;
                } else if is_opposite(&other, &cond) {
                    let mut then_block = then_body.clone();
                    let mut else_block = else_body.clone();
                    then_block.extend(e2);
                    else_block.extend(t2);
                    code.remove(j);
                    code[i] = Stmt::If {
                        cond: cond.clone(),
                        then_body: then_block,
                        else_body: else_block,
                    };
                    continue;
                }
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
            Stmt::Repeat { body, .. } => refine(body),
            Stmt::While { body, .. } => refine(body),
            _ => {}
        }
    }
}

fn is_opposite(a: &Expr, b: &Expr) -> bool {
    matches!(a, Expr::Unary(UnOp::Not, inner) if **inner == *b)
        || matches!(b, Expr::Unary(UnOp::Not, inner) if **inner == *a)
}
