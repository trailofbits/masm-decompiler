mod common;

use common::decompile;
use masm_decompiler::{frontend::testing::workspace_from_modules, ssa::Stmt};

#[test]
fn decompiles_consuming_repeat_without_unknowns() {
    let ws = workspace_from_modules(&[(
        "consume_repeat",
        r#"
        proc consume_repeat
            push.1
            repeat.2
                add
            end
        end
        "#,
    )]);
    let structured = decompile(&ws, "consume_repeat::consume_repeat", "consume_repeat");
    assert!(!structured.is_empty());
    let (count, body) = first_loop(&structured);
    assert_eq!(count, 2);
    assert!(body.len() <= 3, "loop body should stay compact: {body:#?}");
    assert!(
        defined_indices(body).len() <= count,
        "loop-carried vars should reuse indices: {body:#?}"
    );
}

#[test]
fn decompiles_producing_repeat_without_unknowns() {
    let ws = workspace_from_modules(&[(
        "produce_repeat",
        r#"
        proc produce_repeat
            push.0
            repeat.3
                push.1
            end
            add
            add
            add
        end
        "#,
    )]);
    let structured = decompile(&ws, "produce_repeat::produce_repeat", "produce_repeat");
    assert!(!structured.is_empty());
    let (count, body) = first_loop(&structured);
    assert_eq!(count, 3);
    assert!(body.len() <= 3, "loop body should stay compact: {body:#?}");
    assert!(
        defined_indices(body).len() <= count as usize,
        "loop-carried vars should reuse indices: {body:#?}"
    );
}

fn first_loop(stmts: &[Stmt]) -> (usize, &Vec<Stmt>) {
    for stmt in stmts {
        match stmt {
            Stmt::Repeat {
                loop_count, body, ..
            } => return (*loop_count, body),
            Stmt::While { cond, body } => return (loop_count(cond), body),
            _ => {}
        }
    }
    panic!("expected loop statement; stmts: {stmts:#?}");
}

fn defined_indices(stmts: &[Stmt]) -> std::collections::HashSet<usize> {
    let mut out = std::collections::HashSet::new();
    for stmt in stmts {
        match stmt {
            Stmt::Assign { dest: dst, .. } => {
                out.insert(dst.index);
            }
            Stmt::Phi { var, .. } => {
                out.insert(var.index);
            }
            Stmt::Repeat { body, .. } | Stmt::While { body, .. } => {
                out.extend(defined_indices(body));
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                out.extend(defined_indices(then_body));
                out.extend(defined_indices(else_body));
            }
            _ => {}
        }
    }
    out
}

fn loop_count(cond: &masm_decompiler::ssa::Expr) -> usize {
    if let masm_decompiler::ssa::Expr::Binary(masm_decompiler::ssa::BinOp::Lt, _, rhs) = cond {
        if let masm_decompiler::ssa::Expr::Constant(masm_decompiler::ssa::Constant::Felt(v)) =
            rhs.as_ref()
        {
            return *v as usize;
        }
    }
    panic!("unexpected loop condition expr: {cond:?}");
}
