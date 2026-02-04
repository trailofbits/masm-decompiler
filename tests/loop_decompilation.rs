mod common;

use common::decompile;
use masm_decompiler::{frontend::testing::workspace_from_modules, ir::Stmt};

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
}

fn first_loop(stmts: &[Stmt]) -> (usize, &Vec<Stmt>) {
    for stmt in stmts {
        match stmt {
            Stmt::Repeat {
                loop_count, body, ..
            } => return (*loop_count, body),
            _ => {}
        }
    }
    panic!("expected loop statement; stmts: {stmts:#?}");
}
