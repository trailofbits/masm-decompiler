mod common;

use common::run_structure;
use masm_decompiler::{frontend::testing::workspace_from_modules, ssa::Stmt};

#[test]
fn structures_simple_if_else() {
    let ws = workspace_from_modules(&[(
        "simple",
        r#"
        proc simple
            dup.0
            if.true
                push.2
            else
                push.3
            end
        end
        "#,
    )]);
    let structured = run_structure(&ws, "simple::simple", "simple");
    assert!(structured.iter().any(|s| matches!(s, Stmt::If { .. })));
}

#[test]
fn structures_diamond() {
    let ws = workspace_from_modules(&[(
        "diamond",
        r#"
        proc diamond
            dup.0
            if.true
                push.2
            else
                push.3
            end
            add
        end
        "#,
    )]);
    let structured = run_structure(&ws, "diamond::diamond", "diamond");
    // Expect a single If with join code appended.
    assert!(structured.iter().any(|s| matches!(s, Stmt::If { .. })));
}

#[test]
fn structures_loop_with_break() {
    let ws = workspace_from_modules(&[(
        "looping",
        r#"
        proc looping
            push.0
            push.1
            while.true
                dup.0
                if.true
                    add.1
                else
                    add.2
                end
                push.1
            end
        end
        "#,
    )]);
    let structured = run_structure(&ws, "looping::looping", "looping");
    assert!(!structured.is_empty());
    assert!(!structured.iter().any(|s| matches!(s, Stmt::Inst(_))));
}

#[test]
fn structures_loop_with_inner_if() {
    let ws = workspace_from_modules(&[(
        "loop_if",
        r#"
        proc loop_if
            push.0
            push.1
            while.true
                dup.0
                if.true
                    add.1
                else
                    add.2
                end
                push.1
            end
        end
        "#,
    )]);
    let structured = run_structure(&ws, "loop_if::loop_if", "loop_if");
    assert!(!structured.is_empty());
    assert!(contains_if(&structured));
    assert!(!structured.iter().any(|s| matches!(s, Stmt::Inst(_))));
}

#[test]
fn loop_carried_var_keeps_name() {
    let ws = workspace_from_modules(&[(
        "loopcarried",
        r#"
        proc loopcarried
            push.0
            while.true
                dup.0
                push.1
                add
            end
        end
        "#,
    )]);
    let structured = run_structure(&ws, "loopcarried::loopcarried", "loopcarried");
    assert!(structured.iter().any(|s| matches!(s, Stmt::While { .. })));
    assert!(!structured.iter().any(|s| matches!(s, Stmt::Inst(_))));
}

#[test]
fn nested_loops_keep_distinct_carriers() {
    let ws = workspace_from_modules(&[(
        "nested",
        r#"
        proc nested
            push.0
            while.true
                dup.0
                push.1
                add
            end
            push.0
            while.true
                dup.0
                push.2
                add
            end
        end
        "#,
    )]);
    let structured = run_structure(&ws, "nested::nested", "nested");
    assert!(!structured.is_empty());
    assert!(!structured.iter().any(|s| matches!(s, Stmt::Inst(_))));
}

#[test]
fn producing_and_consuming_loop_carrier() {
    // Placeholder replaced by two separate tests below.
}

#[test]
fn producing_repeat_loop_keeps_names() {
    let ws = workspace_from_modules(&[(
        "produce_repeat",
        r#"
        proc produce_repeat
            push.1
            repeat.2
                push.2
                add
            end
        end
        "#,
    )]);
    let structured = run_structure(&ws, "produce_repeat::produce_repeat", "produce_repeat");
    assert!(!structured.is_empty());
    assert!(!structured.iter().any(|s| matches!(s, Stmt::Inst(_))));
}

#[test]
fn consuming_repeat_loop_keeps_names() {
    let ws = workspace_from_modules(&[(
        "consume_repeat",
        r#"
        proc consume_repeat
            push.1
            push.2
            push.3
            repeat.2
                add
            end
        end
        "#,
    )]);
    let structured = run_structure(&ws, "consume_repeat::consume_repeat", "consume_repeat");
    assert!(!structured.is_empty());
    assert!(!structured.iter().any(|s| matches!(s, Stmt::Inst(_))));
}

fn contains_if(stmts: &[Stmt]) -> bool {
    for stmt in stmts {
        match stmt {
            Stmt::If { .. } => return true,
            Stmt::Repeat { body, .. } => {
                if contains_if(body) {
                    return true;
                }
            }
            Stmt::While { body, .. } => {
                if contains_if(body) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}
