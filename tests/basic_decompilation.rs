mod common;

use common::decompile;
use masm_decompiler::{frontend::testing::workspace_from_modules, ir::Stmt};

#[test]
fn decompiles_if_else() {
    let ws = workspace_from_modules(&[(
        "if_else",
        r#"
        proc if_else
            dup.0
            if.true
                push.2
            else
                push.3
            end
        end
        "#,
    )]);
    let stmts = decompile(&ws, "if_else::if_else");
    assert!(contains_if(&stmts, 0));
}

#[test]
fn decompiles_diamond() {
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
    let stmts = decompile(&ws, "diamond::diamond");
    assert!(contains_if(&stmts, 0));
}

#[test]
fn decompiles_while_if() {
    let ws = workspace_from_modules(&[(
        "while_loop",
        r#"
        proc while_loop
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
    let stmts = decompile(&ws, "while_loop::while_loop");
    assert!(contains_while(&stmts, 0));
    assert!(contains_if(&stmts, 1));
}

#[test]
fn decompiles_repeat_loop() {
    let ws = workspace_from_modules(&[(
        "producing_repeat",
        r#"
        proc producing_repeat
            push.1
            repeat.2
                push.2
                add
            end
        end
        "#,
    )]);
    let stmts = decompile(&ws, "producing_repeat::producing_repeat");
    assert!(contains_repeat(&stmts, 0));
}

#[test]
fn decompiles_nested_repeat() {
    let ws = workspace_from_modules(&[(
        "nested_repeat",
        r#"
        proc nested_repeat
            push.1
            push.2
            push.3
            repeat.2
                repeat.2
                    dup
                    add
                end
                add
            end
        end
        "#,
    )]);
    let stmts = decompile(&ws, "nested_repeat::nested_repeat");
    assert!(contains_repeat(&stmts, 0));
    assert!(contains_repeat(&stmts, 1));
}

fn contains_if(stmts: &[Stmt], depth: usize) -> bool {
    for stmt in stmts {
        match stmt {
            Stmt::If { .. } if depth == 0 => return true,
            Stmt::Repeat { body, .. } if depth > 0 => {
                if contains_if(body, depth - 1) {
                    return true;
                }
            }
            Stmt::While { body, .. } if depth > 0 => {
                if contains_if(body, depth - 1) {
                    return true;
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } if depth > 0 => {
                if contains_if(then_body, depth - 1) || contains_if(else_body, depth - 1) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn contains_while(stmts: &[Stmt], depth: usize) -> bool {
    for stmt in stmts {
        match stmt {
            Stmt::While { .. } if depth == 0 => return true,
            Stmt::Repeat { body, .. } if depth > 0 => {
                if contains_while(body, depth - 1) {
                    return true;
                }
            }
            Stmt::While { body, .. } if depth > 0 => {
                if contains_while(body, depth - 1) {
                    return true;
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } if depth > 0 => {
                if contains_while(then_body, depth - 1) || contains_while(else_body, depth - 1) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}

fn contains_repeat(stmts: &[Stmt], depth: usize) -> bool {
    for stmt in stmts {
        match stmt {
            Stmt::Repeat { .. } if depth == 0 => return true,
            Stmt::Repeat { body, .. } if depth > 0 => {
                if contains_repeat(body, depth - 1) {
                    return true;
                }
            }
            Stmt::While { body, .. } if depth > 0 => {
                if contains_repeat(body, depth - 1) {
                    return true;
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } if depth > 0 => {
                if contains_repeat(then_body, depth - 1) || contains_repeat(else_body, depth - 1) {
                    return true;
                }
            }
            _ => {}
        }
    }
    false
}
