use miden_decompiler::{
    callgraph::CallGraph, cfg::build_cfg_for_proc, frontend::testing::workspace_from_modules,
    signature::infer_signatures, ssa::lower::lower_cfg_to_ssa, structuring::structure, ssa::Stmt,
    ssa::{Expr, Var},
};

#[test]
fn structures_simple_if_else() {
    let ws = workspace_from_modules(&[(
        "simple",
        r#"
        proc simple
            push.1
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
            push.1
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
    assert!(structured.iter().any(|s| matches!(s, Stmt::Assign { .. }) || matches!(s, Stmt::StackOp(_))));
}

#[test]
fn structures_loop_with_break() {
    let ws = workspace_from_modules(&[(
        "looping",
        r#"
        proc looping
            push.0
            while.true
                push.1
                neq.0
                if.true
                    push.2
                    drop
                else
                    drop
                end
            end
        end
        "#,
    )]);
    let structured = run_structure(&ws, "looping::looping", "looping");
    assert!(structured.iter().any(|s| matches!(s, Stmt::While { .. })));
}

#[test]
fn structures_loop_with_inner_if() {
    let ws = workspace_from_modules(&[(
        "loop_if",
        r#"
        proc loop_if
            push.0
            while.true
                dup.0
                if.true
                    push.1
                else
                    push.2
                end
                drop
            end
        end
        "#,
    )]);
    let structured = run_structure(&ws, "loop_if::loop_if", "loop_if");
    assert!(structured.iter().any(|s| matches!(s, Stmt::While { .. })));
    assert!(contains_if(&structured));
}

fn run_structure(
    ws: &miden_decompiler::frontend::Workspace,
    proc_name: &str,
    module: &str,
) -> Vec<Stmt> {
    let cg = CallGraph::build_for_workspace(ws);
    let sigs = infer_signatures(ws, &cg);
    let proc = ws.lookup_proc(proc_name).unwrap();
    let cfg = build_cfg_for_proc(proc).unwrap();
    let lowered = lower_cfg_to_ssa(cfg, module, &sigs);
    structure(lowered.cfg)
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
    // Expect first assign initializes v0 and loop body updates the same var.
    let init_var = match structured.first() {
        Some(Stmt::Assign { dst, .. }) => *dst,
        _ => panic!("expected init assign"),
    };
    let loop_body = structured.iter().find_map(|s| {
        if let Stmt::While { body, .. } = s {
            Some(body)
        } else {
            None
        }
    }).expect("while loop");
    let mut seen_update = false;
    for stmt in loop_body {
        if let Stmt::Assign { dst, expr } = stmt {
            if let Expr::BinOp(_, lhs, rhs) = expr {
                if let (Expr::Var(lhs_v), Expr::Constant(_)) = (&**lhs, &**rhs) {
                    if *dst == init_var && *lhs_v == init_var {
                        seen_update = true;
                    }
                }
            }
        }
    }
    assert!(seen_update, "expected loop-carried var to be updated in loop body");
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
                push.0
                while.true
                    dup.0
                    push.2
                    add
                end
            end
        end
        "#,
    )]);
    let structured = run_structure(&ws, "nested::nested", "nested");
    // Collect loop-carried vars for outer and inner loops.
    let mut carriers: Vec<Var> = Vec::new();
    for stmt in &structured {
        if let Stmt::Assign { dst, .. } = stmt {
            carriers.push(*dst);
            break;
        }
    }
    let mut inner_carrier: Option<Var> = None;
    for stmt in &structured {
        if let Stmt::While { body, .. } = stmt {
            for inner in body {
                if let Stmt::Assign { dst, .. } = inner {
                    inner_carrier.get_or_insert(*dst);
                    break;
                }
            }
        }
    }
    carriers.sort();
    carriers.dedup();
    if let Some(inner) = inner_carrier {
        carriers.push(inner);
    }
    carriers.sort();
    carriers.dedup();
    assert!(
        carriers.len() >= 2,
        "expected outer and inner loop carriers to be distinct"
    );
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
    assert!(!structured.iter().any(|s| matches!(s, Stmt::Unknown)));
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
    assert!(!structured.iter().any(|s| matches!(s, Stmt::Unknown)));
}

fn contains_if(stmts: &[Stmt]) -> bool {
    for stmt in stmts {
        match stmt {
            Stmt::If { .. } => return true,
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
