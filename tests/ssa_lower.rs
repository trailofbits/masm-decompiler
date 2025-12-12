use masm_decompiler::{
    callgraph::CallGraph,
    cfg::build_cfg_for_proc,
    frontend::testing::workspace_from_modules,
    signature::infer_signatures,
    ssa::{
        Expr, Stmt,
        lower::{lower_cfg_to_ssa, lower_proc_to_ssa},
    },
};

#[test]
fn lowers_known_instructions() {
    let ws = workspace_from_modules(&[(
        "simple",
        r#"
        proc simple
            push.1
            drop
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("simple::simple").expect("proc");
    let res = lower_proc_to_ssa(proc, "simple", &sigs);
    assert_eq!(res.inputs, 0);
    assert_eq!(res.outputs, 0); // net effect leaves no values on stack
    assert!(matches!(res.code.last(), Some(Stmt::StackOp(_))));
}

#[test]
fn lowers_push_constant_to_assign() {
    let ws = workspace_from_modules(&[(
        "const_push",
        r#"
        proc const_push
            push.5
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("const_push::const_push").expect("proc");
    let res = lower_proc_to_ssa(proc, "const_push", &sigs);
    let has_const = res.code.iter().any(|s| {
        matches!(
            s,
            Stmt::Assign {
                expr: Expr::Constant(..),
                ..
            }
        )
    });
    assert!(has_const, "code: {:?}", res.code);
}

#[test]
fn inserts_exec_unknown_on_dynexec() {
    let ws = workspace_from_modules(&[(
        "dyn",
        r#"
        proc dyn
            dynexec
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("dyn::dyn").expect("proc");
    let res = lower_proc_to_ssa(proc, "dyn", &sigs);
    assert!(res
        .code
        .iter()
        .any(|s| matches!(s, Stmt::DynCall { .. } | Stmt::Unknown)));
}

#[test]
fn uses_signature_for_calls() {
    let ws = workspace_from_modules(&[
        (
            "callee",
            r#"
            proc callee
                drop
                push.1
            end
            "#,
        ),
        (
            "caller",
            r#"
            use callee::callee
            proc caller
                exec.callee::callee
            end
            "#,
        ),
    ]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("caller::caller").expect("proc");
    let res = lower_proc_to_ssa(proc, "caller", &sigs);
    // callee consumes 1, produces 1
    assert_eq!(res.inputs, 1);
    assert_eq!(res.outputs, 1);
    assert!(res.code.iter().all(|s| !matches!(s, Stmt::Unknown)));
}

#[test]
fn lowers_cfg_with_phi() {
    let ws = workspace_from_modules(&[(
        "branch",
        r#"
        proc branch
            if.true
                push.1
            else
                push.2
            end
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("branch::branch").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    let res = lower_cfg_to_ssa(cfg, "branch", "branch::branch", &sigs);
    // Expect a phi in the join block
    let has_phi = res
        .cfg
        .nodes
        .iter()
        .any(|bb| bb.code.iter().any(|s| matches!(s, Stmt::Phi { .. })));
    assert!(has_phi);
    assert_eq!(res.inputs, 1); // condition consumed by branch
    assert_eq!(res.outputs, Some(1));
}

#[test]
fn emits_exec_unknown_for_unknown_call() {
    let ws = workspace_from_modules(&[(
        "caller",
        r#"
        proc caller
            exec.unknown::callee
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("caller::caller").expect("proc");
    let res = lower_proc_to_ssa(proc, "caller", &sigs);
    assert!(res.code.iter().any(|s| matches!(s, Stmt::Unknown)));
}

#[test]
fn repeat_body_not_unrolled() {
    let ws = workspace_from_modules(&[(
        "repeat_only",
        r#"
        proc repeat_only
            repeat.2
                add
            end
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("repeat_only::repeat_only").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    let lowered = lower_cfg_to_ssa(cfg, "repeat_only", "repeat_only::repeat_only", &sigs);

    let has_code = lowered.cfg.nodes.iter().any(|bb| !bb.code.is_empty());
    let no_unknowns = lowered
        .cfg
        .nodes
        .iter()
        .all(|bb| bb.code.iter().all(|s| !matches!(s, Stmt::Unknown)));
    let has_loop = lowered
        .cfg
        .nodes
        .iter()
        .any(|bb| bb.next.iter().any(|e| e.back_edge));
    assert!(
        has_code,
        "all statements eliminated in CFG: {:?}",
        lowered.cfg
    );
    assert!(
        no_unknowns,
        "unexpected unknowns after lowering: {:?}",
        lowered.cfg
    );
    assert!(has_loop, "loop body unrolled in CFG: {:?}", lowered.cfg);
}
