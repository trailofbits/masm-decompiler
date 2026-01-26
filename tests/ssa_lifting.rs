use masm_decompiler::{
    callgraph::CallGraph,
    cfg::build_cfg_for_proc,
    frontend::testing::workspace_from_modules,
    signature::{ProcSignature, SignatureMap, infer_signatures},
    ssa::{Expr, Stmt, lift::lift_cfg_to_ssa},
};

#[test]
fn lifts_known_instructions() {
    let ws = workspace_from_modules(&[(
        "simple",
        r#"
        proc simple
            push.1
            drop
        end
        "#,
    )]);
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("simple::simple").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    let res = lift_cfg_to_ssa(cfg, "simple", "simple::simple", &sigs).expect("ssa");
    let (inputs, outputs) = sig_inputs_outputs(&sigs, "simple::simple");
    assert_eq!(inputs, 0);
    assert_eq!(outputs, Some(0)); // net effect leaves no values on stack
    let has_assign = res
        .nodes
        .iter()
        .any(|bb| bb.code.iter().any(|s| matches!(s, Stmt::Assign { .. })));
    assert!(has_assign, "cfg: {:?}", res);
    let has_inst = res
        .nodes
        .iter()
        .any(|bb| bb.code.iter().any(|s| matches!(s, Stmt::Inst(_))));
    assert!(!has_inst, "cfg: {:?}", res);
}

#[test]
fn lifts_push_constant_to_assign() {
    let ws = workspace_from_modules(&[(
        "const_push",
        r#"
        proc const_push
            push.5
        end
        "#,
    )]);
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("const_push::const_push").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    let res = lift_cfg_to_ssa(cfg, "const_push", "const_push::const_push", &sigs).expect("ssa");
    let mut has_const = false;
    for bb in res.nodes.iter() {
        if bb.code.iter().any(|s| {
            matches!(
                s,
                Stmt::Assign {
                    expr: Expr::Constant(..),
                    ..
                }
            )
        }) {
            has_const = true;
            break;
        }
    }
    assert!(has_const, "cfg: {:?}", res);
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("dyn::dyn").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    assert!(lift_cfg_to_ssa(cfg, "dyn", "dyn::dyn", &sigs).is_err());
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("caller::caller").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    let res = lift_cfg_to_ssa(cfg, "caller", "caller::caller", &sigs).expect("ssa");
    // callee consumes 1, produces 1
    let (inputs, outputs) = sig_inputs_outputs(&sigs, "caller::caller");
    assert_eq!(inputs, 1);
    assert_eq!(outputs, Some(1));
    assert!(
        res.nodes
            .iter()
            .all(|bb| bb.code.iter().all(|s| !matches!(s, Stmt::Inst(_))))
    );
}

#[test]
fn lifts_cfg_with_phi() {
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("branch::branch").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    let res = lift_cfg_to_ssa(cfg, "branch", "branch::branch", &sigs).expect("ssa");
    // Expect a phi in the join block
    let has_phi = res
        .nodes
        .iter()
        .any(|bb| bb.code.iter().any(|s| matches!(s, Stmt::Phi { .. })));
    assert!(has_phi);
    let (inputs, outputs) = sig_inputs_outputs(&sigs, "branch::branch");
    assert_eq!(inputs, 1); // condition consumed by branch
    assert_eq!(outputs, Some(1));
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("caller::caller").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    assert!(lift_cfg_to_ssa(cfg, "caller", "caller::caller", &sigs).is_err());
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("repeat_only::repeat_only").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    let lifted =
        lift_cfg_to_ssa(cfg, "repeat_only", "repeat_only::repeat_only", &sigs).expect("ssa");

    let has_code = lifted.nodes.iter().any(|bb| !bb.code.is_empty());
    let no_unknowns = lifted
        .nodes
        .iter()
        .all(|bb| bb.code.iter().all(|s| !matches!(s, Stmt::Inst(_))));
    let has_loop = lifted
        .nodes
        .iter()
        .any(|bb| bb.next.iter().any(|e| e.back_edge()));
    assert!(has_code, "all statements eliminated in CFG: {:?}", lifted);
    assert!(
        no_unknowns,
        "unexpected unknowns after lifting: {:?}",
        lifted
    );
    assert!(has_loop, "loop body unrolled in CFG: {:?}", lifted);
}

fn sig_inputs_outputs(sigs: &SignatureMap, name: &str) -> (usize, Option<usize>) {
    match sigs.get(name) {
        Some(ProcSignature::Known {
            inputs, outputs, ..
        }) => (*inputs, Some(*outputs)),
        _ => (0, None),
    }
}
