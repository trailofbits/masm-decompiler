use miden_decompiler::{
    callgraph::CallGraph,
    frontend::testing::workspace_from_modules,
    signature::{ProcSignature, infer_signatures},
};

#[test]
fn infers_produce_and_consume() {
    // proc foo pops 1 (of 2) and pushes 2 new => inputs=2, outputs=2
    let ws = workspace_from_modules(&[(
        "foo",
        r#"
        proc foo
            drop
            dup.0
            dup.1
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.signatures.get("foo::foo").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(inputs.min, 2);
            assert_eq!(outputs.min, 2);
            assert_eq!(outputs.max, Some(2));
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

#[test]
fn infers_consume_only() {
    // proc bar consumes three values => inputs=3, outputs=0
    let ws = workspace_from_modules(&[(
        "bar",
        r#"
        proc bar
            drop drop drop
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.signatures.get("bar::bar").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(inputs.min, 3);
            assert_eq!(outputs.min, 0);
            assert_eq!(outputs.max, Some(0));
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

#[test]
fn infers_produce_only() {
    // proc baz produces three constants => inputs=0, outputs=3
    let ws = workspace_from_modules(&[(
        "baz",
        r#"
        proc baz
            push.1
            push.2
            push.3
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.signatures.get("baz::baz").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(inputs.min, 0);
            assert_eq!(outputs.min, 3);
            assert_eq!(outputs.max, Some(3));
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

#[test]
fn infers_call_chain() {
    // proc mid calls leaf twice; leaf consumes 1 produces 1; second call reuses first result -> consumes 1, produces 1
    let ws = workspace_from_modules(&[
        (
            "leaf",
            r#"
            proc leaf
                drop
                push.1
            end
            "#,
        ),
        (
            "mid",
            r#"
            use leaf::leaf
            proc mid
                exec.leaf::leaf
                exec.leaf::leaf
            end
            "#,
        ),
    ]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let mid = sigs.signatures.get("mid::mid").expect("sig");
    match mid {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(inputs.min, 1);
            assert_eq!(outputs.min, 1);
            assert_eq!(outputs.max, Some(1));
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

#[test]
fn infers_while_no_change() {
    // while loop pops a condition each time; body push/drop nets zero height but missing loop condition drives unbounded inputs.
    let ws = workspace_from_modules(&[(
        "loop",
        r#"
        proc loop
            while.true
                push.1
                drop
            end
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.signatures.get("loop::loop").expect("sig");
    assert!(matches!(sig, ProcSignature::Unknown));
}

#[test]
fn infers_while_producing() {
    // while body pushes a value; the loop condition pop consumes it, so net height is unchanged; requires one input for the initial condition.
    let ws = workspace_from_modules(&[(
        "loop_prod",
        r#"
        proc loop_prod
            while.true
                push.1
            end
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.signatures.get("loop_prod::loop_prod").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(inputs.min, 1);
            assert_eq!(inputs.max, Some(1));
            assert_eq!(outputs.min, 0);
            assert_eq!(outputs.max, Some(0));
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

#[test]
fn infers_while_with_condition_produced() {
    // Loop body pushes a value for the next condition, keeping height constant
    // and providing the needed condition each iteration.
    let ws = workspace_from_modules(&[(
        "loop_cond",
        r#"
        proc loop_cond
            while.true
                push.1      # produce a value
            end
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.signatures.get("loop_cond::loop_cond").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            // Needs one condition input; the body manufactures the next condition.
            assert_eq!(inputs.min, 1);
            assert_eq!(inputs.max, Some(1));
            assert_eq!(outputs.min, 0);
            assert_eq!(outputs.max, Some(0));
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

#[test]
fn infers_while_condition_from_body() {
    // Body manufactures the next condition from existing stack data; net height stays constant.
    let ws = workspace_from_modules(&[(
        "loop_body_cond",
        r#"
        proc loop_body_cond
            while.true
                dup.0       # reuse top value as next condition
            end
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs
        .signatures
        .get("loop_body_cond::loop_body_cond")
        .expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(inputs.min, 2);
            assert_eq!(inputs.max, Some(2));
            assert_eq!(outputs.min, 0);
            assert_eq!(outputs.max, Some(0));
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

#[test]
fn infers_while_consuming() {
    // Seed the condition with a constant; the body drops one argument and does not produce outputs.
    // Iteration count is unknown, so inputs are unbounded above; outputs stay 0. Each iteration also needs a condition value.
    let ws = workspace_from_modules(&[(
        "loop_consume",
        r#"
        proc loop_consume
            push.1
            while.true
                drop
            end
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs
        .signatures
        .get("loop_consume::loop_consume")
        .expect("sig");
    assert!(matches!(sig, ProcSignature::Unknown));
}
