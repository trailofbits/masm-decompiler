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
    // mid calls leaf twice, and leaf consumes 1 produces 1. The second call
    // reuses the first result, so mid consumes 1 input and produces 1 output.
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
    // while loop pops a condition each time and the body has zero effect. The
    // missing loop condition yields unbounded inputs.
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
    // The while body pushes a value and the loop condition pop consumes it, so
    // net height is unchanged. The proc requires one input for the initial
    // condition.
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
fn infers_while_consuming() {
    // Seed the condition with a constant. The body drops one argument and does
    // not produce a new loop condition.
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

#[test]
fn infers_while_with_condition_produced() {
    // Loop body pushes a value for the next condition, keeping the height
    // constant.
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
    // Body manufactures the next condition from existing stack, so the net
    // height stays constant.
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
fn infers_if_same_stack_effect() {
    // Both branches drop one. The result is 2 inputs and 0 outputs.
    let ws = workspace_from_modules(&[(
        "if_same",
        r#"
        proc if_same
            if.true
                drop
            else
                drop
            end
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.signatures.get("if_same::if_same").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            // One condition plus one value dropped in both branches
            assert_eq!(inputs.min, 2);
            assert_eq!(inputs.max, Some(2));
            assert_eq!(outputs.min, 0);
            assert_eq!(outputs.max, Some(0));
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

#[test]
fn infers_if_different_stack_effect() {
    // Branches differ (one drops, one pushes). The signature should be Unknown.
    let ws = workspace_from_modules(&[(
        "if_diff",
        r#"
        proc if_diff
            if.true
                drop
            else
                push.1
            end
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.signatures.get("if_diff::if_diff").expect("sig");
    assert!(matches!(sig, ProcSignature::Unknown));
}
