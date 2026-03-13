mod common;

use common::strategies::{
    consuming_instruction_strategy, neutral_instruction_strategy, producing_instruction_strategy,
};
use masm_decompiler::{
    callgraph::CallGraph,
    frontend::testing::workspace_from_modules,
    signature::{ProcSignature, StackEffect, infer_signatures},
};
use miden_assembly_syntax::{ast::Instruction, prettier::PrettyPrint};
use proptest::prelude::*;

// ============================================================================
// Unit Tests - Basic signature inference
// ============================================================================

#[test]
fn infers_produce_and_consume() {
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("foo::foo").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(*inputs, 2);
            assert_eq!(*outputs, 2);
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("bar::bar").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(*inputs, 3);
            assert_eq!(*outputs, 0);
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("baz::baz").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(*inputs, 0);
            assert_eq!(*outputs, 3);
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

#[test]
fn infers_word_memory_and_stack_op_signatures() {
    let ws = workspace_from_modules(&[(
        "word_mem_stack_ops",
        include_str!("fixtures/word_mem_stack_ops.masm"),
    )]);
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);

    for proc_name in [
        "word_mem_stack_ops::uses_movupw",
        "word_mem_stack_ops::uses_loc_loadw_be",
        "word_mem_stack_ops::uses_loc_loadw_le",
        "word_mem_stack_ops::uses_loc_load_and_store",
        "word_mem_stack_ops::uses_mem_loadw_and_storew_be",
        "word_mem_stack_ops::uses_mem_loadw_and_storew_le",
        "word_mem_stack_ops::uses_mem_load_and_store",
        "word_mem_stack_ops::uses_swapdw",
        "word_mem_stack_ops::uses_locaddr",
        "word_mem_stack_ops::uses_u32wrapping_add3",
        "word_mem_stack_ops::uses_u32widening_add3",
        "word_mem_stack_ops::uses_u32shift_imm",
        "word_mem_stack_ops::uses_u32shift_binary",
        "word_mem_stack_ops::uses_sdepth",
        "word_mem_stack_ops::uses_movdnw2",
        "word_mem_stack_ops::uses_movdnw3",
        "word_mem_stack_ops::uses_horner_eval_base",
        "word_mem_stack_ops::uses_horner_eval_ext",
    ] {
        let sig = sigs
            .get(proc_name)
            .unwrap_or_else(|| panic!("missing {proc_name}"));
        assert!(
            !matches!(sig, ProcSignature::Unknown),
            "expected known signature for {proc_name}"
        );
    }
}

#[test]
fn infers_call_chain() {
    // mid calls leaf twice, and leaf consumes 1 and produces 1. The second call
    // reuses the first result, so mid consumes 1 input and produces 1 output.
    let ws = workspace_from_modules(&[
        (
            "leaf",
            r#"
            proc callee
                drop
                push.1
            end
            "#,
        ),
        (
            "mid",
            r#"
            use leaf::callee

            proc caller
                exec.leaf::callee
                exec.callee
            end
            "#,
        ),
    ]);
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let mid = sigs.get("mid::caller").expect("sig");
    match mid {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(*inputs, 1);
            assert_eq!(*outputs, 1);
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

// ============================================================================
// Unit Tests - While loops
// ============================================================================

#[test]
fn infers_while_no_change() {
    // while loop pops a condition each time and the body has zero effect. The
    // missing loop condition yields unbounded inputs.
    let ws = workspace_from_modules(&[(
        "loop_mod",
        r#"
        proc loop_proc
            while.true
                push.1
                drop
            end
        end
        "#,
    )]);
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("loop_mod::loop_proc").expect("sig");
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("loop_prod::loop_prod").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            // Needs one condition input; the body manufactures the next condition.
            assert_eq!(*inputs, 1);
            assert_eq!(*outputs, 0);
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("loop_consume::loop_consume").expect("sig");
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
                push.1
            end
        end
        "#,
    )]);
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("loop_cond::loop_cond").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            // Needs one condition input; the body manufactures the next condition.
            assert_eq!(*inputs, 1);
            assert_eq!(*outputs, 0);
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

#[test]
fn infers_while_condition_from_body() {
    // Body manufactures the next condition by duplicating an input. When the
    // loop exits, the remaining value is an unchanged input, not an output.
    let ws = workspace_from_modules(&[(
        "loop_body_cond",
        r#"
        proc loop_body_cond
            while.true
                dup.0
            end
        end
        "#,
    )]);
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("loop_body_cond::loop_body_cond").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            assert_eq!(*inputs, 2);
            assert_eq!(*outputs, 0);
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

// ============================================================================
// Unit Tests - Conditionals
// ============================================================================

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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("if_same::if_same").expect("sig");
    match sig {
        ProcSignature::Known {
            inputs, outputs, ..
        } => {
            // One condition plus one value dropped in both branches
            assert_eq!(*inputs, 2);
            assert_eq!(*outputs, 0);
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
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("if_diff::if_diff").expect("sig");
    assert!(matches!(sig, ProcSignature::Unknown));
}

// ============================================================================
// Unit Tests - Repeat loops
// ============================================================================

#[test]
fn infers_correct_number_of_arguments_for_testz() {
    let ws = workspace_from_modules(&[(
        "word",
        r#"
        pub proc testz
            repeat.4
                dup.3 eq.0
            end
            and and and
        end
        "#,
    )]);
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let sig = sigs.get("word::testz").expect("sig");
    match sig {
        ProcSignature::Known { inputs, .. } => {
            // testz consumes 4 arguments (1 word)
            assert_eq!(*inputs, 4);
        }
        ProcSignature::Unknown => panic!("expected known signature"),
    }
}

// ============================================================================
// Property Tests
// ============================================================================

/// Helper to generate a body with drops and pushes, ensuring at least one instruction.
fn body_from_drops_pushes(drops: usize, pushes: usize) -> String {
    if drops == 0 && pushes == 0 {
        "nop".to_string()
    } else {
        format!(
            "{}{}",
            (0..drops).map(|_| "drop ").collect::<String>(),
            (0..pushes)
                .map(|i| format!("push.{i} "))
                .collect::<String>()
        )
    }
}

/// Helper to run signature inference on generated modules and check all
/// signatures are Known
fn check_all_signatures_known(modules: &[(String, String)]) -> Result<(), String> {
    let module_refs: Vec<(&str, &str)> = modules
        .iter()
        .map(|(name, src)| (name.as_str(), src.as_str()))
        .collect();

    let ws = workspace_from_modules(&module_refs);
    let cg = CallGraph::from(&ws);
    let sigs = infer_signatures(&ws, &cg);

    for (name, sig) in sigs.iter() {
        if matches!(sig, ProcSignature::Unknown) {
            return Err(format!("Procedure {} has unknown signature", name));
        }
    }
    Ok(())
}

fn instructions_with_effect(
    effect: StackEffect,
    max_len: usize,
) -> BoxedStrategy<Vec<Instruction>> {
    let net = effect.net_effect().unwrap_or(0);
    let neutral = prop::collection::vec(neutral_instruction_strategy(), 0..=max_len);
    if net == 0 {
        return neutral.boxed();
    }
    let tail_len = max_len.saturating_sub(1);
    if net > 0 {
        return (
            producing_instruction_strategy(),
            prop::collection::vec(neutral_instruction_strategy(), 0..=tail_len),
        )
            .prop_map(|(head, mut tail)| {
                tail.insert(0, head);
                tail
            })
            .boxed();
    }
    (
        consuming_instruction_strategy(),
        prop::collection::vec(neutral_instruction_strategy(), 0..=tail_len),
    )
        .prop_map(|(head, mut tail)| {
            tail.insert(0, head);
            tail
        })
        .boxed()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(50))]

    /// Property: Simple instruction sequences always yield Known signatures
    #[test]
    fn prop_simple_sequences_infer_successfully(
        insts in instructions_with_effect(StackEffect::known(0, 0), 10)
    ) {
        let body = if insts.is_empty() {
            "nop".to_string()
        } else {
            insts.iter().map(|i| i.to_pretty_string()).collect::<Vec<_>>().join("\n        ")
        };
        let source = format!(
            r#"
            proc test_proc
                {body}
            end
            "#
        );
        let modules = vec![("test".to_string(), source)];
        prop_assert!(check_all_signatures_known(&modules).is_ok());
    }

    /// Property: Procedures with only pushes yield Known signatures
    #[test]
    fn prop_push_only_infers_successfully(count in 1usize..=8) {
        let pushes = (0..count).map(|i| format!("push.{i}")).collect::<Vec<_>>().join("\n        ");
        let source = format!(
            r#"
            proc pusher
                {pushes}
            end
            "#
        );
        let modules = vec![("push_mod".to_string(), source)];
        prop_assert!(check_all_signatures_known(&modules).is_ok());
    }

    /// Property: Procedures with only drops yield Known signatures
    #[test]
    fn prop_drop_only_infers_successfully(count in 1usize..=8) {
        let drops = (0..count).map(|_| "drop").collect::<Vec<_>>().join("\n        ");
        let source = format!(
            r#"
            proc dropper
                {drops}
            end
            "#
        );
        let modules = vec![("drop_mod".to_string(), source)];
        prop_assert!(check_all_signatures_known(&modules).is_ok());
    }

    /// Property: Balanced if-else always yields Known signatures
    #[test]
    fn prop_balanced_if_infers_successfully(
        then_drops in 0usize..=3,
        then_pushes in 0usize..=3
    ) {
        // Both branches have the same effect
        let then_body = body_from_drops_pushes(then_drops, then_pushes);
        let else_body = body_from_drops_pushes(then_drops, then_pushes);
        let source = format!(
            r#"
            proc balanced_if
                if.true
                    {then_body}
                else
                    {else_body}
                end
            end
            "#
        );
        let modules = vec![("if_mod".to_string(), source)];
        prop_assert!(check_all_signatures_known(&modules).is_ok());
    }

    /// Property: Stack-neutral while loops (body pushes exactly 1) yield Known signatures
    #[test]
    fn prop_neutral_while_infers_successfully(extra_ops in 0usize..=3) {
        // Body pushes 1 for next condition, optionally with neutral ops before
        let neutral_ops = (0..extra_ops)
            .map(|i| format!("push.{i} drop"))
            .collect::<Vec<_>>()
            .join(" ");
        let source = format!(
            r#"
            proc neutral_while
                while.true
                    {neutral_ops}
                    push.1
                end
            end
            "#
        );
        let modules = vec![("while_mod".to_string(), source)];
        prop_assert!(check_all_signatures_known(&modules).is_ok());
    }

    /// Property: Repeat loops with any body always yield Known signatures
    #[test]
    fn prop_repeat_infers_successfully(
        count in 1usize..=5,
        body_pushes in 0usize..=2,
        body_drops in 0usize..=2
    ) {
        let body = body_from_drops_pushes(body_drops, body_pushes);
        let source = format!(
            r#"
            proc repeat_test
                repeat.{count}
                    {body}
                end
            end
            "#
        );
        let modules = vec![("repeat_mod".to_string(), source)];
        prop_assert!(check_all_signatures_known(&modules).is_ok());
    }

    /// Property: Linear call chains (DAG depth 2) yield all Known signatures
    #[test]
    fn prop_linear_call_chain_infers_successfully(
        leaf_pushes in 0usize..=2,
        leaf_drops in 0usize..=2
    ) {
        let leaf_body = body_from_drops_pushes(leaf_drops, leaf_pushes);
        let modules = vec![
            ("leaf".to_string(), format!(
                r#"
                proc leaf_proc
                    {leaf_body}
                end
                "#
            )),
            ("caller".to_string(), r#"
                use leaf::leaf_proc
                proc caller_proc
                    exec.leaf::leaf_proc
                end
                "#.to_string()),
        ];
        prop_assert!(check_all_signatures_known(&modules).is_ok());
    }

    /// Property: Multi-level call DAG yields all Known signatures
    #[test]
    fn prop_multi_level_dag_infers_successfully(
        l1_effect in (0usize..=2, 0usize..=2),
        l2_effect in (0usize..=2, 0usize..=2)
    ) {
        let (l1_drops, l1_pushes) = l1_effect;
        let (l2_drops, l2_pushes) = l2_effect;

        let l1_body = body_from_drops_pushes(l1_drops, l1_pushes);
        let l2_body = body_from_drops_pushes(l2_drops, l2_pushes);

        let modules = vec![
            ("level1".to_string(), format!(
                r#"
                proc l1_proc
                    {l1_body}
                end
                "#
            )),
            ("level2".to_string(), format!(
                r#"
                use level1::l1_proc
                proc l2_proc
                    exec.level1::l1_proc
                    {l2_body}
                end
                "#
            )),
            ("level3".to_string(), r#"
                use level2::l2_proc
                proc l3_proc
                    exec.level2::l2_proc
                end
                "#.to_string()),
        ];
        prop_assert!(check_all_signatures_known(&modules).is_ok());
    }
}

// ============================================================================
// Negative Property Tests - Verify Unknown signatures for invalid patterns
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    /// Property: Unbalanced if-else yields Unknown signature
    #[test]
    fn prop_unbalanced_if_yields_unknown(
        then_net in -2isize..=2,
        else_offset in 1isize..=3  // Ensure different from then
    ) {
        let else_net = then_net + else_offset;

        let then_body = if then_net >= 0 {
            (0..then_net).map(|i| format!("push.{i}")).collect::<Vec<_>>().join(" ")
        } else {
            (0..(-then_net)).map(|_| "drop".to_string()).collect::<Vec<_>>().join(" ")
        };

        let else_body = if else_net >= 0 {
            (0..else_net).map(|i| format!("push.{i}")).collect::<Vec<_>>().join(" ")
        } else {
            (0..(-else_net)).map(|_| "drop".to_string()).collect::<Vec<_>>().join(" ")
        };

        let source = format!(
            r#"
            proc unbalanced_if
                if.true
                    {then_body}
                else
                    {else_body}
                end
            end
            "#
        );

        let module_refs = [("unbal".to_string(), source)];
        let refs: Vec<(&str, &str)> = module_refs
            .iter()
            .map(|(n, s)| (n.as_str(), s.as_str()))
            .collect();

        let ws = workspace_from_modules(&refs);
        let cg = CallGraph::from(&ws);
        let sigs = infer_signatures(&ws, &cg);

        let sig = sigs.get("unbal::unbalanced_if").expect("sig");
        prop_assert!(matches!(sig, ProcSignature::Unknown),
            "Expected Unknown for unbalanced if, got {:?}", sig);
    }

    /// Property: Non-neutral while loop yields Unknown signature
    #[test]
    fn prop_non_neutral_while_yields_unknown(body_net in -2isize..=0) {
        // Body that doesn't push exactly 1 (the condition)
        // When body_net == 0, use nop to ensure non-empty body
        let body = if body_net == 0 {
            "nop".to_string()
        } else if body_net > 0 {
            (0..body_net).map(|i| format!("push.{i}")).collect::<Vec<_>>().join(" ")
        } else {
            (0..(-body_net)).map(|_| "drop".to_string()).collect::<Vec<_>>().join(" ")
        };

        let source = format!(
            r#"
            proc non_neutral_while
                while.true
                    {body}
                end
            end
            "#
        );

        let module_refs = [("nn_while".to_string(), source)];
        let refs: Vec<(&str, &str)> = module_refs
            .iter()
            .map(|(n, s)| (n.as_str(), s.as_str()))
            .collect();

        let ws = workspace_from_modules(&refs);
        let cg = CallGraph::from(&ws);
        let sigs = infer_signatures(&ws, &cg);

        let sig = sigs.get("nn_while::non_neutral_while").expect("sig");
        prop_assert!(matches!(sig, ProcSignature::Unknown),
            "Expected Unknown for non-neutral while (body_net={}), got {:?}", body_net, sig);
    }
}
