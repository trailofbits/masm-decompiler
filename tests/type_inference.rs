use masm_decompiler::{
    decompile::Decompiler,
    frontend::testing::workspace_from_modules,
    symbol::path::SymbolPath,
    types::{InferredType, TypeRequirement},
};

fn diagnostics_for(
    decompiler: &Decompiler<'_>,
    proc: &str,
) -> Vec<masm_decompiler::types::TypeDiagnostic> {
    decompiler
        .type_diagnostics()
        .get(&SymbolPath::new(proc.to_string()))
        .cloned()
        .unwrap_or_default()
}

fn setup_decompiler() -> Decompiler<'static> {
    let ws = Box::new(workspace_from_modules(&[(
        "typecheck",
        r#"
        pub proc needs_bool
            if.true
                nop
            else
                nop
            end
        end

        pub proc needs_and_bool
            and
            drop
        end

        pub proc needs_felt
            push.1
            add
            drop
        end

        pub proc needs_u32
            push.1
            u32wrapping_add
            drop
        end

        pub proc needs_address
            mem_load
            drop
        end

        pub proc caller_bad_bool
            push.2
            exec.needs_bool
        end

        pub proc caller_ok_and_bool
            push.1.1
            eq
            push.2.2
            eq
            exec.needs_and_bool
        end

        pub proc caller_bad_and_bool
            push.1
            push.2
            exec.needs_and_bool
        end

        pub proc caller_unknown_bool
            adv_push.1
            exec.needs_bool
        end

        pub proc caller_bool_to_felt
            push.1.1
            eq
            exec.needs_felt
        end

        pub proc caller_bad_u32
            push.2
            exec.needs_u32
        end

        pub proc caller_bad_address
            push.1.1
            eq
            exec.needs_address
        end

        pub proc needs_bool_u32
            swap.1
            if.true
                nop
            else
                nop
            end
            push.1
            u32wrapping_add
            drop
        end

        pub proc caller_order_ok
            push.1.1
            eq
            push.2
            push.3
            u32wrapping_add
            exec.needs_bool_u32
        end

        pub proc caller_order_bad
            push.2
            push.3
            u32wrapping_add
            push.1.1
            eq
            exec.needs_bool_u32
        end

        pub proc out_mixed
            push.1
            push.1.1
            eq
        end

        pub proc out_and
            push.1.1
            eq
            push.2.2
            eq
            and
        end

        pub proc out_or
            push.1.1
            eq
            push.2.2
            eq
            or
        end

        pub proc out_xor
            push.1.1
            eq
            push.2.2
            eq
            xor
        end

        pub proc caller_out_ok
            exec.out_mixed
            if.true
                nop
            else
                nop
            end
            drop
        end

        pub proc caller_out_bad
            exec.out_mixed
            swap.1
            if.true
                nop
            else
                nop
            end
            drop
        end
        "#,
    )]));

    // Leak the workspace to simplify lifetime management in tests.
    let ws: &'static _ = Box::leak(ws);
    Decompiler::new(ws)
}

#[test]
fn infers_expected_input_requirements() {
    let decompiler = setup_decompiler();
    let summaries = decompiler.type_summaries();

    let needs_bool = summaries
        .get(&SymbolPath::new("typecheck::needs_bool"))
        .expect("needs_bool summary");
    assert_eq!(needs_bool.inputs, vec![TypeRequirement::Bool]);

    let needs_felt = summaries
        .get(&SymbolPath::new("typecheck::needs_felt"))
        .expect("needs_felt summary");
    assert_eq!(needs_felt.inputs, vec![TypeRequirement::Felt]);

    let needs_u32 = summaries
        .get(&SymbolPath::new("typecheck::needs_u32"))
        .expect("needs_u32 summary");
    assert_eq!(needs_u32.inputs, vec![TypeRequirement::U32]);

    let needs_address = summaries
        .get(&SymbolPath::new("typecheck::needs_address"))
        .expect("needs_address summary");
    assert_eq!(needs_address.inputs, vec![TypeRequirement::Address]);

    let needs_and_bool = summaries
        .get(&SymbolPath::new("typecheck::needs_and_bool"))
        .expect("needs_and_bool summary");
    assert_eq!(
        needs_and_bool.inputs,
        vec![TypeRequirement::Bool, TypeRequirement::Bool]
    );
}

#[test]
fn reports_call_argument_type_mismatches() {
    let decompiler = setup_decompiler();

    let bad_bool = diagnostics_for(&decompiler, "typecheck::caller_bad_bool");
    assert!(
        bad_bool
            .iter()
            .any(|diag| diag.arg_index == Some(0) && diag.expected == Some(TypeRequirement::Bool))
    );

    let bad_u32 = diagnostics_for(&decompiler, "typecheck::caller_bad_u32");
    assert!(
        bad_u32
            .iter()
            .any(|diag| diag.arg_index == Some(0) && diag.expected == Some(TypeRequirement::U32))
    );

    let bad_addr = diagnostics_for(&decompiler, "typecheck::caller_bad_address");
    assert!(
        bad_addr.iter().any(
            |diag| diag.arg_index == Some(0) && diag.expected == Some(TypeRequirement::Address)
        )
    );

    let bad_and = diagnostics_for(&decompiler, "typecheck::caller_bad_and_bool");
    assert!(
        bad_and
            .iter()
            .any(|diag| diag.arg_index == Some(0) && diag.expected == Some(TypeRequirement::Bool)),
        "expected arg 0 Bool mismatch, got: {bad_and:?}"
    );
    assert!(
        bad_and
            .iter()
            .any(|diag| diag.arg_index == Some(1) && diag.expected == Some(TypeRequirement::Bool)),
        "expected arg 1 Bool mismatch, got: {bad_and:?}"
    );
}

#[test]
fn suppresses_mismatch_for_unknown_argument_type() {
    let decompiler = setup_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "typecheck::caller_unknown_bool");
    assert!(
        diagnostics.is_empty(),
        "unknown argument types should not emit diagnostics: {diagnostics:?}"
    );
}

#[test]
fn allows_promotion_to_felt() {
    let decompiler = setup_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "typecheck::caller_bool_to_felt");
    assert!(
        diagnostics.is_empty(),
        "Bool should be accepted where Felt is required: {diagnostics:?}"
    );
}

#[test]
fn type_summary_positions_follow_stack_conventions() {
    let decompiler = setup_decompiler();
    let summaries = decompiler.type_summaries();

    let needs_bool_u32 = summaries
        .get(&SymbolPath::new("typecheck::needs_bool_u32"))
        .expect("needs_bool_u32 summary");
    assert_eq!(
        needs_bool_u32.inputs,
        vec![TypeRequirement::U32, TypeRequirement::Bool]
    );

    let out_mixed = summaries
        .get(&SymbolPath::new("typecheck::out_mixed"))
        .expect("out_mixed summary");
    assert_eq!(
        out_mixed.outputs,
        vec![InferredType::Felt, InferredType::Bool]
    );
}

#[test]
fn enforces_argument_types_by_stack_position() {
    let decompiler = setup_decompiler();

    let ok = diagnostics_for(&decompiler, "typecheck::caller_order_ok");
    assert!(ok.is_empty(), "stack-ordered arguments should pass: {ok:?}");

    let bad = diagnostics_for(&decompiler, "typecheck::caller_order_bad");
    assert!(
        bad.iter().any(|diag| {
            diag.arg_index == Some(0) && diag.expected == Some(TypeRequirement::U32)
        }),
        "expected arg 0 U32 mismatch, got: {bad:?}"
    );
    assert!(
        bad.iter().any(|diag| {
            diag.arg_index == Some(1) && diag.expected == Some(TypeRequirement::Bool)
        }),
        "expected arg 1 Bool mismatch, got: {bad:?}"
    );
}

#[test]
fn maps_call_results_to_output_types_by_position() {
    let decompiler = setup_decompiler();

    let ok = diagnostics_for(&decompiler, "typecheck::caller_out_ok");
    assert!(
        ok.is_empty(),
        "top result should be inferred Bool for condition: {ok:?}"
    );

    let bad = diagnostics_for(&decompiler, "typecheck::caller_out_bad");
    assert!(
        bad.iter()
            .any(|diag| diag.message.contains("if-condition is not guaranteed Bool")),
        "expected Bool condition mismatch, got: {bad:?}"
    );
}

#[test]
fn infers_boolean_operator_outputs_as_bool() {
    let decompiler = setup_decompiler();
    let summaries = decompiler.type_summaries();

    let out_and = summaries
        .get(&SymbolPath::new("typecheck::out_and"))
        .expect("out_and summary");
    assert_eq!(out_and.outputs, vec![InferredType::Bool]);

    let out_or = summaries
        .get(&SymbolPath::new("typecheck::out_or"))
        .expect("out_or summary");
    assert_eq!(out_or.outputs, vec![InferredType::Bool]);

    let out_xor = summaries
        .get(&SymbolPath::new("typecheck::out_xor"))
        .expect("out_xor summary");
    assert_eq!(out_xor.outputs, vec![InferredType::Bool]);
}

#[test]
fn accepts_boolean_arguments_for_and_operator() {
    let decompiler = setup_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "typecheck::caller_ok_and_bool");
    assert!(
        diagnostics.is_empty(),
        "boolean arguments to and should satisfy Bool requirements: {diagnostics:?}"
    );
}

#[test]
fn infers_locaddr_output_as_address() {
    let ws = workspace_from_modules(&[(
        "locaddr_types",
        r#"
        pub proc returns_locaddr
            locaddr.0
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let summaries = decompiler.type_summaries();
    let summary = summaries
        .get(&SymbolPath::new("locaddr_types::returns_locaddr"))
        .expect("returns_locaddr summary");
    assert_eq!(summary.outputs, vec![InferredType::Address]);
}

#[test]
fn infers_u32shift_outputs_as_u32() {
    let ws = workspace_from_modules(&[(
        "u32_shift_types",
        r#"
        pub proc shifts
            push.1
            u32shl.1
            u32shr.1
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let summaries = decompiler.type_summaries();
    let summary = summaries
        .get(&SymbolPath::new("u32_shift_types::shifts"))
        .expect("shifts summary");
    assert_eq!(summary.outputs, vec![InferredType::U32]);
}
