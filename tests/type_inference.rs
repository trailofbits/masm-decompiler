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
            push.3
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
            push.2
            exec.needs_bool_u32
        end

        pub proc out_mixed
            push.2
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

        pub proc assert_only
            u32assert
        end

        pub proc assert2_only
            u32assert2
        end

        pub proc assertw_only
            u32assertw
        end

        pub proc assert_then_add
            u32assert
            push.1
            u32wrapping_add
            drop
        end

        pub proc assert_then_divmod
            u32assert
            push.4
            u32divmod
            drop
            drop
        end

        pub proc split_only
            u32split
        end

        pub proc split_then_add
            u32split
            drop
            push.1
            u32wrapping_add
            drop
        end

        pub proc cast_only
            u32cast
        end

        pub proc test_only
            u32test
            drop
        end

        pub proc test_outputs
            u32test
        end

        pub proc not_only
            u32not
        end

        pub proc rotr_only
            push.1
            u32rotr
        end

        pub proc widening_add_only
            push.1
            u32widening_add
        end

        pub proc widening_add3_only
            push.1
            push.2
            u32widening_add3
        end

        pub proc mod_only
            push.8
            u32mod
        end

        pub proc sdepth_only
            sdepth
        end

        pub proc cast_then_add
            u32cast
            push.1
            u32wrapping_add
            drop
        end

        pub proc bool_to_u32assert
            push.1.1
            eq
            u32assert
            drop
        end

        pub proc bool_to_u32split
            push.1.1
            eq
            u32split
            drop
            drop
        end

        pub proc bool_to_u32cast
            push.1.1
            eq
            u32cast
            drop
        end

        pub proc bool_to_u32test
            push.1.1
            eq
            u32test
            drop
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
fn call_argument_diagnostics_disabled_in_chain_lattice() {
    let decompiler = setup_decompiler();

    // In the four-point chain, no scalar type pair is definitively
    // incompatible. Call-argument diagnostics are disabled.
    let bad_bool = diagnostics_for(&decompiler, "typecheck::caller_bad_bool");
    assert!(
        bad_bool.is_empty(),
        "call-arg diagnostics disabled: {bad_bool:?}"
    );

    let bad_u32 = diagnostics_for(&decompiler, "typecheck::caller_bad_u32");
    assert!(
        bad_u32.is_empty(),
        "call-arg diagnostics disabled: {bad_u32:?}"
    );

    let bad_addr = diagnostics_for(&decompiler, "typecheck::caller_bad_address");
    assert!(
        bad_addr.is_empty(),
        "call-arg diagnostics disabled: {bad_addr:?}"
    );

    let bad_and = diagnostics_for(&decompiler, "typecheck::caller_bad_and_bool");
    assert!(
        bad_and.is_empty(),
        "call-arg diagnostics disabled: {bad_and:?}"
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
        vec![InferredType::U32, InferredType::Bool]
    );
}

#[test]
fn enforces_argument_types_by_stack_position() {
    let decompiler = setup_decompiler();

    let ok = diagnostics_for(&decompiler, "typecheck::caller_order_ok");
    assert!(ok.is_empty(), "stack-ordered arguments should pass: {ok:?}");

    // Call-argument diagnostics are disabled in the chain lattice.
    let bad = diagnostics_for(&decompiler, "typecheck::caller_order_bad");
    assert!(bad.is_empty(), "call-arg diagnostics disabled: {bad:?}");
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

#[test]
fn infers_inv_input_and_output_as_felt() {
    let ws = workspace_from_modules(&[(
        "inv_types",
        r#"
        pub proc inverse
            inv
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let summaries = decompiler.type_summaries();
    let summary = summaries
        .get(&SymbolPath::new("inv_types::inverse"))
        .expect("inverse summary");
    assert_eq!(summary.inputs, vec![TypeRequirement::Felt]);
    assert_eq!(summary.outputs, vec![InferredType::Felt]);
}

#[test]
fn u32_assert_split_and_cast_do_not_seed_u32_input_requirements() {
    let decompiler = setup_decompiler();
    let summaries = decompiler.type_summaries();

    let assert_only = summaries
        .get(&SymbolPath::new("typecheck::assert_only"))
        .expect("assert_only summary");
    assert_eq!(assert_only.inputs, vec![TypeRequirement::Felt]);

    let assert2_only = summaries
        .get(&SymbolPath::new("typecheck::assert2_only"))
        .expect("assert2_only summary");
    assert_eq!(
        assert2_only.inputs,
        vec![TypeRequirement::Felt, TypeRequirement::Felt]
    );

    let assertw_only = summaries
        .get(&SymbolPath::new("typecheck::assertw_only"))
        .expect("assertw_only summary");
    assert_eq!(
        assertw_only.inputs,
        vec![
            TypeRequirement::Felt,
            TypeRequirement::Felt,
            TypeRequirement::Felt,
            TypeRequirement::Felt
        ]
    );

    let split_only = summaries
        .get(&SymbolPath::new("typecheck::split_only"))
        .expect("split_only summary");
    assert_eq!(split_only.inputs, vec![TypeRequirement::Felt]);
    assert_eq!(
        split_only.outputs,
        vec![InferredType::U32, InferredType::U32]
    );

    let cast_only = summaries
        .get(&SymbolPath::new("typecheck::cast_only"))
        .expect("cast_only summary");
    assert_eq!(cast_only.inputs, vec![TypeRequirement::Felt]);
    assert_eq!(cast_only.outputs, vec![InferredType::U32]);

    let test_only = summaries
        .get(&SymbolPath::new("typecheck::test_only"))
        .expect("test_only summary");
    assert_eq!(test_only.inputs, vec![TypeRequirement::Felt]);

    let test_outputs = summaries
        .get(&SymbolPath::new("typecheck::test_outputs"))
        .expect("test_outputs summary");
    assert_eq!(test_outputs.outputs, vec![InferredType::Bool]);
}

#[test]
fn u32_postconditions_discharge_downstream_u32_requirements() {
    let decompiler = setup_decompiler();
    let summaries = decompiler.type_summaries();

    let assert_then_add = summaries
        .get(&SymbolPath::new("typecheck::assert_then_add"))
        .expect("assert_then_add summary");
    assert_eq!(assert_then_add.inputs, vec![TypeRequirement::Felt]);

    let assert_then_divmod = summaries
        .get(&SymbolPath::new("typecheck::assert_then_divmod"))
        .expect("assert_then_divmod summary");
    assert_eq!(assert_then_divmod.inputs, vec![TypeRequirement::Felt]);

    let split_then_add = summaries
        .get(&SymbolPath::new("typecheck::split_then_add"))
        .expect("split_then_add summary");
    assert_eq!(split_then_add.inputs, vec![TypeRequirement::Felt]);

    let cast_then_add = summaries
        .get(&SymbolPath::new("typecheck::cast_then_add"))
        .expect("cast_then_add summary");
    assert_eq!(cast_then_add.inputs, vec![TypeRequirement::Felt]);
}

#[test]
fn u32_not_rotr_widening_add_and_mod_infer_u32_types() {
    let decompiler = setup_decompiler();
    let summaries = decompiler.type_summaries();

    let not_only = summaries
        .get(&SymbolPath::new("typecheck::not_only"))
        .expect("not_only summary");
    assert_eq!(not_only.inputs, vec![TypeRequirement::U32]);
    assert_eq!(not_only.outputs, vec![InferredType::U32]);

    let rotr_only = summaries
        .get(&SymbolPath::new("typecheck::rotr_only"))
        .expect("rotr_only summary");
    assert_eq!(rotr_only.inputs, vec![TypeRequirement::U32]);
    assert_eq!(rotr_only.outputs, vec![InferredType::U32]);

    let widening_add_only = summaries
        .get(&SymbolPath::new("typecheck::widening_add_only"))
        .expect("widening_add_only summary");
    assert_eq!(widening_add_only.inputs, vec![TypeRequirement::U32]);
    assert_eq!(
        widening_add_only.outputs,
        vec![InferredType::U32, InferredType::U32]
    );

    let widening_add3_only = summaries
        .get(&SymbolPath::new("typecheck::widening_add3_only"))
        .expect("widening_add3_only summary");
    assert_eq!(widening_add3_only.inputs, vec![TypeRequirement::U32]);
    assert_eq!(
        widening_add3_only.outputs,
        vec![InferredType::U32, InferredType::U32]
    );

    let mod_only = summaries
        .get(&SymbolPath::new("typecheck::mod_only"))
        .expect("mod_only summary");
    assert_eq!(mod_only.inputs, vec![TypeRequirement::U32]);
    assert_eq!(mod_only.outputs, vec![InferredType::U32]);

    let sdepth_only = summaries
        .get(&SymbolPath::new("typecheck::sdepth_only"))
        .expect("sdepth_only summary");
    assert_eq!(sdepth_only.inputs, vec![]);
    assert_eq!(sdepth_only.outputs, vec![InferredType::U32]);
}

fn setup_storage_decompiler() -> Decompiler<'static> {
    let ws = Box::new(workspace_from_modules(&[(
        "storage",
        r#"
        # U32 value round-trips through a local and is used in a u32 operation.
        # Before fix: loc_load produces Felt, u32wrapping_add triggers diagnostic.
        # After fix: loc_load produces U32, no diagnostic.
        @locals(1)
        pub proc u32_local_roundtrip
            push.1
            push.2
            u32wrapping_add
            loc_store.0
            loc_load.0
            push.1
            u32wrapping_add
            drop
        end

        # Address from locaddr round-trips through a local and is used as mem_load address.
        # Before fix: loc_load produces Felt, mem_load address triggers diagnostic.
        # After fix: loc_load produces Address, no diagnostic.
        @locals(1)
        pub proc address_local_roundtrip
            locaddr.0
            loc_store.0
            loc_load.0
            mem_load
            drop
        end

        # A Felt value stored and loaded should remain Felt (no regression).
        @locals(1)
        pub proc felt_local_roundtrip
            push.999
            loc_store.0
            loc_load.0
            drop
        end

        # Word store/load: all 4 elements of a U32 word should preserve type.
        @locals(1)
        pub proc u32_word_local_roundtrip
            push.1.2.3.4
            u32assertw
            loc_storew_be.0
            loc_loadw_be.0
            push.1
            u32wrapping_add
            drop drop drop drop
        end

        # U32 stored to memory at immediate address and loaded back.
        # Both mem_store.100 and mem_load.100 use the same immediate address.
        # Before fix: mem_load produces Felt, u32wrapping_add triggers diagnostic.
        # After fix: mem_load produces U32, no diagnostic.
        pub proc u32_mem_roundtrip
            push.1
            push.2
            u32wrapping_add
            mem_store.100
            mem_load.100
            push.1
            u32wrapping_add
            drop
        end

        # Address stored to memory at immediate address and loaded back.
        @locals(1)
        pub proc address_mem_roundtrip
            locaddr.0
            mem_store.100
            mem_load.100
            mem_load
            drop
        end

        # U32 stored via locaddr and loaded back.
        # locaddr.0 is used for both store and load but produces different SSA
        # variables — the MemAddressKey::LocalAddr(0) abstraction connects them.
        @locals(1)
        pub proc u32_mem_locaddr_roundtrip
            push.1
            push.2
            u32wrapping_add
            locaddr.0
            mem_store
            locaddr.0
            mem_load
            push.1
            u32wrapping_add
            drop
        end

        # Procedure stores its input to a local, loads it, uses it in u32 op.
        # Without back-propagation: input requirement stays Unknown.
        # With back-propagation: U32 requirement propagates from u32wrapping_add
        # back through the load/store to the procedure input.
        @locals(1)
        pub proc u32_req_through_local
            loc_store.0
            loc_load.0
            push.1
            u32wrapping_add
            drop
        end

        # Same pattern through memory with immediate address.
        pub proc u32_req_through_mem
            mem_store.200
            mem_load.200
            push.1
            u32wrapping_add
            drop
        end

        # locaddr.0 followed by add.1 to address element 1 of the word.
        # The inferred type of add is Felt (not Address), but the
        # MemAddressKey::LocalAddrOffset suppresses the address diagnostic.
        @locals(1)
        pub proc address_offset_no_warning
            locaddr.0
            push.1
            add
            mem_load
            drop
        end

        # A large Felt constant (>= 2^32) used as a memory address should
        # produce a diagnostic warning, not be silently suppressed.
        pub proc large_felt_as_address
            push.4294967296
            mem_load
            drop
        end

        # Address + large U32 offset should produce a diagnostic because the
        # u32wrapping_add result has no MemAddressKey (address keys are not
        # propagated through u32 operations), so the `add` result has no key
        # and its inferred type (Felt) is incompatible with Address.
        @locals(2)
        pub proc address_plus_large_offset
            locaddr.0
            push.4294967295
            push.0
            u32wrapping_add
            add
            mem_load
            drop
        end

        # The procedure input flows through a local store/load and is used
        # by two loads with conflicting requirements: u32wrapping_add (U32)
        # and `not` (Bool). The analysis should converge without exhausting
        # 128 iterations. The conflicting requirements collapse to Unknown,
        # so the input requirement should also be Unknown.
        @locals(1)
        pub proc conflicting_local_requirements
            loc_store.0

            loc_load.0
            push.1
            u32wrapping_add
            drop

            loc_load.0
            not
            drop
        end

        # locaddr.0 flows through an if-phi and is used as mem_load address.
        # Both branches produce the same locaddr.0 value.
        @locals(1)
        pub proc address_through_if_phi
            push.1
            if.true
                locaddr.0
            else
                locaddr.0
            end
            mem_load
            drop
        end

        # locaddr.0 - 1: field subtraction computes (addr - 1) mod p,
        # which may point outside the procedure's local frame. No
        # MemAddressKey should be created, so the diagnostic should fire.
        @locals(1)
        pub proc address_through_sub_offset
            locaddr.0
            push.1
            sub
            mem_load
            drop
        end

        # locaddr.0 + 1 + 2: chained offsets should compose into
        # LocalAddrOffset(0, 3), suppressing the address diagnostic.
        @locals(1)
        pub proc address_chained_offset
            locaddr.0
            push.1
            add
            push.2
            add
            mem_load
            drop
        end

        # locaddr.0 and locaddr.1 flow through an if-phi. The branches
        # disagree, so no MemAddressKey is propagated to the phi dest.
        # A U32 stored at the phi address should NOT be tracked, so
        # loading from locaddr.0 should produce Felt (not U32).
        @locals(2)
        pub proc u32_not_tracked_through_disagreeing_phi
            push.1.2
            u32wrapping_add
            push.1
            if.true
                locaddr.0
            else
                locaddr.1
            end
            mem_store
            drop
            locaddr.0
            mem_load
        end
        "#,
    )]));

    let ws: &'static _ = Box::leak(ws);
    Decompiler::new(ws)
}

#[test]
fn u32_type_preserved_through_local_roundtrip() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::u32_local_roundtrip");
    assert!(
        diagnostics.is_empty(),
        "U32 type should survive local store/load roundtrip: {diagnostics:?}"
    );
}

#[test]
fn address_type_preserved_through_local_roundtrip() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::address_local_roundtrip");
    assert!(
        diagnostics.is_empty(),
        "Address type should survive local store/load roundtrip: {diagnostics:?}"
    );
}

#[test]
fn u32_type_preserved_through_word_local_roundtrip() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::u32_word_local_roundtrip");
    assert!(
        diagnostics.is_empty(),
        "U32 type should survive local word store/load roundtrip: {diagnostics:?}"
    );
}

#[test]
fn felt_type_unchanged_through_local_roundtrip() {
    let decompiler = setup_storage_decompiler();
    let summaries = decompiler.type_summaries();
    let summary = summaries
        .get(&SymbolPath::new("storage::felt_local_roundtrip"))
        .expect("felt_local_roundtrip summary");
    // Procedure takes no stack inputs — the Felt comes from a push constant.
    assert!(
        summary.inputs.is_empty() || summary.inputs.iter().all(|r| *r == TypeRequirement::Felt),
        "felt roundtrip should not introduce spurious requirements: {:?}",
        summary.inputs
    );
}

#[test]
fn u32_type_preserved_through_mem_roundtrip() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::u32_mem_roundtrip");
    assert!(
        diagnostics.is_empty(),
        "U32 type should survive memory store/load roundtrip: {diagnostics:?}"
    );
}

#[test]
fn address_type_preserved_through_mem_roundtrip() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::address_mem_roundtrip");
    assert!(
        diagnostics.is_empty(),
        "Address type should survive memory store/load roundtrip: {diagnostics:?}"
    );
}

#[test]
fn u32_type_preserved_through_mem_locaddr_roundtrip() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::u32_mem_locaddr_roundtrip");
    assert!(
        diagnostics.is_empty(),
        "U32 type should survive locaddr-addressed memory roundtrip: {diagnostics:?}"
    );
}

#[test]
fn u32_assert_split_and_cast_skip_argument_mismatch_diagnostics() {
    let decompiler = setup_decompiler();

    let assert_diags = diagnostics_for(&decompiler, "typecheck::bool_to_u32assert");
    assert!(
        assert_diags.is_empty(),
        "u32assert should be a runtime check, got: {assert_diags:?}"
    );

    let split_diags = diagnostics_for(&decompiler, "typecheck::bool_to_u32split");
    assert!(
        split_diags.is_empty(),
        "u32split should not require U32 input, got: {split_diags:?}"
    );

    let cast_diags = diagnostics_for(&decompiler, "typecheck::bool_to_u32cast");
    assert!(
        cast_diags.is_empty(),
        "u32cast should not require U32 input, got: {cast_diags:?}"
    );

    let test_diags = diagnostics_for(&decompiler, "typecheck::bool_to_u32test");
    assert!(
        test_diags.is_empty(),
        "u32test should not require U32 input, got: {test_diags:?}"
    );
}

#[test]
fn requirement_propagates_through_local_store() {
    let decompiler = setup_storage_decompiler();
    let summaries = decompiler.type_summaries();
    let summary = summaries
        .get(&SymbolPath::new("storage::u32_req_through_local"))
        .expect("u32_req_through_local summary");
    assert_eq!(
        summary.inputs,
        vec![TypeRequirement::U32],
        "U32 requirement should propagate back through local store/load to input"
    );
}

#[test]
fn requirement_propagates_through_mem_store() {
    let decompiler = setup_storage_decompiler();
    let summaries = decompiler.type_summaries();
    let summary = summaries
        .get(&SymbolPath::new("storage::u32_req_through_mem"))
        .expect("u32_req_through_mem summary");
    assert_eq!(
        summary.inputs,
        vec![TypeRequirement::U32],
        "U32 requirement should propagate back through memory store/load to input"
    );
}

#[test]
fn address_plus_offset_preserves_address_type() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::address_offset_no_warning");
    assert!(
        diagnostics.is_empty(),
        "Address + small offset should remain Address: {diagnostics:?}"
    );
}

#[test]
fn large_felt_constant_address_emits_diagnostic() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::large_felt_as_address");
    assert!(
        diagnostics
            .iter()
            .any(|d| d.message.contains("not guaranteed Address")),
        "Felt constant >= 2^32 used as memory address should produce an address diagnostic, got: {diagnostics:?}"
    );
}

#[test]
fn address_plus_large_offset_emits_diagnostic() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::address_plus_large_offset");
    assert!(
        diagnostics
            .iter()
            .any(|d| d.message.contains("not guaranteed Address")),
        "Address + untracked offset should produce an address diagnostic, got: {diagnostics:?}"
    );
}

#[test]
fn conflicting_local_requirements_do_not_propagate() {
    let decompiler = setup_storage_decompiler();
    let summaries = decompiler.type_summaries();
    let summary = summaries
        .get(&SymbolPath::new("storage::conflicting_local_requirements"))
        .expect("conflicting_local_requirements summary");
    // The procedure takes one stack input, stores it to local 0, then loads
    // it twice with requirements U32 and Bool. In the chain lattice,
    // glb(U32, Bool) = Bool (the most specific type that satisfies both).
    assert_eq!(
        summary.inputs,
        vec![TypeRequirement::Bool],
        "glb(U32, Bool) = Bool in the chain lattice"
    );
}

#[test]
fn address_sub_offset_emits_diagnostic() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::address_through_sub_offset");
    assert!(
        diagnostics
            .iter()
            .any(|d| d.message.contains("not guaranteed Address")),
        "locaddr - offset should produce an address diagnostic: {diagnostics:?}"
    );
}

#[test]
fn address_chained_offset_suppresses_diagnostic() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::address_chained_offset");
    assert!(
        diagnostics.is_empty(),
        "locaddr + 1 + 2 should suppress address diagnostic via chained LocalAddrOffset: {diagnostics:?}"
    );
}

#[test]
fn u32_not_tracked_through_disagreeing_phi() {
    let decompiler = setup_storage_decompiler();
    let summaries = decompiler.type_summaries();
    let summary = summaries
        .get(&SymbolPath::new(
            "storage::u32_not_tracked_through_disagreeing_phi",
        ))
        .expect("u32_not_tracked_through_disagreeing_phi summary");
    // The procedure stores U32 at phi(locaddr.0, locaddr.1) — the phi
    // branches disagree so no MemAddressKey is propagated and the type
    // is not tracked. Loading from locaddr.0 should yield the default
    // Felt type, not U32.
    assert_eq!(
        summary.outputs,
        vec![InferredType::Felt],
        "mem_load from locaddr.0 should be Felt when type was stored through disagreeing phi"
    );
}

#[test]
fn address_key_survives_if_phi() {
    let decompiler = setup_storage_decompiler();
    let diagnostics = diagnostics_for(&decompiler, "storage::address_through_if_phi");
    assert!(
        diagnostics.is_empty(),
        "locaddr through if-phi should not produce address diagnostic: {diagnostics:?}"
    );
}

// -- Regression tests for type lattice redesign --------------------------

#[test]
fn is_odd_intrinsic_infers_bool() {
    let ws = workspace_from_modules(&[(
        "is_odd_types",
        r#"
        pub proc uses_is_odd
            push.5
            is_odd
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let summaries = decompiler.type_summaries();
    let summary = summaries
        .get(&SymbolPath::new("is_odd_types::uses_is_odd"))
        .expect("uses_is_odd summary");
    assert_eq!(summary.outputs, vec![InferredType::Bool]);
}

#[test]
fn u32_range_constant_infers_u32() {
    let ws = workspace_from_modules(&[(
        "const_types",
        r#"
        pub proc returns_small_felt
            push.42
        end

        pub proc returns_large_felt
            push.4294967296
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let summaries = decompiler.type_summaries();

    let small = summaries
        .get(&SymbolPath::new("const_types::returns_small_felt"))
        .expect("returns_small_felt summary");
    assert_eq!(small.outputs, vec![InferredType::U32]);

    let large = summaries
        .get(&SymbolPath::new("const_types::returns_large_felt"))
        .expect("returns_large_felt summary");
    assert_eq!(large.outputs, vec![InferredType::Felt]);
}

#[test]
fn bool_satisfies_address_requirement() {
    let ws = workspace_from_modules(&[(
        "subtype_test",
        r#"
        pub proc bool_as_address
            push.1.1
            eq
            mem_load
            drop
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let diagnostics = decompiler
        .type_diagnostics()
        .get(&SymbolPath::new("subtype_test::bool_as_address"))
        .cloned()
        .unwrap_or_default();
    assert!(
        diagnostics.is_empty(),
        "Bool satisfies Address in the chain lattice: {diagnostics:?}"
    );
}

#[test]
fn local_store_join_widens_type() {
    let ws = workspace_from_modules(&[(
        "store_join",
        r#"
        @locals(1)
        pub proc store_bool_then_u32
            push.1
            loc_store.0
            push.42
            u32assert
            loc_store.0
            loc_load.0
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let summaries = decompiler.type_summaries();
    let summary = summaries
        .get(&SymbolPath::new("store_join::store_bool_then_u32"))
        .expect("store_bool_then_u32 summary");
    // Bool stored then U32 stored → join(Bool, U32) = U32
    assert_eq!(summary.outputs, vec![InferredType::U32]);
}

#[test]
fn opaque_summary_with_arity_fills_felt() {
    use masm_decompiler::types::TypeSummary;
    let summary = TypeSummary::opaque_with_arity(2, 3);
    assert!(summary.is_opaque());
    assert_eq!(summary.inputs, vec![TypeRequirement::Felt; 2]);
    assert_eq!(summary.outputs, vec![InferredType::Felt; 3]);
}
