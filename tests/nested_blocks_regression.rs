use masm_decompiler::{
    DecompilationError,
    decompile::Decompiler,
    frontend::testing::workspace_from_modules,
    lift::{LiftingError, lift_proc},
    symbol::{path::SymbolPath, resolution::create_resolver},
};

#[test]
fn nested_blocks_fixture_resolves_calls_in_blocks() {
    let ws =
        workspace_from_modules(&[("nested_blocks", include_str!("fixtures/nested_blocks.masm"))]);
    let decompiler = Decompiler::new(&ws);

    decompiler
        .decompile_proc("nested_blocks::nested_repeat")
        .expect("nested_repeat should decompile");

    for proc_name in ["nested_blocks::nested_if", "nested_blocks::nested_while"] {
        let proc_path = SymbolPath::new(proc_name);
        let (program, proc) = ws
            .lookup_proc_entry(&proc_path)
            .expect("fixture procedure should exist");
        let resolver = create_resolver(program.module(), ws.source_manager());
        let lift_result = lift_proc(proc, &proc_path, &resolver, decompiler.signatures());

        let expected_construct = if proc_name.ends_with("nested_if") {
            "if.true"
        } else {
            "while.true"
        };
        assert!(
            matches!(
                lift_result,
                Err(LiftingError::MissingControlFlowCondition {
                    construct,
                    required_depth: 1,
                    actual_depth: 0,
                    ..
                }) if construct == expected_construct
            ),
            "expected explicit control-flow underflow for {proc_name}, got {lift_result:?}"
        );
    }

    for proc_name in [
        "nested_blocks::nested_if",
        "nested_blocks::nested_while",
        "nested_blocks::deeply_nested",
    ] {
        let err = decompiler
            .decompile_proc(proc_name)
            .expect_err("unsupported fixture should fail cleanly");
        assert!(
            matches!(err, DecompilationError::UnknownProcedureSignature(ref name) if name == proc_name),
            "expected unknown-signature decompilation error for {proc_name}, got {err:?}"
        );
    }
}
