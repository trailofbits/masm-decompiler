use masm_decompiler::{
    frontend::testing::workspace_from_modules,
    lift::{LiftingError, lift_proc},
    signature::{ProcSignature, SignatureMap},
    symbol::{path::SymbolPath, resolution::create_resolver},
};

fn lift_with_signature(
    source: &str,
    proc_name: &str,
    signature: ProcSignature,
) -> Result<Vec<masm_decompiler::ir::Stmt>, LiftingError> {
    let ws = workspace_from_modules(&[("underflow", source)]);
    let proc_path = SymbolPath::new(format!("underflow::{proc_name}"));
    let (program, proc) = ws
        .lookup_proc_entry(&proc_path)
        .expect("fixture procedure should exist");
    let resolver = create_resolver(program.module(), ws.source_manager());

    let mut sigs = SignatureMap::default();
    sigs.insert(proc_path.clone(), signature);

    lift_proc(proc, &proc_path, &resolver, &sigs)
}

#[test]
fn lift_proc_reports_underflow_for_instruction_when_signature_is_too_shallow() {
    let result = lift_with_signature(
        r#"
        proc too_shallow_add
            add
        end
        "#,
        "too_shallow_add",
        ProcSignature::known(1, 1, 0),
    );

    assert!(
        matches!(
            result,
            Err(LiftingError::InsufficientStackDepth {
                ref operation,
                required_depth: 2,
                actual_depth: 1,
                ..
            }) if operation == "add"
        ),
        "expected add underflow, got {result:?}"
    );
}

#[test]
fn lift_proc_reports_underflow_for_stack_permutation_when_signature_is_too_shallow() {
    let result = lift_with_signature(
        r#"
        proc too_shallow_dupw
            dupw.3
        end
        "#,
        "too_shallow_dupw",
        ProcSignature::known(12, 16, 4),
    );

    assert!(
        matches!(
            result,
            Err(LiftingError::InsufficientStackDepth {
                ref operation,
                required_depth: 16,
                actual_depth: 12,
                ..
            }) if operation == "dupw.3"
        ),
        "expected dupw.3 underflow, got {result:?}"
    );
}

#[test]
fn lift_proc_reports_underflow_when_signature_claims_too_many_outputs() {
    let result = lift_with_signature(
        r#"
        proc too_many_outputs
            push.1
        end
        "#,
        "too_many_outputs",
        ProcSignature::known(0, 2, 2),
    );

    assert!(
        matches!(
            result,
            Err(LiftingError::InsufficientStackDepth {
                ref operation,
                required_depth: 2,
                actual_depth: 1,
                ..
            }) if operation == "return"
        ),
        "expected return underflow, got {result:?}"
    );
}
