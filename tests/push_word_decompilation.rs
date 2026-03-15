//! Regression tests for `push.[a, b, c, d]` (word push) decompilation.
//!
//! The word push instruction pushes 4 felt elements onto the stack. This is
//! distinct from a scalar push (`push.N`) which pushes a single element.

use masm_decompiler::{
    decompile::Decompiler,
    fmt::{CodeWriter, FormattingConfig},
    frontend::testing::workspace_from_modules,
};

const FIXTURE: &str = include_str!("fixtures/push_word.masm");

fn decompile_proc(source: &str, proc_name: &str) -> masm_decompiler::decompile::DecompiledProc {
    let ws = workspace_from_modules(&[("push_word", source)]);
    let fq_name = format!("push_word::{proc_name}");
    Decompiler::new(&ws)
        .decompile_proc(&fq_name)
        .expect("decompilation should succeed")
}

fn format_body(result: &masm_decompiler::decompile::DecompiledProc) -> String {
    let mut writer = CodeWriter::with_config(FormattingConfig::new().with_color(false));
    writer.register_loop_vars(result.stmts());
    for stmt in result.stmts() {
        writer.write(stmt.clone());
    }
    writer.finish()
}

/// Verify that `push.[a, b, c, d]` is correctly handled as a 4-element push
/// across the full pipeline: signature inference, lifting, and formatting.
#[test]
fn push_word_is_decomposed_into_four_felt_pushes() {
    // --- push_word_identity: bare word push ---
    let identity = decompile_proc(FIXTURE, "push_word_identity");
    let identity_body = format_body(&identity);

    assert_eq!(
        identity.inputs(),
        Some(0),
        "push.[1,2,3,4] should require no inputs: {identity_body}"
    );
    assert_eq!(
        identity.outputs(),
        Some(4),
        "push.[1,2,3,4] should produce 4 outputs: {identity_body}"
    );
    assert!(
        !identity_body.contains("[1, 2, 3, 4]"),
        "word push should be decomposed into individual felt assignments, \
         not formatted as a single word constant: {identity_body}"
    );

    // --- push_word_sum: word push followed by three adds ---
    let sum = decompile_proc(FIXTURE, "push_word_sum");
    let sum_body = format_body(&sum);

    assert_eq!(
        sum.inputs(),
        Some(0),
        "push.[1,2,3,4] followed by three adds should require no inputs: {sum_body}"
    );
    assert_eq!(
        sum.outputs(),
        Some(1),
        "push.[1,2,3,4] followed by three adds should produce 1 output: {sum_body}"
    );
}
