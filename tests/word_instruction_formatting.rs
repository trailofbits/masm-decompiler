use masm_decompiler::{
    decompile::Decompiler,
    fmt::{CodeWriter, FormattingConfig},
    frontend::testing::workspace_from_modules,
};

fn format_proc(source: &str, proc_name: &str) -> String {
    let ws = workspace_from_modules(&[("word_mem_stack_ops", source)]);
    let fq_name = format!("word_mem_stack_ops::{proc_name}");
    let result = Decompiler::new(&ws)
        .decompile_proc(&fq_name)
        .expect("decompilation should succeed");

    let mut writer = CodeWriter::with_config(FormattingConfig::new().with_color(false));
    writer.register_loop_vars(result.stmts());
    for stmt in result.stmts() {
        writer.write(stmt.clone());
    }
    writer.finish()
}

#[test]
fn formats_word_memory_and_locaddr_ops() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");

    let mem_fmt = format_proc(source, "uses_mem_loadw_and_storew_be");
    assert!(mem_fmt.contains("memory.be["), "{mem_fmt}");
    assert!(
        mem_fmt.contains(" = (") && mem_fmt.contains(");"),
        "{mem_fmt}"
    );
    assert!(mem_fmt.contains(") = memory.be["), "{mem_fmt}");

    let local_fmt = format_proc(source, "uses_loc_loadw_be");
    assert!(local_fmt.contains("locals.be[0]"), "{local_fmt}");

    let addr_fmt = format_proc(source, "uses_locaddr");
    assert!(addr_fmt.contains("locaddr(0)"), "{addr_fmt}");
}

#[test]
fn formats_scalar_and_le_memory_local_ops_with_bracket_syntax() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");

    let mem_scalar = format_proc(source, "uses_mem_load_and_store");
    assert!(mem_scalar.contains("memory["), "{mem_scalar}");
    assert!(mem_scalar.contains(" = memory["), "{mem_scalar}");

    let mem_le = format_proc(source, "uses_mem_loadw_and_storew_le");
    assert!(mem_le.contains("memory.le["), "{mem_le}");
    assert!(mem_le.contains(") = memory.le["), "{mem_le}");

    let local_scalar = format_proc(source, "uses_loc_load_and_store");
    assert!(local_scalar.contains("locals[0] = "), "{local_scalar}");
    assert!(local_scalar.contains(" = locals[0];"), "{local_scalar}");

    let local_le = format_proc(source, "uses_loc_loadw_le");
    assert!(local_le.contains("locals.le[0]"), "{local_le}");
    assert!(local_le.contains(") = locals.le[0];"), "{local_le}");
}

#[test]
fn formats_u32wrapping_add3_intrinsic() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");
    let formatted = format_proc(source, "uses_u32wrapping_add3");
    assert!(formatted.contains("u32wrapping_add3("), "{formatted}");
}

#[test]
fn formats_u32widening_add3_intrinsic() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");
    let formatted = format_proc(source, "uses_u32widening_add3");
    assert!(formatted.contains("u32widening_add3("), "{formatted}");
}

#[test]
fn formats_u32shift_ops_with_infix_u32_operators() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");

    let imm_fmt = format_proc(source, "uses_u32shift_imm");
    assert!(imm_fmt.contains(">>_u32"), "{imm_fmt}");
    assert!(imm_fmt.contains("<<_u32"), "{imm_fmt}");

    let binary_fmt = format_proc(source, "uses_u32shift_binary");
    assert!(binary_fmt.contains(">>_u32"), "{binary_fmt}");
    assert!(binary_fmt.contains("<<_u32"), "{binary_fmt}");
}

#[test]
fn formats_u32rotr_u32test_and_u32not_with_readable_forms() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");

    let rotr_imm_fmt = format_proc(source, "uses_u32rotr_imm");
    assert!(rotr_imm_fmt.contains("rotr_u32("), "{rotr_imm_fmt}");

    let rotr_binary_fmt = format_proc(source, "uses_u32rotr_binary");
    assert!(rotr_binary_fmt.contains("rotr_u32("), "{rotr_binary_fmt}");

    let test_fmt = format_proc(source, "uses_u32test");
    assert!(test_fmt.contains("is_u32("), "{test_fmt}");

    let not_fmt = format_proc(source, "uses_u32not");
    assert!(not_fmt.contains("not_u32("), "{not_fmt}");
}

#[test]
fn formats_u32widening_add_and_mod_as_intrinsics() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");

    let widening_fmt = format_proc(source, "uses_u32widening_add");
    assert!(widening_fmt.contains("u32widening_add("), "{widening_fmt}");

    let mod_fmt = format_proc(source, "uses_u32mod_imm");
    assert!(mod_fmt.contains("u32mod.8("), "{mod_fmt}");
}

#[test]
fn formats_sdepth_and_decompiles_movdnw() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");

    let sdepth_fmt = format_proc(source, "uses_sdepth");
    assert!(sdepth_fmt.contains("sdepth()"), "{sdepth_fmt}");

    let movdnw2_fmt = format_proc(source, "uses_movdnw2");
    assert!(movdnw2_fmt.contains("return"), "{movdnw2_fmt}");
    assert!(!movdnw2_fmt.contains("movdnw"), "{movdnw2_fmt}");

    let movdnw3_fmt = format_proc(source, "uses_movdnw3");
    assert!(movdnw3_fmt.contains("return"), "{movdnw3_fmt}");
    assert!(!movdnw3_fmt.contains("movdnw"), "{movdnw3_fmt}");
}

#[test]
fn formats_u32_exp_with_infix_operator() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");
    let formatted = format_proc(source, "uses_exp_u32");
    assert!(formatted.contains("^_u32"), "{formatted}");
}

#[test]
fn formats_u32cast_with_readable_parenthesization() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");

    let cast_fmt = format_proc(source, "uses_u32cast");
    assert!(cast_fmt.contains("mod 2^32"), "{cast_fmt}");

    let composite_fmt = format_proc(source, "uses_u32cast_in_composite_expr");
    assert!(composite_fmt.contains("mod 2^32"), "{composite_fmt}");
    assert!(
        composite_fmt.contains(") mod 2^32) + 1"),
        "u32cast in composite expressions should be grouped for readability: {composite_fmt}"
    );
}

#[test]
fn formats_inv_as_unary_field_inverse() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");
    let formatted = format_proc(source, "uses_inv");
    assert!(formatted.contains("inv("), "{formatted}");
}

#[test]
fn formats_u32_assert_and_divmod_imm_as_intrinsics() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");
    let formatted = format_proc(source, "uses_u32assert_and_divmod_imm");
    assert!(formatted.contains("u32assert("), "{formatted}");
    assert!(formatted.contains("u32divmod.4("), "{formatted}");
}

#[test]
fn formats_u32assertw_ext2add_and_is_odd_intrinsics() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");

    let u32assertw_fmt = format_proc(source, "uses_u32assertw");
    assert!(u32assertw_fmt.contains("u32assertw("), "{u32assertw_fmt}");

    let ext2_fmt = format_proc(source, "uses_ext2add");
    assert!(ext2_fmt.contains("ext2add("), "{ext2_fmt}");

    let is_odd_fmt = format_proc(source, "uses_is_odd");
    assert!(is_odd_fmt.contains("is_odd("), "{is_odd_fmt}");
}

#[test]
fn formats_mem_stream_and_adv_pipe_intrinsics() {
    let source = include_str!("fixtures/word_mem_stack_ops.masm");

    let mem_stream_fmt = format_proc(source, "uses_mem_stream");
    assert!(mem_stream_fmt.contains("mem_stream("), "{mem_stream_fmt}");

    let adv_pipe_fmt = format_proc(source, "uses_adv_pipe");
    assert!(adv_pipe_fmt.contains("adv_pipe("), "{adv_pipe_fmt}");
}
