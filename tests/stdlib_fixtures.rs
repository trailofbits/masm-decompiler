mod common;

use common::decompile;
use masm_decompiler::frontend::testing::workspace_from_modules;

fn assert_fixture_proc(module_path: &str, source: &str, proc_name: &str) {
    let ws = workspace_from_modules(&[(module_path, source)]);
    let proc_name = proc_name.strip_prefix("r#").unwrap_or(proc_name);
    let fq = format!("{module_path}::{proc_name}");
    let stmts = decompile(&ws, &fq);
    assert!(
        !stmts.is_empty(),
        "decompile of {fq} produced no statements"
    );
}

macro_rules! fixture_module {
    ($tag:ident, $module:expr, $source:expr, [$($proc:ident),* $(,)?]) => {
        mod $tag {
            use super::*;
            $(#[test] fn $proc() { assert_fixture_proc($module, $source, stringify!($proc)); })*
        }
    };
}

fixture_module!(word, "word", include_str!("fixtures/word.masm"), [testz,]);
fixture_module!(
    word_mem_stack_ops,
    "word_mem_stack_ops",
    include_str!("fixtures/word_mem_stack_ops.masm"),
    [
        uses_movupw,
        uses_loc_loadw_be,
        uses_loc_loadw_le,
        uses_loc_load_and_store,
        uses_mem_loadw_and_storew_be,
        uses_mem_loadw_and_storew_le,
        uses_mem_load_and_store,
        uses_swapdw,
        uses_locaddr,
        uses_u32wrapping_add3,
        uses_u32shift_imm,
        uses_u32shift_binary,
        uses_exp_u32,
        uses_u32assert_and_divmod_imm,
        uses_u32assertw,
        uses_ext2add,
        uses_is_odd,
        uses_mem_stream,
        uses_adv_pipe,
    ]
);
#[test]
fn u64_clz_renders_a_public_header() {
    let ws = workspace_from_modules(&[("u64", include_str!("fixtures/u64.masm"))]);
    let proc = Decompiler::new(&ws)
        .decompile_proc("u64::clz")
        .expect("decompilation should succeed");
    let rendered = proc.render(FormattingConfig::new().with_color(false));
    let first_line = rendered.lines().next().unwrap_or_default();
    let add_line = rendered
        .lines()
        .find(|line| line.contains(" + 32;"))
        .expect("clz branch should assign the widened count");
    let else_line = rendered
        .lines()
        .find(|line| line.contains("clz_u32(v_1);"))
        .expect("clz else-branch should assign from the low limb");
    let return_line = rendered
        .lines()
        .find(|line| line.trim_start().starts_with("return "))
        .expect("clz should return the merged result");
    let add_dest = add_line
        .split('=')
        .next()
        .expect("assignment should have a destination")
        .trim();
    let else_dest = else_line
        .split('=')
        .next()
        .expect("assignment should have a destination")
        .trim();
    let return_var = return_line
        .trim()
        .trim_start_matches("return ")
        .trim_end_matches(';')
        .trim();

    assert!(first_line.starts_with("pub proc clz("));
    assert!(first_line.contains(": U32, v_1: U32) -> U32 {"));
    assert!(
        rendered.contains("if (v_1 == 0) {") && add_dest == else_dest && else_dest == return_var,
        "expected lifted branch structure in rendered clz body: {rendered}"
    );
}
