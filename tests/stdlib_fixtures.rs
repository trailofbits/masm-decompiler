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
