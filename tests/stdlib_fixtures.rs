mod common;

use common::decompile;
use masm_decompiler::{frontend::testing::workspace_from_modules, ssa::Stmt};

fn assert_fixture_proc(module_path: &str, source: &str, proc_name: &str) {
    let ws = workspace_from_modules(&[(module_path, source)]);
    let proc_name = proc_name.strip_prefix("r#").unwrap_or(proc_name);
    let fq = format!("{module_path}::{proc_name}");
    let structured = decompile(&ws, &fq, module_path);
    assert!(
        !structured.is_empty(),
        "decompile of {fq} produced no statements"
    );
    assert!(
        !structured.iter().any(|s| matches!(s, Stmt::Inst(_))),
        "decompile of {fq} produced raw insts: {structured:#?}"
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

fixture_module!(
    word,
    "word",
    include_str!("fixtures/word.masm"),
    [
        testz,
    ]
);
