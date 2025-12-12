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
        !structured.iter().any(|s| matches!(s, Stmt::Unknown)),
        "decompile of {fq} produced Unknowns: {structured:#?}"
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
    u64,
    "u64",
    include_str!("fixtures/u64.masm"),
    [
        overflowing_add,
        wrapping_add,
        wrapping_sub,
        overflowing_sub,
        wrapping_mul,
        overflowing_mul,
        lt,
        gt,
        lte,
        gte,
        eq,
        neq,
        eqz,
        min,
        max,
        div,
        r#mod,
        divmod,
        and,
        or,
        xor,
        shl,
        shr,
        rotl,
        rotr,
        clz,
        ctz,
        clo,
        cto,
    ]
);

fixture_module!(
    u256,
    "u256",
    include_str!("fixtures/u256.masm"),
    [
        wrapping_add,
        wrapping_sub,
        and,
        or,
        xor,
        eqz,
        eq,
        wrapping_mul,
    ]
);

fixture_module!(
    word,
    "word",
    include_str!("fixtures/word.masm"),
    [
        reverse,
        store_word_u32s_le,
        eqz,
        testz,
        gt,
        gte,
        lt,
        lte,
        eq,
        test_eq,
    ]
);
