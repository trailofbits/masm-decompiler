mod common;

use std::fs;
use std::path::PathBuf;
use std::time::{SystemTime, UNIX_EPOCH};

use common::decompile;
use masm_decompiler::{
    decompile::Decompiler,
    fmt::FormattingConfig,
    frontend::{LibraryRoot, Workspace, testing::workspace_from_modules},
    symbol::path::SymbolPath,
    types::{InferredType, TypeRequirement},
};

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

/// Temporary stdlib fixture root on disk for provenance-gated tests.
struct TempStdlibFixture {
    root: PathBuf,
}

impl TempStdlibFixture {
    /// Create a temporary trusted `miden::core` root with one module file.
    fn new(module_relative: &str, source: &str) -> Self {
        let unique = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system time should be after unix epoch")
            .as_nanos();
        let root = std::env::temp_dir().join(format!(
            "masm-decompiler-stdlib-fixture-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir_all(&root).expect("create temp stdlib root");
        fs::write(
            root.join("miden-project.toml"),
            "[lib]\nnamespace = \"miden::core\"\n",
        )
        .expect("write miden-project.toml");

        let module_path = root.join(module_relative);
        if let Some(parent) = module_path.parent() {
            fs::create_dir_all(parent).expect("create module directory");
        }
        fs::write(&module_path, source).expect("write module fixture");

        Self { root }
    }

    /// Build a workspace that loads this fixture under the `miden::core` namespace.
    fn workspace(&self, module_path: &str, trusted: bool) -> Workspace {
        let root = if trusted {
            LibraryRoot::trusted_stdlib("miden::core", self.root.clone())
        } else {
            LibraryRoot::new("miden::core", self.root.clone())
        };
        let mut ws = Workspace::new(vec![root]);
        ws.load_module_by_path(module_path)
            .expect("trusted stdlib fixture module should load");
        ws
    }
}

impl Drop for TempStdlibFixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
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
    [testz, test_eq,]
);
fixture_module!(
    u64,
    "u64",
    include_str!("fixtures/u64.masm"),
    [clz, ctz, clo, cto]
);
fixture_module!(
    u128,
    "u128",
    include_str!("fixtures/u128.masm"),
    [wrapping_mul]
);
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

#[test]
fn u64_shift_and_rotate_outputs_stay_u32() {
    let fixture = TempStdlibFixture::new("math/u64.masm", include_str!("fixtures/u64.masm"));
    let ws = fixture.workspace("miden::core::math::u64", true);
    let decompiler = Decompiler::new(&ws);

    for proc_name in [
        "miden::core::math::u64::shr",
        "miden::core::math::u64::rotl",
        "miden::core::math::u64::rotr",
    ] {
        let proc = decompiler
            .decompile_proc(proc_name)
            .unwrap_or_else(|err| panic!("decompilation should succeed for {proc_name}: {err}"));
        let rendered = proc.render(FormattingConfig::new().with_color(false));
        let first_line = rendered.lines().next().unwrap_or_default();
        assert!(
            first_line.contains("-> (U32, U32) {"),
            "expected {proc_name} to keep u64 limb outputs typed, got: {first_line}",
        );
    }
}

#[test]
fn u64_rotr_keeps_exact_u32_inputs() {
    let fixture = TempStdlibFixture::new("math/u64.masm", include_str!("fixtures/u64.masm"));
    let ws = fixture.workspace("miden::core::math::u64", true);
    let proc = Decompiler::new(&ws)
        .decompile_proc("miden::core::math::u64::rotr")
        .expect("decompilation should succeed");
    let rendered = proc.render(FormattingConfig::new().with_color(false));
    let first_line = rendered.lines().next().unwrap_or_default();

    assert_eq!(
        first_line, "pub proc rotr(v_0: U32, v_1: U32, v_2: U32) -> (U32, U32) {",
        "expected rotr to keep exact U32 limb inputs, got: {first_line}",
    );
}

#[test]
fn u128_wrapping_mul_keeps_u128_limb_header() {
    let fixture = TempStdlibFixture::new("math/u128.masm", include_str!("fixtures/u128.masm"));
    let ws = fixture.workspace("miden::core::math::u128", true);
    let proc = Decompiler::new(&ws)
        .decompile_proc("miden::core::math::u128::wrapping_mul")
        .expect("decompilation should succeed");
    let rendered = proc.render(FormattingConfig::new().with_color(false));
    let first_line = rendered.lines().next().unwrap_or_default();
    assert!(
        first_line.starts_with(
            "pub proc wrapping_mul(v_0: U32, v_1: U32, v_2: U32, v_3: U32, v_4: U32, v_5: U32, v_6: U32, v_7: U32) -> (U32, U32, U32, U32) {"
        ),
        "expected u128 wrapping_mul to keep exact U32 limb typing, got: {first_line}",
    );
}

#[test]
fn word_testz_preserves_word_outputs() {
    let fixture = TempStdlibFixture::new("word.masm", include_str!("fixtures/word.masm"));
    let ws = fixture.workspace("miden::core::word", true);
    let proc = Decompiler::new(&ws)
        .decompile_proc("miden::core::word::testz")
        .expect("decompilation should succeed");
    let rendered = proc.render(FormattingConfig::new().with_color(false));
    let first_line = rendered.lines().next().unwrap_or_default();

    assert!(
        first_line.starts_with(
            "pub proc testz(v_0: Felt, v_1: Felt, v_2: Felt, v_3: Felt) -> (Bool, Felt, Felt, Felt, Felt) {"
        ),
        "expected testz to preserve the input word in its public header, got: {first_line}",
    );
    assert!(
        rendered.contains("= v_i;") && rendered.contains("== 0);"),
        "expected rendered testz body to walk loop-indexed input limbs: {rendered}",
    );
}

#[test]
fn word_test_eq_preserves_both_words() {
    let fixture = TempStdlibFixture::new("word.masm", include_str!("fixtures/word.masm"));
    let ws = fixture.workspace("miden::core::word", true);
    let proc = Decompiler::new(&ws)
        .decompile_proc("miden::core::word::test_eq")
        .expect("decompilation should succeed");
    let rendered = proc.render(FormattingConfig::new().with_color(false));
    let first_line = rendered.lines().next().unwrap_or_default();

    assert!(
        first_line.starts_with(
            "pub proc test_eq(v_0: Felt, v_1: Felt, v_2: Felt, v_3: Felt, v_4: Felt, v_5: Felt, v_6: Felt, v_7: Felt) -> (Bool, Felt, Felt, Felt, Felt, Felt, Felt, Felt, Felt) {"
        ),
        "expected test_eq to preserve both words in its public header, got: {first_line}",
    );
}

#[test]
fn u64_eq_family_keeps_exact_u32_inputs() {
    let fixture = TempStdlibFixture::new("math/u64.masm", include_str!("fixtures/u64.masm"));
    let ws = fixture.workspace("miden::core::math::u64", true);

    for (proc_name, expected_prefix) in [
        (
            "miden::core::math::u64::eq",
            "pub proc eq(v_0: U32, v_1: U32, v_2: U32, v_3: U32) -> Bool {",
        ),
        (
            "miden::core::math::u64::neq",
            "pub proc neq(v_0: U32, v_1: U32, v_2: U32, v_3: U32) -> Bool {",
        ),
    ] {
        let proc = Decompiler::new(&ws)
            .decompile_proc(proc_name)
            .expect("decompilation should succeed");
        let rendered = proc.render(FormattingConfig::new().with_color(false));
        let first_line = rendered.lines().next().unwrap_or_default();

        assert_eq!(
            first_line, expected_prefix,
            "expected exact U32 limb header for {proc_name}, got: {first_line}",
        );
    }

    let eqz = Decompiler::new(&ws)
        .decompile_proc("miden::core::math::u64::eqz")
        .expect("decompilation should succeed");
    let eqz_line = eqz
        .render(FormattingConfig::new().with_color(false))
        .lines()
        .next()
        .unwrap_or_default()
        .to_string();
    assert_eq!(
        eqz_line, "pub proc eqz(v_0: Felt, v_1: Felt) -> Bool {",
        "arity-mismatched u64::eqz fixture declaration should stay broad, got: {eqz_line}",
    );
}

#[test]
fn larger_eq_helpers_keep_exact_u32_inputs_when_declared_arity_matches() {
    let u256_fixture = TempStdlibFixture::new("math/u256.masm", include_str!("fixtures/u256.masm"));
    let u256_ws = u256_fixture.workspace("miden::core::math::u256", true);
    let u256_eq = Decompiler::new(&u256_ws)
        .decompile_proc("miden::core::math::u256::eq")
        .expect("decompilation should succeed");
    let u256_eq_line = u256_eq
        .render(FormattingConfig::new().with_color(false))
        .lines()
        .next()
        .unwrap_or_default()
        .to_string();
    assert_eq!(
        u256_eq_line,
        "pub proc eq(v_0: U32, v_1: U32, v_2: U32, v_3: U32, v_4: U32, v_5: U32, v_6: U32, v_7: U32, v_8: U32, v_9: U32, v_10: U32, v_11: U32, v_12: U32, v_13: U32, v_14: U32, v_15: U32) -> Bool {",
        "expected exact U32 limb header for u256::eq, got: {u256_eq_line}",
    );

    let u256_eqz = Decompiler::new(&u256_ws)
        .decompile_proc("miden::core::math::u256::eqz")
        .expect("decompilation should succeed");
    let u256_eqz_line = u256_eqz
        .render(FormattingConfig::new().with_color(false))
        .lines()
        .next()
        .unwrap_or_default()
        .to_string();
    assert_eq!(
        u256_eqz_line,
        "pub proc eqz(v_0: Felt, v_1: Felt, v_2: Felt, v_3: Felt, v_4: Felt, v_5: Felt, v_6: Felt, v_7_1: Felt) -> Bool {",
        "arity-mismatched u256::eqz declaration should stay broad, got: {u256_eqz_line}",
    );
}

#[test]
fn u256_overflowing_sub_keeps_borrow_then_limbs() {
    let fixture = TempStdlibFixture::new("math/u256.masm", include_str!("fixtures/u256.masm"));
    let ws = fixture.workspace("miden::core::math::u256", true);
    let proc = Decompiler::new(&ws)
        .decompile_proc("miden::core::math::u256::overflowing_sub")
        .expect("decompilation should succeed");
    let rendered = proc.render(FormattingConfig::new().with_color(false));
    let first_line = rendered.lines().next().unwrap_or_default();

    assert!(
        first_line.contains("-> (Bool, U32, U32, U32, U32, U32, U32, U32, U32) {"),
        "expected overflowing_sub to keep borrow-first output typing, got: {first_line}",
    );
}

#[test]
fn u256_wrapping_mul_hides_internal_frame_inputs() {
    let fixture = TempStdlibFixture::new("math/u256.masm", include_str!("fixtures/u256.masm"));
    let ws = fixture.workspace("miden::core::math::u256", true);
    let decompiler = Decompiler::new(&ws);
    let proc = decompiler
        .decompile_proc("miden::core::math::u256::wrapping_mul")
        .expect("decompilation should succeed");
    let rendered = proc.render(FormattingConfig::new().with_color(false));
    let first_line = rendered.lines().next().unwrap_or_default();

    assert!(
        first_line.starts_with("pub proc wrapping_mul(v_0:")
            && first_line.contains("v_15:")
            && first_line.ends_with("-> (U32, U32, U32, U32, U32, U32, U32, U32) {"),
        "expected wrapping_mul to expose only its semantic 16-limb public inputs and u32 outputs, got: {first_line}",
    );
    assert!(
        !first_line.contains("v_16:"),
        "wrapping_mul should not expose hidden lifting scaffolding in its header: {first_line}",
    );
    assert_eq!(proc.inputs(), Some(16), "{first_line}");

    let summary = proc
        .type_summary
        .as_ref()
        .expect("wrapping_mul should have a type summary");
    assert_eq!(summary.inputs.len(), 16, "{summary:?}");
    assert!(
        summary
            .inputs
            .iter()
            .all(|input| *input == TypeRequirement::U32),
        "wrapping_mul should keep its visible public inputs typed as U32 limbs: {summary:?}",
    );
    assert!(
        summary
            .outputs
            .iter()
            .all(|output| *output == InferredType::U32),
        "wrapping_mul outputs should stay typed as U32 limbs: {summary:?}",
    );

    let diagnostics = decompiler
        .type_diagnostics()
        .get(&SymbolPath::new("miden::core::math::u256::wrapping_mul"))
        .cloned()
        .unwrap_or_default();
    for hidden_input in 17..=32 {
        let needle = format!("public procedure input {hidden_input} ");
        assert!(
            diagnostics
                .iter()
                .all(|diag| !diag.message.contains(&needle)),
            "wrapping_mul diagnostics should not mention hidden input {hidden_input}: {diagnostics:?}",
        );
    }
}

#[test]
fn canonical_stdlib_path_without_trusted_root_is_not_refined() {
    let fixture = TempStdlibFixture::new("math/u64.masm", include_str!("fixtures/u64.masm"));
    let ws = fixture.workspace("miden::core::math::u64", false);
    let proc = Decompiler::new(&ws)
        .decompile_proc("miden::core::math::u64::shr")
        .expect("decompilation should succeed");
    let rendered = proc.render(FormattingConfig::new().with_color(false));
    let first_line = rendered.lines().next().unwrap_or_default();

    assert!(
        !first_line.contains("-> (U32, U32) {"),
        "untrusted canonical namespace should not trigger stdlib-only refinement: {first_line}",
    );
}
