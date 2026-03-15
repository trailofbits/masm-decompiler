mod common;

use common::decompile_no_optimizations;
use masm_decompiler::{frontend::testing::workspace_from_modules, ir::Stmt};

/// Verify that mtree_get surfaces the Merkle root as both an input and output.
///
/// The mtree_get instruction takes 6 inputs (depth, index, R₀..R₃) and
/// produces 8 outputs (V₀..V₃, R₀..R₃). The root R is left unchanged on
/// the stack but is still a genuine input to the operation.
#[test]
fn mtree_get_shows_root_as_argument() {
    let ws = workspace_from_modules(&[(
        "mtree_mod",
        r#"
        proc uses_mtree_get
            push.[1, 2, 3, 4]
            push.0.2
            mtree_get
            dropw
            dropw
        end
        "#,
    )]);
    let stmts = decompile_no_optimizations(&ws, "mtree_mod::uses_mtree_get");

    let intrinsic = stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Intrinsic { intrinsic, .. } if intrinsic.name == "mtree_get" => Some(intrinsic),
            _ => None,
        })
        .expect("expected mtree_get intrinsic");

    assert_eq!(
        intrinsic.args.len(),
        6,
        "mtree_get should have 6 arguments (depth, index, R₀..R₃), got {}",
        intrinsic.args.len()
    );
    assert_eq!(
        intrinsic.results.len(),
        8,
        "mtree_get should have 8 results (V₀..V₃, R₀..R₃), got {}",
        intrinsic.results.len()
    );
}

/// Verify that the mtree_get fixture decompiles successfully with all
/// three Merkle tree lookups.
#[test]
fn mtree_get_fixture_decompiles_successfully() {
    let ws = workspace_from_modules(&[("mtree_mod", include_str!("fixtures/mtree_get.masm"))]);
    let stmts = decompile_no_optimizations(&ws, "mtree_mod::test_mtree_get");

    let mtree_get_count = stmts
        .iter()
        .filter(|s| matches!(s, Stmt::Intrinsic { intrinsic, .. } if intrinsic.name == "mtree_get"))
        .count();

    assert_eq!(
        mtree_get_count, 3,
        "expected 3 mtree_get calls, got {mtree_get_count}"
    );
}
