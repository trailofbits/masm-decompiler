mod common;

use common::decompile_no_optimizations;
use masm_decompiler::{frontend::testing::workspace_from_modules, ir::Stmt};

/// Verify that intrinsics use `required_depth` (not `pops`) for the number of
/// arguments, so that passthrough inputs are visible in the decompiled output.
///
/// `mtree_verify` has stack effect `known(0, 0).with_required_depth(10)`:
/// it reads 10 elements `[V, d, i, R]` but modifies none. With the correct
/// lifting, all 10 elements should appear as arguments.
#[test]
fn intrinsic_args_reflect_required_depth() {
    let ws = workspace_from_modules(&[(
        "test_mod",
        r#"
        proc uses_mtree_verify
            push.[5, 6, 7, 8]
            push.0.2
            push.[1, 2, 3, 4]
            mtree_verify
            dropw
            drop
            drop
            dropw
        end
        "#,
    )]);
    let stmts = decompile_no_optimizations(&ws, "test_mod::uses_mtree_verify");

    let intrinsic = stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Intrinsic { intrinsic, .. } if intrinsic.name == "mtree_verify" => {
                Some(intrinsic)
            }
            _ => None,
        })
        .expect("expected mtree_verify intrinsic");

    assert_eq!(
        intrinsic.args.len(),
        10,
        "mtree_verify should have 10 arguments (V₀..V₃, d, i, R₀..R₃), got {}",
        intrinsic.args.len()
    );
    assert_eq!(
        intrinsic.results.len(),
        0,
        "mtree_verify should have 0 results (all passthrough), got {}",
        intrinsic.results.len()
    );
}

/// Verify that exec calls use `required_depth` (not `pops`) for the number of
/// arguments, so that passthrough inputs are visible in the decompiled output.
///
/// The helper procedure `dup.2; add` has composed stack effect
/// `known(1, 1).with_required_depth(3)`: it reads 3 elements but only
/// consumes 1 and produces 1. With the correct lifting, all 3 elements
/// should appear as call arguments.
#[test]
fn exec_call_args_reflect_required_depth() {
    let ws = workspace_from_modules(&[(
        "test_mod",
        r#"
        proc helper
            dup.2
            add
        end

        proc caller
            push.1.2.3
            exec.helper
            drop
            drop
            drop
        end
        "#,
    )]);
    let stmts = decompile_no_optimizations(&ws, "test_mod::caller");

    let call = stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Exec { call, .. } if call.target.ends_with("helper") => Some(call),
            _ => None,
        })
        .expect("expected exec call to helper");

    assert_eq!(
        call.args.len(),
        3,
        "exec.helper should have 3 arguments (required_depth), got {}",
        call.args.len()
    );
    assert_eq!(
        call.results.len(),
        1,
        "exec.helper should have 1 result, got {}",
        call.results.len()
    );
}
