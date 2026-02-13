mod common;

use common::decompile_no_optimizations;
use masm_decompiler::{
    frontend::testing::workspace_from_modules,
    ir::{Expr, Stmt},
};

#[test]
fn while_condition_update_is_modeled_as_loop_carried_value() {
    let ws = workspace_from_modules(&[
        (
            "issue::constants",
            include_str!("fixtures/while_condition_update_constants.masm"),
        ),
        (
            "issue::random_coin",
            include_str!("fixtures/while_condition_update_random_coin.masm"),
        ),
    ]);

    let stmts = decompile_no_optimizations(&ws, "issue::random_coin::generate_z_zN");

    let (cond, phis) = stmts
        .iter()
        .find_map(|stmt| {
            if let Stmt::While { cond, phis, .. } = stmt {
                Some((cond, phis))
            } else {
                None
            }
        })
        .expect("expected while loop in decompiled output");

    let cond_var = match cond {
        Expr::Var(var) => var,
        other => panic!("expected while condition to be a variable, got: {other:?}"),
    };

    let has_condition_phi = phis.iter().any(|phi| &phi.init == cond_var);

    assert!(
        has_condition_phi,
        "expected while condition to be tracked as loop-carried state (phi init).\nCondition: {:?}\nPhis: {:?}\nOutput: {:#?}",
        cond, phis, stmts
    );
}
