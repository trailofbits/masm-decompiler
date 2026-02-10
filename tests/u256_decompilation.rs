//! Targeted regression tests for u256 decompilation.

mod common;

use common::{
    collect_used_defined_value_ids, const_index, decompile_no_optimizations, linear_index,
};
use masm_decompiler::fmt::{CodeWriter, FormattingConfig};
use masm_decompiler::frontend::testing::workspace_from_modules;
use masm_decompiler::ir::{BinOp, Expr, Stmt, ValueId, Var, VarBase};
use std::collections::HashSet;

/// Helper to format decompiled output as a string for debugging (without colors).
fn format_output(stmts: &[Stmt]) -> String {
    let config = FormattingConfig::new().with_color(false);
    let mut writer = CodeWriter::with_config(config);
    writer.register_loop_vars(stmts);
    for stmt in stmts {
        writer.write(stmt.clone());
    }
    writer.finish()
}

/// Collect value identifiers that originate from procedure inputs.
fn input_value_ids(stmts: &[Stmt]) -> HashSet<ValueId> {
    let (used, defined) = collect_used_defined_value_ids(stmts);
    used.difference(&defined).cloned().collect()
}

/// Extract an assignment of the form `dest = var == 0`.
fn eq_zero_assignment(stmt: &Stmt) -> Option<(Var, Var)> {
    let Stmt::Assign { dest, expr, .. } = stmt else {
        return None;
    };
    let Expr::Binary(BinOp::Eq, lhs, rhs) = expr else {
        return None;
    };
    match (lhs.as_ref(), rhs.as_ref()) {
        (Expr::Var(var), Expr::Constant(c)) if c.is_zero() => Some((dest.clone(), var.clone())),
        (Expr::Constant(c), Expr::Var(var)) if c.is_zero() => Some((dest.clone(), var.clone())),
        _ => None,
    }
}

/// Extract an assignment of the form `dest = lhs and rhs`.
fn and_assignment(stmt: &Stmt) -> Option<(Var, Var, Var)> {
    let Stmt::Assign { dest, expr, .. } = stmt else {
        return None;
    };
    let Expr::Binary(BinOp::And, lhs, rhs) = expr else {
        return None;
    };
    match (lhs.as_ref(), rhs.as_ref()) {
        (Expr::Var(lhs_var), Expr::Var(rhs_var)) => {
            Some((dest.clone(), lhs_var.clone(), rhs_var.clone()))
        }
        _ => None,
    }
}

/// Find the first repeat loop and return its depth, count, and body.
fn find_repeat_loop<'a>(stmts: &'a [Stmt]) -> Option<(usize, usize, &'a [Stmt])> {
    for stmt in stmts {
        if let Stmt::Repeat {
            loop_var,
            loop_count,
            body,
            ..
        } = stmt
        {
            return Some((loop_var.loop_depth, *loop_count, body));
        }
    }
    None
}

/// U256 `or` should pair inputs (0..7) with (8..15) and return all results.
#[test]
fn u256_or_pairs_inputs_and_returns_results() {
    let ws = workspace_from_modules(&[("u256", include_str!("fixtures/u256.masm"))]);
    let structured = decompile_no_optimizations(&ws, "u256::or");
    let output = format_output(&structured);
    eprintln!("Output for u256::or:\n{}", output);

    let input_ids = input_value_ids(&structured);

    let mut or_assignments = Vec::new();
    for stmt in &structured {
        if let Stmt::Assign { dest, expr, .. } = stmt {
            if let Expr::Binary(BinOp::U32Or, lhs, rhs) = expr {
                or_assignments.push((dest.clone(), lhs.as_ref().clone(), rhs.as_ref().clone()));
            }
        }
    }

    assert_eq!(
        or_assignments.len(),
        8,
        "u256::or should contain exactly 8 u32 or assignments. Output:\n{}",
        output
    );

    let mut dests = Vec::new();
    let mut seen_pairs = HashSet::new();
    for (dest, lhs, rhs) in or_assignments {
        let (lhs_var, rhs_var) = match (lhs, rhs) {
            (Expr::Var(lhs_var), Expr::Var(rhs_var)) => (lhs_var, rhs_var),
            _ => panic!("u256::or operands should be variables. Output:\n{}", output),
        };

        for operand in [&lhs_var, &rhs_var] {
            let operand_id = operand
                .base
                .value_id()
                .expect("u256::or operands should have value ids");
            assert!(
                input_ids.contains(&operand_id),
                "u256::or operands should be inputs, not computed values. Output:\n{}",
                output
            );
        }

        let lhs_index = const_index(&lhs_var).expect("expected constant lhs subscript");
        let rhs_index = const_index(&rhs_var).expect("expected constant rhs subscript");
        let mut indices = [lhs_index, rhs_index];
        indices.sort();
        assert!(
            indices[1] - indices[0] == 8,
            "u256::or operands should pair values 8 apart, got {:?}. Output:\n{}",
            indices,
            output
        );
        assert!(
            seen_pairs.insert(indices),
            "duplicate operand pair {:?} in u256::or. Output:\n{}",
            indices,
            output
        );

        dests.push(dest);
    }

    assert_eq!(
        seen_pairs.len(),
        8,
        "u256::or should cover 8 distinct operand pairs. Output:\n{}",
        output
    );

    let return_vars = structured
        .iter()
        .find_map(|stmt| match stmt {
            Stmt::Return { values, .. } => Some(values),
            _ => None,
        })
        .expect("expected return statement");

    assert_eq!(
        return_vars.len(),
        8,
        "u256::or should return 8 values. Output:\n{}",
        output
    );

    let dest_set: HashSet<Var> = dests.into_iter().collect();
    let return_set: HashSet<Var> = return_vars.iter().cloned().collect();
    assert_eq!(
        dest_set, return_set,
        "u256::or return values should match assignment destinations. Output:\n{}",
        output
    );
}

/// U256 `eqz` should compare each input against zero and fold with a boolean accumulator.
#[test]
fn u256_eqz_loop_uses_boolean_accumulator_and_returns_it() {
    let ws = workspace_from_modules(&[("u256", include_str!("fixtures/u256.masm"))]);
    let stmts = decompile_no_optimizations(&ws, "u256::eqz");
    let output = format_output(&stmts);
    eprintln!("Output for u256::eqz:\n{}", output);

    let input_ids = input_value_ids(&stmts);

    let mut pre_loop_eq = None;
    for stmt in &stmts {
        if matches!(stmt, Stmt::Repeat { .. }) {
            break;
        }
        if let Some((dest, input)) = eq_zero_assignment(&stmt) {
            pre_loop_eq = Some((dest, input));
        }
    }

    let (pre_loop_eq_dest, _pre_loop_eq_input) =
        pre_loop_eq.expect("expected initial eq.0 before repeat loop");
    let pre_loop_eq_id = pre_loop_eq_dest
        .base
        .value_id()
        .expect("pre-loop eq dest should have value id");

    let (loop_depth, loop_count, body) =
        find_repeat_loop(&stmts).expect("expected repeat loop in u256::eqz");
    assert_eq!(
        loop_count, 7,
        "u256::eqz should repeat 7 times. Output:\n{}",
        output
    );

    let mut loop_eq = None;
    let mut loop_and = None;
    for stmt in body {
        if let Some((dest, input)) = eq_zero_assignment(stmt) {
            loop_eq = Some((dest, input));
        }
        if let Some((dest, lhs, rhs)) = and_assignment(stmt) {
            loop_and = Some((dest, lhs, rhs));
        }
    }

    let (loop_eq_dest, loop_eq_input) = loop_eq.expect("expected eq.0 inside repeat loop");
    let (loop_and_dest, loop_and_lhs, loop_and_rhs) =
        loop_and.expect("expected and inside repeat loop");

    let loop_and_index =
        const_index(&loop_and_dest).expect("loop accumulator should have constant subscript");
    assert_eq!(
        loop_and_index, 7,
        "loop accumulator should be the v_7 slot. Output:\n{}",
        output
    );

    let loop_eq_input_index =
        linear_index(&loop_eq_input).expect("loop eq input should be indexed by the loop counter");
    assert_eq!(
        loop_eq_input.stack_depth, 6,
        "loop eq should compare the v_6 slot against zero. Output:\n{}",
        output
    );
    assert_eq!(
        loop_eq_input_index.base, 6,
        "loop eq should index the v_6 slot across iterations. Output:\n{}",
        output
    );
    assert_eq!(
        loop_eq_input_index.step, -1,
        "loop eq should iterate downward over v_6..v_0. Output:\n{}",
        output
    );
    assert_eq!(
        loop_eq_input_index.loop_depth, loop_depth,
        "loop eq should use the repeat loop counter. Output:\n{}",
        output
    );
    if let Some(loop_eq_input_id) = loop_eq_input.base.value_id() {
        assert!(
            input_ids.contains(&loop_eq_input_id),
            "loop eq should compare an input word against zero. Output:\n{}",
            output
        );
    }

    let (_acc_var, eq_var) = if const_index(&loop_and_lhs) == Some(7) {
        (&loop_and_lhs, &loop_and_rhs)
    } else if const_index(&loop_and_rhs) == Some(7) {
        (&loop_and_rhs, &loop_and_lhs)
    } else {
        panic!(
            "loop and should use the v_7 accumulator slot. Output:\n{}",
            output
        );
    };

    let eq_index = linear_index(eq_var).unwrap_or_else(|| {
        panic!(
            "loop and should combine against v_(6 - i). Output:\n{}",
            output
        )
    });
    assert_eq!(
        eq_index.base, 6,
        "loop and should combine v_7 accumulator with v_(6 - i) eq result. Output:\n{}",
        output
    );
    assert_eq!(
        eq_index.step, -1,
        "loop and should iterate downward over v_6..v_0. Output:\n{}",
        output
    );
    assert_eq!(
        eq_index.loop_depth, loop_depth,
        "loop and should use the repeat loop counter. Output:\n{}",
        output
    );

    let loop_eq_id = loop_eq_dest
        .base
        .value_id()
        .expect("loop eq dest should have value id");
    let loop_and_id = loop_and_dest
        .base
        .value_id()
        .expect("loop and dest should have value id");
    let repeat_phis = stmts
        .iter()
        .find_map(|stmt| match stmt {
            Stmt::Repeat { phis, .. } => Some(phis),
            _ => None,
        })
        .expect("expected repeat loop in u256::eqz");
    let acc_phi = repeat_phis
        .iter()
        .find(|phi| const_index(&phi.dest) == Some(7))
        .expect("expected accumulator loop phi for v_7");
    let acc_phi_id = acc_phi
        .dest
        .base
        .value_id()
        .expect("accumulator phi dest should have value id");
    assert_eq!(
        acc_phi
            .init
            .base
            .value_id()
            .expect("accumulator phi init should have value id"),
        pre_loop_eq_id,
        "accumulator phi should start from the pre-loop eq result. Output:\n{}",
        output
    );
    assert_eq!(
        acc_phi
            .step
            .base
            .value_id()
            .expect("accumulator phi step should have value id"),
        loop_and_id,
        "accumulator phi should step from the loop and result. Output:\n{}",
        output
    );

    let and_operands = [&loop_and_lhs, &loop_and_rhs];
    assert!(
        and_operands
            .iter()
            .any(|var| var.base.value_id() == Some(loop_eq_id)),
        "loop and should use the eq.0 result. Output:\n{}",
        output
    );

    let mut bool_defs = HashSet::new();
    bool_defs.insert(pre_loop_eq_id);
    bool_defs.insert(loop_eq_id);
    bool_defs.insert(loop_and_id);
    bool_defs.insert(acc_phi_id);

    for operand in and_operands {
        let is_input = operand
            .base
            .value_id()
            .map_or(false, |id| input_ids.contains(&id));
        assert!(
            !is_input,
            "loop and should not consume raw input words. Output:\n{}",
            output
        );

        let is_bool = operand
            .base
            .value_id()
            .map_or(false, |id| bool_defs.contains(&id));
        let is_loop_input = matches!(operand.base, VarBase::LoopInput { .. });
        assert!(
            is_bool || is_loop_input,
            "loop and operands should be boolean values. Output:\n{}",
            output
        );
    }

    let accumulator_operand = if loop_and_lhs.base.value_id() == Some(loop_eq_id) {
        &loop_and_rhs
    } else if loop_and_rhs.base.value_id() == Some(loop_eq_id) {
        &loop_and_lhs
    } else {
        panic!("loop and does not use the eq result");
    };
    assert_eq!(
        const_index(accumulator_operand),
        Some(7),
        "loop and should combine against the accumulator slot (v_7). Output:\n{}",
        output
    );

    let return_vars = stmts
        .iter()
        .find_map(|stmt| match stmt {
            Stmt::Return { values, .. } => Some(values),
            _ => None,
        })
        .expect("expected return statement");
    assert_eq!(
        return_vars.len(),
        1,
        "u256::eqz should return a single value. Output:\n{}",
        output
    );
    let return_id = return_vars[0]
        .base
        .value_id()
        .expect("u256::eqz return should have value id");
    assert_eq!(
        return_id, acc_phi_id,
        "u256::eqz should return the accumulated boolean. Output:\n{}",
        output
    );
}
