//! Tests for repeat loop decompilation with correct subscript assignment.

mod common;

use common::{decompile, decompile_no_optimizations, decompile_no_propagation};
use masm_decompiler::fmt::{CodeWriter, FormattingConfig};
use masm_decompiler::frontend::testing::workspace_from_modules;
use masm_decompiler::ir::{BinOp, Expr, IndexExpr, Stmt, ValueId, Var};
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

/// Extract the destination subscript from the binary operation inside a repeat loop.
/// Skips carrier assignments (simple var copies) and finds the actual computation.
fn loop_dest_subscript(stmts: &[Stmt]) -> Option<IndexExpr> {
    for stmt in stmts {
        if let Stmt::Repeat { body, .. } = stmt {
            for inner in body {
                if let Stmt::Assign { dest, expr } = inner {
                    // Skip carrier assignments (Expr::Var), find binary operations
                    if matches!(expr, Expr::Binary(..)) {
                        return Some(dest.subscript.clone());
                    }
                }
            }
        }
    }
    None
}

/// Extract the destination variable from the binary operation inside a repeat loop.
fn loop_dest_var(stmts: &[Stmt]) -> Option<Var> {
    for stmt in stmts {
        if let Stmt::Repeat { body, .. } = stmt {
            for inner in body {
                if let Stmt::Assign { dest, expr } = inner {
                    if matches!(expr, Expr::Binary(..)) {
                        return Some(dest.clone());
                    }
                }
            }
        }
    }
    None
}

fn subscript_has_loop_var(expr: &IndexExpr) -> bool {
    match expr {
        IndexExpr::LoopVar(_) => true,
        IndexExpr::Add(a, b) | IndexExpr::Mul(a, b) => {
            subscript_has_loop_var(a) || subscript_has_loop_var(b)
        }
        IndexExpr::Const(_) => false,
    }
}

/// Extract the constant base from a subscript expression, if present.
fn subscript_base(expr: &IndexExpr) -> Option<i64> {
    match expr {
        IndexExpr::Const(value) => Some(*value),
        IndexExpr::Add(lhs, rhs) => match (&**lhs, &**rhs) {
            (IndexExpr::Const(value), _) => Some(*value),
            (_, IndexExpr::Const(value)) => Some(*value),
            _ => None,
        },
        _ => None,
    }
}

/// Check if any variable has a negative constant subscript.
fn has_negative_subscript(stmts: &[Stmt]) -> bool {
    fn check_stmt(stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Assign { dest, .. } => {
                matches!(dest.subscript, IndexExpr::Const(n) if n < 0)
            }
            Stmt::Repeat { body, .. } | Stmt::While { body, .. } => body.iter().any(check_stmt),
            Stmt::If {
                then_body,
                else_body,
                ..
            } => then_body.iter().any(check_stmt) || else_body.iter().any(check_stmt),
            _ => false,
        }
    }
    stmts.iter().any(check_stmt)
}

/// Collect all used and defined value identifiers in structured statements.
fn collect_used_defined_ids(stmts: &[Stmt]) -> (HashSet<ValueId>, HashSet<ValueId>) {
    let mut used = HashSet::new();
    let mut defined = HashSet::new();
    for stmt in stmts {
        collect_stmt_ids(stmt, &mut used, &mut defined);
    }
    (used, defined)
}

/// Record the value identifier for a variable if it is value-based.
fn record_var_id(var: &Var, ids: &mut HashSet<ValueId>) {
    if let Some(id) = var.base.value_id() {
        ids.insert(id);
    }
}

/// Collect used and defined value identifiers from a statement.
fn collect_stmt_ids(stmt: &Stmt, used: &mut HashSet<ValueId>, defined: &mut HashSet<ValueId>) {
    match stmt {
        Stmt::Assign { dest, expr } => {
            record_var_id(dest, defined);
            collect_expr_ids(expr, used);
        }
        Stmt::MemLoad(load) => {
            for v in &load.address {
                record_var_id(v, used);
            }
            for v in &load.outputs {
                record_var_id(v, defined);
            }
        }
        Stmt::MemStore(store) => {
            for v in &store.address {
                record_var_id(v, used);
            }
            for v in &store.values {
                record_var_id(v, used);
            }
        }
        Stmt::AdvLoad(load) => {
            for v in &load.outputs {
                record_var_id(v, defined);
            }
        }
        Stmt::AdvStore(store) => {
            for v in &store.values {
                record_var_id(v, used);
            }
        }
        Stmt::LocalLoad(load) => {
            for v in &load.outputs {
                record_var_id(v, defined);
            }
        }
        Stmt::LocalStore(store) => {
            for v in &store.values {
                record_var_id(v, used);
            }
        }
        Stmt::LocalStoreW(store) => {
            for v in &store.values {
                record_var_id(v, used);
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in &call.args {
                record_var_id(v, used);
            }
            for v in &call.results {
                record_var_id(v, defined);
            }
        }
        Stmt::DynCall { args, results } => {
            for v in args {
                record_var_id(v, used);
            }
            for v in results {
                record_var_id(v, defined);
            }
        }
        Stmt::Intrinsic(intrinsic) => {
            for v in &intrinsic.args {
                record_var_id(v, used);
            }
            for v in &intrinsic.results {
                record_var_id(v, defined);
            }
        }
        Stmt::Repeat { body, phis, .. } => {
            for phi in phis {
                record_var_id(&phi.dest, defined);
                record_var_id(&phi.init, used);
                record_var_id(&phi.step, used);
            }
            for stmt in body {
                collect_stmt_ids(stmt, used, defined);
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            phis,
        } => {
            collect_expr_ids(cond, used);
            for phi in phis {
                record_var_id(&phi.dest, defined);
                record_var_id(&phi.then_var, used);
                record_var_id(&phi.else_var, used);
            }
            for stmt in then_body {
                collect_stmt_ids(stmt, used, defined);
            }
            for stmt in else_body {
                collect_stmt_ids(stmt, used, defined);
            }
        }
        Stmt::While { cond, body, phis } => {
            collect_expr_ids(cond, used);
            for phi in phis {
                record_var_id(&phi.dest, defined);
                record_var_id(&phi.init, used);
                record_var_id(&phi.step, used);
            }
            for stmt in body {
                collect_stmt_ids(stmt, used, defined);
            }
        }
        Stmt::Return(vars) => {
            for v in vars {
                record_var_id(v, used);
            }
        }
    }
}

/// Collect used value identifiers from an expression.
fn collect_expr_ids(expr: &Expr, used: &mut HashSet<ValueId>) {
    match expr {
        Expr::Var(v) => record_var_id(v, used),
        Expr::Binary(_, lhs, rhs) => {
            collect_expr_ids(lhs, used);
            collect_expr_ids(rhs, used);
        }
        Expr::Unary(_, inner) => collect_expr_ids(inner, used),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_ids(cond, used);
            collect_expr_ids(then_expr, used);
            collect_expr_ids(else_expr, used);
        }
        Expr::True | Expr::False | Expr::Constant(_) => {}
    }
}

/// Consuming repeat loop: `repeat.4 { add }`
///
/// Initial stack: `[v_0, v_1, v_2, v_3, v_4]` (5 inputs)
///
/// Expected output:
/// ```text
/// for i in 0..4 {
///   v_3 = v_3 + v_(4 - i);
/// }
/// return v_0;
/// ```
///
/// The key property: the accumulator stays in the `v_3` slot.
///
/// Stack trace at iteration i:
/// - Depth before add: 5 - i
/// - Reads: positions (4-i) and (3-i)
/// - Writes: position (3-i) (depth decreases by 1)
#[test]
fn consuming_repeat_destination_subscript() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc consuming_repeat_0
            repeat.4
                add
            end
        end
        "#,
    )]);

    let structured = decompile(&ws, "test::consuming_repeat_0", "test");
    let output = format_output(&structured);
    eprintln!("Actual output:\n{}", output);

    // The destination subscript should be constant (the accumulator slot).
    let dest_sub = loop_dest_subscript(&structured);
    match dest_sub {
        Some(IndexExpr::Const(base_val)) => {
            assert_eq!(
                base_val, 3,
                "destination subscript base should be 3, got {}. Full output:\n{}",
                base_val, output
            );
        }
        other => {
            panic!(
                "expected constant subscript for loop destination, got {:?}. Full output:\n{}",
                other, output
            );
        }
    }
}

/// Consuming repeat with pre-loop pushes: `push.1.2.3.4; repeat.4 { add }; push.5; sub`
///
/// This test verifies that:
/// 1. Expression propagation does NOT inline constants into the repeat loop body
/// 2. DCE keeps all pre-loop assignments alive (they feed into the consuming loop)
///
/// The loop body should keep the accumulator in a fixed slot and index the
/// consumed input with the loop counter (e.g., `v_3 = v_3 + v_(4 - i)`).
///
/// Expected output:
/// ```text
/// v_1 = 1;
/// v_2 = 2;
/// v_3 = 3;
/// v_4 = 4;
/// for i in 0..4 {
///   v_3 = v_3 + v_(4 - i);
/// }
/// v_1 = 5;
/// v_0 = v_0 - 5;
/// return v_0;
/// ```
#[test]
fn consuming_repeat_with_pre_loop_pushes() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc consuming_repeat_1
            push.1.2.3.4
            repeat.4
                add
            end
            push.5
            sub
        end
        "#,
    )]);

    let structured = decompile(&ws, "test::consuming_repeat_1", "test");
    let output = format_output(&structured);
    eprintln!("Actual output:\n{}", output);

    // Check 1: No negative subscripts
    assert!(
        !has_negative_subscript(&structured),
        "output should not contain negative subscripts. Full output:\n{}",
        output
    );

    // Check 2: Loop destination should stay in the accumulator slot.
    let dest_sub = loop_dest_subscript(&structured);
    match dest_sub {
        Some(IndexExpr::Const(base_val)) => {
            assert_eq!(
                base_val, 3,
                "destination subscript base should be 3, got {}. Full output:\n{}",
                base_val, output
            );
        }
        other => {
            panic!(
                "expected constant subscript for loop destination, got {:?}. Full output:\n{}",
                other, output
            );
        }
    }

    // Check 3: The loop body should NOT be empty (constants should not be folded away)
    let has_non_empty_loop = structured.iter().any(|stmt| {
        if let Stmt::Repeat { body, .. } = stmt {
            !body.is_empty()
        } else {
            false
        }
    });
    assert!(
        has_non_empty_loop,
        "loop body should not be empty (constants should not be propagated in). Full output:\n{}",
        output
    );

    // Check 4: All 4 pre-loop assignments should be present (DCE fix)
    // The values 1, 2, 3, 4 are pushed before the loop and all feed into it.
    for (var, val) in [("v_1", "1"), ("v_2", "2"), ("v_3", "3"), ("v_4", "4")] {
        let assignment = format!("{} = {}", var, val);
        assert!(
            output.contains(&assignment),
            "output should contain '{}' (DCE should preserve pre-loop assignments). Full output:\n{}",
            assignment,
            output
        );
    }
}

/// Verify the current behavior after the subscript fix.
#[test]
fn verify_correct_behavior_consuming_repeat_0() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc consuming_repeat_0
            repeat.4
                add
            end
        end
        "#,
    )]);

    let structured = decompile(&ws, "test::consuming_repeat_0", "test");
    let output = format_output(&structured);

    eprintln!("Output for consuming_repeat_0:\n{}", output);

    // The destination subscript should stay in the accumulator slot.
    let dest_sub = loop_dest_subscript(&structured);
    if let Some(IndexExpr::Const(base_val)) = dest_sub {
        assert_eq!(
            base_val, 3,
            "destination subscript base should be 3, got {}",
            base_val
        );
    }

    // Return should be v_0 (final result at position 0)
    assert!(
        output.contains("return v_0"),
        "return should be v_0, got: {}",
        output
    );
}

/// Verify the current behavior after the expression propagation fix.
///
/// This test verifies that expression propagation correctly handles repeat loops
/// by NOT inlining constants into the loop body.
#[test]
fn verify_correct_behavior_consuming_repeat_1() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc consuming_repeat_1
            push.1.2.3.4
            repeat.4
                add
            end
            push.5
            sub
        end
        "#,
    )]);

    let structured = decompile(&ws, "test::consuming_repeat_1", "test");
    let output = format_output(&structured);

    eprintln!("Output for consuming_repeat_1:\n{}", output);

    // Should NOT have negative subscripts
    assert!(
        !has_negative_subscript(&structured),
        "should not have negative subscripts, got: {}",
        output
    );

    // The loop body should keep the accumulator in a fixed slot.
    let dest_sub = loop_dest_subscript(&structured);
    assert!(
        matches!(dest_sub, Some(IndexExpr::Const(3))),
        "loop destination should stay in v_3, got {:?}. Output:\n{}",
        dest_sub,
        output
    );
}

/// Test neutral repeat loop: `push.1; repeat.4 { dup.0; add }`
///
/// This is a "neutral" loop (stack effect = 0) because each iteration:
/// - dup.0: pushes 1 value
/// - add: pops 2 values, pushes 1 value
/// - Net effect: 0
///
/// The loop doubles the top value: 1 -> 2 -> 4 -> 8 -> 16.
///
/// Expected output (without expression propagation):
/// ```text
/// proc neutral_repeat_0() -> Felt {
///   v_0 = 1;
///   for i in 0..4 {
///     v_1 = v_0;
///     v_0 = v_0 + v_1;
///   }
///   return v_0;
/// }
/// ```
///
/// The dup.0 creates v_1 = v_0, and add creates v_0 = v_0 + v_1.
/// The key property is that subscripts are not negative (which was a bug).
#[test]
fn neutral_repeat_doubles_value() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc neutral_repeat_0
            push.1
            repeat.4
                dup.0
                add
            end
        end
        "#,
    )]);

    let structured = decompile_no_propagation(&ws, "test::neutral_repeat_0", "test");
    let output = format_output(&structured);

    // Should have the initial assignment v_0 = 1
    assert!(
        output.contains("v_0 = 1"),
        "should have initial assignment v_0 = 1, got: {}",
        output
    );

    // Should have the loop structure
    assert!(
        output.contains("for i in 0..4"),
        "should have a for loop, got: {}",
        output
    );

    // The loop body should NOT have negative subscripts (this was the bug)
    assert!(
        !has_negative_subscript(&structured),
        "should not have negative subscripts. Full output:\n{}",
        output
    );

    // Return should be v_0
    assert!(
        output.contains("return v_0"),
        "return should be v_0, got: {}",
        output
    );
}

/// Test loop-carried slot below entry depth stays unindexed in neutral loops.
///
/// This loop is stack-neutral but overwrites the entry slot each iteration:
/// - `dup.0` copies the entry value
/// - `add` replaces the entry slot with a new value
///
/// The destination of the `add` should keep a constant subscript in neutral
/// repeat loops.
#[test]
fn loop_carried_below_entry_depth_not_indexed_in_neutral_repeat() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc carry_below_entry
            push.1
            repeat.2
                dup.0
                add
            end
        end
        "#,
    )]);

    let structured = decompile_no_propagation(&ws, "test::carry_below_entry", "test");
    let output = format_output(&structured);

    let mut saw_pre_loop_assign = false;
    for stmt in &structured {
        match stmt {
            Stmt::Assign { .. } => saw_pre_loop_assign = true,
            Stmt::Repeat { .. } => break,
            _ => {}
        }
    }
    assert!(
        saw_pre_loop_assign,
        "expected pre-loop assignment to establish entry depth. Output:\n{}",
        output
    );

    let dest = loop_dest_var(&structured).expect("expected binary assignment in loop body");
    assert_eq!(
        dest.stack_depth, 0,
        "expected loop-carried destination at stack depth 0. Output:\n{}",
        output
    );
    assert!(
        !subscript_has_loop_var(&dest.subscript),
        "expected constant subscript for loop-carried value. Output:\n{}",
        output
    );
}

/// Test consuming repeat with symbolic inputs (not constants).
/// This tests the phi fix in isolation from constant propagation issues.
#[test]
fn consuming_repeat_symbolic_inputs() {
    // This procedure reads 5 inputs from the stack (no pushes)
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc symbolic_repeat
            repeat.4
                add
            end
        end
        "#,
    )]);

    let structured = decompile_no_propagation(&ws, "test::symbolic_repeat", "test");
    let output = format_output(&structured);

    eprintln!("Output for symbolic_repeat (no propagation):\n{}", output);

    // The output should have proper symbolic loop body:
    // for i in 0..4 {
    //   v_3 = v_3 + v_(4 - i);
    // }
    // return v_0;

    // Check for the loop structure
    assert!(
        output.contains("for i in 0..4"),
        "should have a for loop, got: {}",
        output
    );

    // Check that there are no carrier assignments (the phi fix)
    // A carrier assignment would look like `v_(something) = v_N;` (simple var copy)
    // instead of `v_(something) = v_X + v_Y;` (actual add)
    for stmt in &structured {
        if let Stmt::Repeat { body, .. } = stmt {
            for inner in body {
                if let Stmt::Assign { expr, .. } = inner {
                    // The expr should be a Binary(Add, ...), not a simple Var
                    assert!(
                        matches!(expr, Expr::Binary(..)),
                        "loop body should have binary add, not carrier assignment. Stmt: {:?}",
                        inner
                    );
                }
            }
        }
    }

    // Return should be v_0
    assert!(
        output.contains("return v_0"),
        "return should be v_0, got: {}",
        output
    );
}

/// Consuming repeat loop with a loop-carried accumulator after `eq.0`.
///
/// The `and` operation must combine the accumulator (dest base) with the
/// freshly computed `eq.0` result (dest base + 1). The current analysis
/// incorrectly uses the consumed input instead of the accumulator.
#[test]
fn consuming_repeat_eqz_uses_accumulator_operand() {
    let ws = workspace_from_modules(&[("repeat", include_str!("fixtures/repeat.masm"))]);

    let structured = decompile_no_propagation(&ws, "repeat::consuming_repeat_eqz", "repeat");
    let output = format_output(&structured);
    eprintln!("Output for consuming_repeat_eqz:\n{}", output);

    let mut found = None;
    for stmt in &structured {
        if let Stmt::Repeat { body, .. } = stmt {
            for inner in body {
                if let Stmt::Assign { dest, expr } = inner {
                    if let Expr::Binary(BinOp::And, lhs, rhs) = expr {
                        let dest_base = subscript_base(&dest.subscript);
                        let lhs_base = match &**lhs {
                            Expr::Var(v) => subscript_base(&v.subscript),
                            _ => None,
                        };
                        let rhs_base = match &**rhs {
                            Expr::Var(v) => subscript_base(&v.subscript),
                            _ => None,
                        };
                        found = Some((dest_base, lhs_base, rhs_base));
                        break;
                    }
                }
            }
        }
    }

    let (dest_base, lhs_base, rhs_base) =
        found.expect("expected an `and` assignment in the repeat body");
    let dest_base = dest_base.expect("expected constant base in dest subscript");
    let lhs_base = lhs_base.expect("expected constant base in lhs subscript");
    let rhs_base = rhs_base.expect("expected constant base in rhs subscript");

    let mut bases = [lhs_base, rhs_base];
    bases.sort();
    let expected = [dest_base - 1, dest_base];
    assert_eq!(
        bases, expected,
        "and operands should use accumulator (base {}) and consumed eq result (base {}). Output:\n{}",
        dest_base,
        dest_base + 1,
        output
    );
}

/// Producing repeat loop that swaps a pushed value with the entry value.
///
/// This permutation moves the entry value into the produced region, which
/// the current loop analysis cannot represent correctly. The decompiler
/// should reject this pattern rather than misrepresent it.
#[test]
fn producing_repeat_swap_entry_has_no_phis() {
    let ws = workspace_from_modules(&[("repeat", include_str!("fixtures/repeat.masm"))]);

    let structured = decompile_no_optimizations(&ws, "repeat::producing_repeat_swap_entry");
    let output = format_output(&structured);
    eprintln!("Output for producing_repeat_swap_entry:\n{}", output);

    let mut saw_repeat = false;
    for stmt in &structured {
        if let Stmt::Repeat { phis, .. } = stmt {
            saw_repeat = true;
            assert!(
                phis.is_empty(),
                "producing swap-only loop should not create repeat phis. Output:\n{}",
                output
            );
        }
    }
    assert!(saw_repeat, "expected repeat loop in output");
}

/// Producing repeat loop should index each pushed value by the loop counter.
#[test]
fn producing_repeat_1_indexes_loop_outputs() {
    let ws = workspace_from_modules(&[("repeat", include_str!("fixtures/repeat.masm"))]);

    let structured = decompile_no_propagation(&ws, "repeat::producing_repeat_1", "repeat");
    let output = format_output(&structured);
    eprintln!("Output for producing_repeat_1:\n{}", output);

    let mut dest_subscript = None;
    for stmt in &structured {
        if let Stmt::Repeat { body, .. } = stmt {
            for inner in body {
                if let Stmt::Assign { dest, .. } = inner {
                    dest_subscript = Some(dest.subscript.clone());
                    break;
                }
            }
        }
    }

    let dest_subscript = dest_subscript.expect("expected assignment in repeat body");
    assert!(
        subscript_has_loop_var(&dest_subscript),
        "producing repeat outputs should be indexed by loop counter. Output:\n{}",
        output
    );
}

/// U256 eqz should return a value defined in the loop, not an input.
#[test]
fn u256_eqz_returns_non_input_value() {
    let ws = workspace_from_modules(&[("u256", include_str!("fixtures/u256.masm"))]);

    let structured = decompile_no_propagation(&ws, "u256::eqz", "u256");
    let output = format_output(&structured);
    eprintln!("Output for u256::eqz:\n{}", output);

    let (used, defined) = collect_used_defined_ids(&structured);
    let input_ids: HashSet<ValueId> = used.difference(&defined).cloned().collect();

    let return_vars = structured
        .iter()
        .find_map(|stmt| match stmt {
            Stmt::Return(vars) => Some(vars),
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
        .expect("expected return to be a value id");
    assert!(
        !input_ids.contains(&return_id),
        "u256::eqz should return a computed value, not an input. Output:\n{}",
        output
    );
}
