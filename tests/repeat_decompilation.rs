//! Tests for repeat loop decompilation with correct subscript assignment.

mod common;

use common::{decompile, decompile_no_propagation};
use masm_decompiler::fmt::{CodeWriter, FormattingConfig};
use masm_decompiler::frontend::testing::workspace_from_modules;
use masm_decompiler::ir::{Expr, IndexExpr, Stmt, Var};

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

/// Consuming repeat loop: `repeat.4 { add }`
///
/// Initial stack: `[v_0, v_1, v_2, v_3, v_4]` (5 inputs)
///
/// Expected output:
/// ```text
/// for i in 0..4 {
///   v_(3 - i) = v_(4 - i) + v_(3 - i);
/// }
/// return v_0;
/// ```
///
/// The key property: destination is `v_(3-i)`, not `v_(4-i)`.
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

    // The destination subscript should be (3 - i)
    let dest_sub = loop_dest_subscript(&structured);
    match dest_sub {
        Some(IndexExpr::Add(base, _offset)) => {
            // Expected: base = 3, offset = -1 * loop_var
            if let IndexExpr::Const(base_val) = *base {
                assert_eq!(
                    base_val, 3,
                    "destination subscript base should be 3, got {}. Full output:\n{}",
                    base_val, output
                );
            } else {
                panic!(
                    "expected constant base in destination subscript, got {:?}. Full output:\n{}",
                    base, output
                );
            }
        }
        other => {
            panic!(
                "expected Add subscript for loop destination, got {:?}. Full output:\n{}",
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
/// The loop body should use symbolic subscripts like `v_(3 - i) = v_(4 - i) + v_(3 - i)`
/// rather than constant values.
///
/// Expected output:
/// ```text
/// v_1 = 1;
/// v_2 = 2;
/// v_3 = 3;
/// v_4 = 4;
/// for i in 0..4 {
///   v_(3 - i) = v_(4 - i) + v_(3 - i);
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

    // Check 2: Loop destination should be (3 - i) - this is the key fix!
    // Previously, constants were propagated into the loop, causing incorrect output.
    let dest_sub = loop_dest_subscript(&structured);
    match dest_sub {
        Some(IndexExpr::Add(base, _)) => {
            if let IndexExpr::Const(base_val) = *base {
                assert_eq!(
                    base_val, 3,
                    "destination subscript base should be 3, got {}. Full output:\n{}",
                    base_val, output
                );
            }
        }
        other => {
            panic!(
                "expected Add subscript for loop destination, got {:?}. Full output:\n{}",
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

    // The destination subscript should now be (3 - i), which is correct
    let dest_sub = loop_dest_subscript(&structured);
    if let Some(IndexExpr::Add(base, _)) = dest_sub {
        if let IndexExpr::Const(base_val) = *base {
            assert_eq!(
                base_val, 3,
                "destination subscript base should be 3, got {}",
                base_val
            );
        }
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

    // The loop body should use symbolic subscripts, not inlined constants.
    // Check that the loop destination subscript is (3 - i).
    let dest_sub = loop_dest_subscript(&structured);
    assert!(
        matches!(dest_sub, Some(IndexExpr::Add(..))),
        "loop destination should have symbolic subscript (3 - i), got {:?}. Output:\n{}",
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
    //   v_(3 - i) = v_(4 - i) + v_(3 - i);
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
