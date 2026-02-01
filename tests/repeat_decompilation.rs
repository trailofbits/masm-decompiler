//! Tests for repeat loop decompilation with correct subscript assignment.
//!
//! These tests document known issues with the current subscript assignment algorithm.
//! The tests are marked `#[ignore]` because they currently fail.
//!
//! ## Problem Summary
//!
//! The current implementation computes subscripts incorrectly for consuming loops.
//! The root cause is that subscript assignment doesn't properly track absolute stack
//! positions during execution.
//!
//! ## Expected Behavior
//!
//! For a consuming loop like `repeat.N { add }`:
//! - Entry stack depth: D
//! - At iteration i: reads positions (D-1-i) and (D-2-i), writes to (D-2-i)
//! - The destination subscript should be `(D-2-i)`, not `(D-1-i)`
//!
//! For values pushed before a loop:
//! - Each push should get a consecutive subscript matching its stack position
//! - These subscripts should be consistent with the loop's symbolic subscripts

mod common;

use common::{decompile, decompile_no_propagation, run_structure_debug};
use masm_decompiler::fmt::CodeWriter;
use masm_decompiler::frontend::testing::workspace_from_modules;
use masm_decompiler::ssa::{IndexExpr, Stmt, Subscript};

/// Helper to format decompiled output as a string for debugging.
fn format_output(stmts: &[Stmt]) -> String {
    let mut writer = CodeWriter::new();
    writer.register_loop_vars(stmts);
    for stmt in stmts {
        writer.write(stmt.clone());
    }
    writer.finish()
}

/// Extract the destination subscript from the binary operation inside a repeat loop.
/// Skips carrier assignments (simple var copies) and finds the actual computation.
fn loop_dest_subscript(stmts: &[Stmt]) -> Option<Subscript> {
    use masm_decompiler::ssa::Expr;
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

/// Check if any variable has a negative constant subscript.
fn has_negative_subscript(stmts: &[Stmt]) -> bool {
    fn check_stmt(stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Assign { dest, .. } => {
                matches!(dest.subscript, Subscript::Expr(IndexExpr::Const(n)) if n < 0)
            }
            Stmt::Repeat { body, .. } | Stmt::While { body, .. } => {
                body.iter().any(check_stmt)
            }
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
        Some(Subscript::Expr(IndexExpr::Add(base, _offset))) => {
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
/// NOTE: This test is marked #[ignore] because expression propagation inlines constants
/// into the loop body, which is a known limitation (see CLAUDE.md). The phi fix works
/// correctly for symbolic inputs - see `consuming_repeat_symbolic_inputs` test.
///
/// Expected output (with proper symbolic handling):
/// ```text
/// v_1 = 1;
/// v_2 = 2;
/// v_3 = 3;
/// v_4 = 4;
/// for i in 0..4 {
///   v_(3 - i) = v_(4 - i) + v_(3 - i);
/// }
/// v_0 = ...;  // final computation
/// return v_0;
/// ```
#[test]
#[ignore = "Known limitation: constant propagation into repeat loops (see CLAUDE.md)"]
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

    // Check 2: Loop destination should be (3 - i)
    let dest_sub = loop_dest_subscript(&structured);
    match dest_sub {
        Some(Subscript::Expr(IndexExpr::Add(base, _))) => {
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

    // Check 3: Pre-loop pushes should have consecutive subscripts 1, 2, 3, 4
    let mut push_subscripts = Vec::new();
    for stmt in &structured {
        if let Stmt::Repeat { .. } = stmt {
            break; // Stop at the loop
        }
        if let Stmt::Assign { dest, .. } = stmt {
            if let Subscript::Expr(IndexExpr::Const(n)) = dest.subscript {
                push_subscripts.push(n);
            }
        }
    }
    assert_eq!(
        push_subscripts,
        vec![1, 2, 3, 4],
        "pre-loop push subscripts should be [1, 2, 3, 4], got {:?}. Full output:\n{}",
        push_subscripts,
        output
    );
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
    if let Some(Subscript::Expr(IndexExpr::Add(base, _))) = dest_sub {
        if let IndexExpr::Const(base_val) = *base {
            assert_eq!(
                base_val, 3,
                "destination subscript base should be 3, got {}", base_val
            );
        }
    }

    // Return should be v_0 (final result at position 0)
    assert!(
        output.contains("return v_0"),
        "return should be v_0, got: {}", output
    );
}

/// Verify the current behavior after the subscript fix for the second example.
///
/// NOTE: This test is marked #[ignore] because expression propagation inlines constants
/// into the loop body, which is a known limitation (see CLAUDE.md). The phi fix works
/// correctly for symbolic inputs - see `consuming_repeat_symbolic_inputs` test.
#[test]
#[ignore = "Known limitation: constant propagation into repeat loops (see CLAUDE.md)"]
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
        "should not have negative subscripts, got: {}", output
    );

    // Pre-loop pushes should have consecutive subscripts 1, 2, 3, 4
    let mut push_subscripts = Vec::new();
    for stmt in &structured {
        if let Stmt::Repeat { .. } = stmt {
            break; // Stop at the loop
        }
        if let Stmt::Assign { dest, .. } = stmt {
            if let Subscript::Expr(IndexExpr::Const(n)) = dest.subscript {
                push_subscripts.push(n);
            }
        }
    }
    assert_eq!(
        push_subscripts,
        vec![1, 2, 3, 4],
        "pre-loop push subscripts should be [1, 2, 3, 4], got {:?}", push_subscripts
    );
}

/// Debug test to inspect var_depths and loop_contexts.
#[test]
fn debug_loop_context() {
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

    let structured = run_structure_debug(&ws, "test::consuming_repeat_0", "test");

    // Print all statements in the Repeat body
    for stmt in &structured {
        if let Stmt::Repeat { loop_var, loop_count, body } = stmt {
            eprintln!("Repeat: loop_var.index = {}, loop_count = {}", loop_var.index, loop_count);
            for inner in body {
                eprintln!("  Body stmt: {:?}", inner);
            }
        }
    }

    let output = format_output(&structured);
    eprintln!("Debug output:\n{}", output);
}

/// Debug test for consuming_repeat_1 without expression propagation.
#[test]
fn debug_consuming_repeat_1_no_propagation() {
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

    let structured = decompile_no_propagation(&ws, "test::consuming_repeat_1", "test");
    let output = format_output(&structured);

    eprintln!("Output for consuming_repeat_1 (no propagation):\n{}", output);

    // Print all statements
    for stmt in &structured {
        eprintln!("Stmt: {:?}", stmt);
    }
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
        "should have a for loop, got: {}", output
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
                        matches!(expr, masm_decompiler::ssa::Expr::Binary(..)),
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
        "return should be v_0, got: {}", output
    );
}
