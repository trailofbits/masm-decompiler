//! Tests for `cdropw` and `cswapw` instruction decompilation.
//!
//! These word-width conditional operations produce per-element ternary
//! assignments, mirroring the scalar `cdrop` and `cswap` implementations.
//!
//! The tests operate on the unoptimized IR so that the body structure directly
//! reflects the lifting output rather than the result of expression propagation
//! or dead-code elimination.

mod common;

use common::{assert_names_defined_when_used, decompile_no_optimizations};
use masm_decompiler::{
    frontend::testing::workspace_from_modules,
    ir::{Constant, Expr, Stmt, Var},
};

const FIXTURE: &str = include_str!("fixtures/conditional_word_ops.masm");

fn decompile(proc_name: &str) -> Vec<Stmt> {
    let ws = workspace_from_modules(&[("cond_word", FIXTURE)]);
    let fq_name = format!("cond_word::{proc_name}");
    decompile_no_optimizations(&ws, &fq_name)
}

/// Extract the ternary components `(cond, then, else)` from an assignment.
fn ternary_parts(stmt: &Stmt) -> Option<(&Expr, &Expr, &Expr)> {
    match stmt {
        Stmt::Assign {
            expr:
                Expr::Ternary {
                    cond,
                    then_expr,
                    else_expr,
                },
            ..
        } => Some((cond, then_expr, else_expr)),
        _ => None,
    }
}

/// Extract the destination variable from an assignment statement.
fn assign_dest(stmt: &Stmt) -> Option<&Var> {
    match stmt {
        Stmt::Assign { dest, .. } => Some(dest),
        _ => None,
    }
}

/// Extract the felt constant from a constant assignment.
fn const_felt_value(stmt: &Stmt) -> Option<u64> {
    match stmt {
        Stmt::Assign {
            expr: Expr::Constant(Constant::Felt(v)),
            ..
        } => Some(*v),
        _ => None,
    }
}

/// Extract the variable from a `Expr::Var` reference.
fn expr_var(expr: &Expr) -> Option<&Var> {
    match expr {
        Expr::Var(v) => Some(v),
        _ => None,
    }
}

// ---------- cdropw tests ----------

/// `cdropw_passthrough` applies `cdropw` directly to 9 inputs.
///
/// The body must consist of exactly 4 ternary assignments.  Every ternary
/// must share the *same* condition variable, and the then/else operands must
/// reference distinct input variables (never the same pair).
#[test]
fn cdropw_passthrough_body_is_four_ternary_assignments_sharing_one_condition() {
    let stmts = decompile("cdropw_passthrough");

    // Exactly 4 ternary assignments, no other statements except the return.
    let ternaries: Vec<_> = stmts
        .iter()
        .filter(|s| ternary_parts(s).is_some())
        .collect();
    assert_eq!(
        ternaries.len(),
        4,
        "cdropw must produce exactly 4 ternary assignments: {stmts:?}"
    );

    // All four ternaries must share the same condition variable.
    let cond_vars: Vec<_> = ternaries
        .iter()
        .map(|s| expr_var(ternary_parts(s).unwrap().0).expect("condition should be a Var"))
        .collect();
    assert!(
        cond_vars.windows(2).all(|w| w[0] == w[1]),
        "all cdropw ternary conditions must reference the same variable: {cond_vars:?}"
    );

    // For each ternary, the then and else operands must be distinct variables.
    for (i, s) in ternaries.iter().enumerate() {
        let (_, then_expr, else_expr) = ternary_parts(s).unwrap();
        let then_var = expr_var(then_expr).expect("then branch should be a Var");
        let else_var = expr_var(else_expr).expect("else branch should be a Var");
        assert_ne!(
            then_var, else_var,
            "cdropw ternary {i}: then and else must reference different variables"
        );
    }
}

/// For cdropw on passthrough inputs, the then-branch of every ternary
/// must reference the "B" word (inputs closer to the top of the stack)
/// and the else-branch must reference the "A" word (inputs farther down).
///
/// Concretely, the condition is input 8, B is inputs 4..8, A is inputs 0..4.
/// Each ternary `dest = cond ? b_i : a_i` must pair corresponding positions:
/// the then-var for ternary i must come from B and the else-var from A, and
/// the two sets must not overlap.
#[test]
fn cdropw_passthrough_then_and_else_reference_disjoint_input_words() {
    let stmts = decompile("cdropw_passthrough");

    let ternaries: Vec<_> = stmts.iter().filter_map(|s| ternary_parts(s)).collect();
    assert_eq!(ternaries.len(), 4);

    let then_vars: Vec<&Var> = ternaries
        .iter()
        .map(|(_, t, _)| expr_var(t).unwrap())
        .collect();
    let else_vars: Vec<&Var> = ternaries
        .iter()
        .map(|(_, _, e)| expr_var(e).unwrap())
        .collect();

    // The then-set and else-set must be completely disjoint.
    for tv in &then_vars {
        assert!(
            !else_vars.contains(tv),
            "then-var {tv:?} must not appear in else-set {else_vars:?}"
        );
    }

    // Within each set the variables must be unique (no duplicates).
    let mut then_sorted = then_vars.clone();
    then_sorted.sort();
    then_sorted.dedup();
    assert_eq!(
        then_sorted.len(),
        4,
        "each then-branch must reference a unique variable: {then_vars:?}"
    );
    let mut else_sorted = else_vars.clone();
    else_sorted.sort();
    else_sorted.dedup();
    assert_eq!(
        else_sorted.len(),
        4,
        "each else-branch must reference a unique variable: {else_vars:?}"
    );
}

/// Variable names must be defined before use in the cdropw output.
#[test]
fn cdropw_passthrough_names_defined_when_used() {
    let stmts = decompile("cdropw_passthrough");
    assert_names_defined_when_used("cdropw_passthrough", &stmts);
}

/// When cdropw operates on constant words (via preceding pushes), the
/// unoptimized body contains 8 constant assignments followed by 4 ternaries.
/// The ternary then/else branches must reference the pushed constants, with
/// the "B" word (second push, values 5..8) in then-branches and the "A" word
/// (first push, values 1..4) in else-branches.
#[test]
fn cdropw_with_constant_words_references_correct_push_values() {
    let stmts = decompile("uses_cdropw");

    // First 8 statements are constant assignments.
    let const_assigns: Vec<_> = stmts
        .iter()
        .filter_map(|s| {
            let v = const_felt_value(s)?;
            let dest = assign_dest(s)?;
            Some((dest.clone(), v))
        })
        .collect();
    assert_eq!(
        const_assigns.len(),
        8,
        "uses_cdropw must have 8 constant assignments (2 words): {stmts:?}"
    );

    // The first 4 constants form word A ([4, 3, 2, 1] in push-reverse order).
    let word_a_values: Vec<u64> = const_assigns[..4].iter().map(|(_, v)| *v).collect();
    assert_eq!(
        word_a_values,
        vec![4, 3, 2, 1],
        "word A constants must be [4, 3, 2, 1] (push.[1,2,3,4] in reverse): {stmts:?}"
    );
    // The next 4 form word B ([8, 7, 6, 5]).
    let word_b_values: Vec<u64> = const_assigns[4..].iter().map(|(_, v)| *v).collect();
    assert_eq!(
        word_b_values,
        vec![8, 7, 6, 5],
        "word B constants must be [8, 7, 6, 5] (push.[5,6,7,8] in reverse): {stmts:?}"
    );

    // Build lookup maps from Var to its constant value.
    let word_a_vars: Vec<&Var> = const_assigns[..4].iter().map(|(d, _)| d).collect();
    let word_b_vars: Vec<&Var> = const_assigns[4..].iter().map(|(d, _)| d).collect();

    // The 4 ternary assignments must reference word B in then and word A in else.
    let ternaries: Vec<_> = stmts.iter().filter_map(|s| ternary_parts(s)).collect();
    assert_eq!(ternaries.len(), 4);

    for (i, (_, then_expr, else_expr)) in ternaries.iter().enumerate() {
        let then_var = expr_var(then_expr).unwrap();
        let else_var = expr_var(else_expr).unwrap();
        assert!(
            word_b_vars.contains(&then_var),
            "cdropw ternary {i} then-branch should reference word B, got {then_var:?}"
        );
        assert!(
            word_a_vars.contains(&else_var),
            "cdropw ternary {i} else-branch should reference word A, got {else_var:?}"
        );
    }
}

/// Variable names must be defined before use in the uses_cdropw output.
#[test]
fn cdropw_with_constants_names_defined_when_used() {
    let stmts = decompile("uses_cdropw");
    assert_names_defined_when_used("uses_cdropw", &stmts);
}

// ---------- cswapw tests ----------

/// `cswapw_passthrough` applies `cswapw` directly to 9 inputs.
///
/// The body must consist of exactly 8 ternary assignments: the first 4
/// select `(cond ? B_i : A_i)` and the next 4 select `(cond ? A_i : B_i)`,
/// all sharing the same condition variable.
#[test]
fn cswapw_passthrough_body_is_eight_ternary_assignments_sharing_one_condition() {
    let stmts = decompile("cswapw_passthrough");

    let ternaries: Vec<_> = stmts
        .iter()
        .filter(|s| ternary_parts(s).is_some())
        .collect();
    assert_eq!(
        ternaries.len(),
        8,
        "cswapw must produce exactly 8 ternary assignments: {stmts:?}"
    );

    // All 8 ternaries must share the same condition variable.
    let cond_vars: Vec<_> = ternaries
        .iter()
        .map(|s| expr_var(ternary_parts(s).unwrap().0).expect("condition should be a Var"))
        .collect();
    assert!(
        cond_vars.windows(2).all(|w| w[0] == w[1]),
        "all cswapw ternary conditions must reference the same variable: {cond_vars:?}"
    );
}

/// The first 4 and second 4 ternaries of cswapw must have swapped operands:
/// if the first half has `(cond ? b_i : a_i)`, then the second half must
/// have `(cond ? a_i : b_i)` for corresponding element positions.
#[test]
fn cswapw_passthrough_second_half_swaps_then_else_operands() {
    let stmts = decompile("cswapw_passthrough");

    let ternaries: Vec<_> = stmts.iter().filter_map(|s| ternary_parts(s)).collect();
    assert_eq!(ternaries.len(), 8);

    let first_half = &ternaries[..4];
    let second_half = &ternaries[4..];

    for i in 0..4 {
        let (_, fst_then, fst_else) = first_half[i];
        let (_, snd_then, snd_else) = second_half[i];

        let fst_then_var = expr_var(fst_then).unwrap();
        let fst_else_var = expr_var(fst_else).unwrap();
        let snd_then_var = expr_var(snd_then).unwrap();
        let snd_else_var = expr_var(snd_else).unwrap();

        // The second half must be the mirror of the first half.
        assert_eq!(
            fst_then_var, snd_else_var,
            "cswapw element {i}: first-half then-var must equal second-half else-var"
        );
        assert_eq!(
            fst_else_var, snd_then_var,
            "cswapw element {i}: first-half else-var must equal second-half then-var"
        );
    }
}

/// The 8 output variables of cswapw must all be unique (no two ternaries
/// write to the same destination).
#[test]
fn cswapw_passthrough_destinations_are_unique() {
    let stmts = decompile("cswapw_passthrough");

    let mut dests: Vec<&Var> = stmts.iter().filter_map(|s| assign_dest(s)).collect();
    let total = dests.len();
    dests.sort();
    dests.dedup();
    assert_eq!(
        dests.len(),
        total,
        "cswapw destinations must all be unique: {stmts:?}"
    );
}

/// Variable names must be defined before use in the cswapw output.
#[test]
fn cswapw_passthrough_names_defined_when_used() {
    let stmts = decompile("cswapw_passthrough");
    assert_names_defined_when_used("cswapw_passthrough", &stmts);
}

/// When cswapw operates on constant words, the unoptimized body should
/// have 8 constant assigns and 8 ternary assigns.  The first 4 ternaries
/// should select B-when-true/A-when-false, and the second 4 should swap.
#[test]
fn cswapw_with_constant_words_references_correct_push_values() {
    let stmts = decompile("uses_cswapw");

    let const_assigns: Vec<_> = stmts
        .iter()
        .filter_map(|s| {
            let v = const_felt_value(s)?;
            let dest = assign_dest(s)?;
            Some((dest.clone(), v))
        })
        .collect();
    assert_eq!(
        const_assigns.len(),
        8,
        "8 constant pushes expected: {stmts:?}"
    );

    let word_a_vars: Vec<&Var> = const_assigns[..4].iter().map(|(d, _)| d).collect();
    let word_b_vars: Vec<&Var> = const_assigns[4..].iter().map(|(d, _)| d).collect();

    let ternaries: Vec<_> = stmts.iter().filter_map(|s| ternary_parts(s)).collect();
    assert_eq!(ternaries.len(), 8);

    // First 4: then references B, else references A.
    for (i, (_, then_expr, else_expr)) in ternaries[..4].iter().enumerate() {
        let then_var = expr_var(then_expr).unwrap();
        let else_var = expr_var(else_expr).unwrap();
        assert!(
            word_b_vars.contains(&then_var),
            "cswapw first-half ternary {i} then-branch should reference word B"
        );
        assert!(
            word_a_vars.contains(&else_var),
            "cswapw first-half ternary {i} else-branch should reference word A"
        );
    }
    // Second 4: then references A, else references B (swapped).
    for (i, (_, then_expr, else_expr)) in ternaries[4..].iter().enumerate() {
        let then_var = expr_var(then_expr).unwrap();
        let else_var = expr_var(else_expr).unwrap();
        assert!(
            word_a_vars.contains(&then_var),
            "cswapw second-half ternary {i} then-branch should reference word A"
        );
        assert!(
            word_b_vars.contains(&else_var),
            "cswapw second-half ternary {i} else-branch should reference word B"
        );
    }
}

/// Variable names must be defined before use in the uses_cswapw output.
#[test]
fn cswapw_with_constants_names_defined_when_used() {
    let stmts = decompile("uses_cswapw");
    assert_names_defined_when_used("uses_cswapw", &stmts);
}
