//! Tests for `push.[a, b, c, d][i]` and `push.[a, b, c, d][i..j]` decompilation.
//!
//! `PushSlice` pushes a contiguous sub-range of a word constant onto the stack.
//! Tests operate on the unoptimized IR to verify the exact body shape produced
//! by the lifter.

mod common;

use common::{assert_names_defined_when_used, decompile_no_optimizations};
use masm_decompiler::{
    decompile::Decompiler,
    frontend::testing::workspace_from_modules,
    ir::{BinOp, Constant, Expr, Stmt, Var},
};

const FIXTURE: &str = include_str!("fixtures/push_slice.masm");

fn decompile(proc_name: &str) -> Vec<Stmt> {
    let ws = workspace_from_modules(&[("push_slice", FIXTURE)]);
    let fq_name = format!("push_slice::{proc_name}");
    decompile_no_optimizations(&ws, &fq_name)
}

fn decompile_optimized(proc_name: &str) -> Vec<Stmt> {
    let ws = workspace_from_modules(&[("push_slice", FIXTURE)]);
    let fq_name = format!("push_slice::{proc_name}");
    let decompiler = Decompiler::new(&ws);
    decompiler
        .decompile_proc(&fq_name)
        .expect("decompilation should succeed")
        .body
        .stmts
        .clone()
}

/// Extract the destination and felt value from a constant assignment.
fn const_assign(stmt: &Stmt) -> Option<(&Var, u64)> {
    match stmt {
        Stmt::Assign {
            dest,
            expr: Expr::Constant(Constant::Felt(v)),
            ..
        } => Some((dest, *v)),
        _ => None,
    }
}

// ---------- push_slice_single: push.[1,2,3,4][2] ----------

/// `push.[1,2,3,4][2]` must produce exactly 1 constant assignment with value 3.
#[test]
fn push_slice_single_produces_one_constant_assignment() {
    let stmts = decompile("push_slice_single");

    let consts: Vec<_> = stmts.iter().filter_map(|s| const_assign(s)).collect();
    assert_eq!(
        consts.len(),
        1,
        "push.[1,2,3,4][2] should produce 1 constant assignment: {stmts:?}"
    );
    assert_eq!(
        consts[0].1, 3,
        "push.[1,2,3,4][2] should push element at index 2 (value 3): {stmts:?}"
    );
}

#[test]
fn push_slice_single_names_defined_when_used() {
    let stmts = decompile("push_slice_single");
    assert_names_defined_when_used("push_slice_single", &stmts);
}

// ---------- push_slice_range: push.[1,2,3,4][1..3] ----------

/// `push.[1,2,3,4][1..3]` must produce exactly 2 constant assignments whose
/// values are the elements at indices 1 and 2 of the word: values 2 and 3.
///
/// The element at the lower index (value 2) must end up on top, matching the
/// convention where `word[range.start]` is TOS.  In the unoptimized IR the
/// elements are pushed in reverse, so the first assignment pushes the last
/// element and the second assignment pushes the first element — but the
/// *returned* order (as seen in the Return statement) must place value 2 first.
#[test]
fn push_slice_range_produces_two_constant_assignments_in_correct_order() {
    let stmts = decompile("push_slice_range");

    let consts: Vec<_> = stmts.iter().filter_map(|s| const_assign(s)).collect();
    assert_eq!(
        consts.len(),
        2,
        "push.[1,2,3,4][1..3] should produce 2 constant assignments: {stmts:?}"
    );

    // The two values pushed must be 3 and 2 (reverse order), but the final
    // result must present them as [2, 3] (index 1 on top, index 2 below).
    let values: Vec<u64> = consts.iter().map(|(_, v)| *v).collect();
    assert_eq!(
        values,
        vec![3, 2],
        "push.[1,2,3,4][1..3] should push values [3, 2] (reverse order): {stmts:?}"
    );

    // Verify the return order: the variable for value 2 should come before
    // the variable for value 3, matching the stack convention where the
    // element at the lower slice index sits on top.
    let ret = stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Return { values, .. } => Some(values),
            _ => None,
        })
        .expect("expected a return statement");
    assert_eq!(ret.len(), 2, "return should have 2 values");
    // ret[0] should be the var that was assigned 2, ret[1] the var assigned 3.
    assert_eq!(
        ret[0], *consts[1].0,
        "return[0] should be the variable holding value 2 (top of stack)"
    );
    assert_eq!(
        ret[1], *consts[0].0,
        "return[1] should be the variable holding value 3"
    );
}

#[test]
fn push_slice_range_names_defined_when_used() {
    let stmts = decompile("push_slice_range");
    assert_names_defined_when_used("push_slice_range", &stmts);
}

// ---------- push_slice_and_add: push.[1,2,3,4][1..3]; add ----------

/// The unoptimized body must contain:
///   1. Two constant assignments (values 3 and 2).
///   2. One add-assignment whose operands are exactly those two variables.
#[test]
fn push_slice_and_add_body_shape() {
    let stmts = decompile("push_slice_and_add");

    let consts: Vec<_> = stmts.iter().filter_map(|s| const_assign(s)).collect();
    assert_eq!(consts.len(), 2, "expected 2 constant pushes: {stmts:?}");

    // Find the add assignment.
    let add_stmt = stmts.iter().find(|s| {
        matches!(
            s,
            Stmt::Assign {
                expr: Expr::Binary(BinOp::Add, ..),
                ..
            }
        )
    });
    assert!(
        add_stmt.is_some(),
        "expected an add assignment after the two pushes: {stmts:?}"
    );

    // The add operands must reference the two pushed constants.
    let Stmt::Assign {
        expr: Expr::Binary(BinOp::Add, lhs, rhs),
        ..
    } = add_stmt.unwrap()
    else {
        unreachable!()
    };
    let operands = [lhs, rhs];
    let add_operand_vars: Vec<&Var> = operands
        .iter()
        .filter_map(|e| match e.as_ref() {
            Expr::Var(v) => Some(v),
            _ => None,
        })
        .collect();
    assert_eq!(
        add_operand_vars.len(),
        2,
        "add operands should both be variable references: {stmts:?}"
    );
    let pushed_vars: Vec<&Var> = consts.iter().map(|(v, _)| *v).collect();
    for operand in &add_operand_vars {
        assert!(
            pushed_vars.contains(operand),
            "add operand {operand:?} should reference one of the pushed constants: {pushed_vars:?}"
        );
    }
}

/// With optimizations, the add of two constants should fold to 5.
#[test]
fn push_slice_and_add_optimized_folds_to_constant() {
    let stmts = decompile_optimized("push_slice_and_add");

    let consts: Vec<_> = stmts.iter().filter_map(|s| const_assign(s)).collect();
    assert_eq!(
        consts.len(),
        1,
        "optimized push_slice_and_add should fold to a single constant: {stmts:?}"
    );
    assert_eq!(consts[0].1, 5, "2 + 3 should fold to 5: {stmts:?}");
}

#[test]
fn push_slice_and_add_names_defined_when_used() {
    let stmts = decompile("push_slice_and_add");
    assert_names_defined_when_used("push_slice_and_add", &stmts);
}

// ---------- push_slice_full: push.[1,2,3,4][0..4] ----------

/// `push.[1,2,3,4][0..4]` must produce exactly 4 constant assignments,
/// and the values must match the full word in reverse push order: [4, 3, 2, 1].
/// This should be identical in structure to a regular `push.[1,2,3,4]`.
#[test]
fn push_slice_full_range_produces_four_constants_matching_word_push() {
    let stmts = decompile("push_slice_full");

    let consts: Vec<_> = stmts.iter().filter_map(|s| const_assign(s)).collect();
    assert_eq!(
        consts.len(),
        4,
        "push.[1,2,3,4][0..4] should produce 4 constant assignments: {stmts:?}"
    );

    let values: Vec<u64> = consts.iter().map(|(_, v)| *v).collect();
    assert_eq!(
        values,
        vec![4, 3, 2, 1],
        "full-range push slice should push [4, 3, 2, 1] (reverse order): {stmts:?}"
    );

    // Verify the return order: element at index 0 (value 1) on top.
    let ret = stmts
        .iter()
        .find_map(|s| match s {
            Stmt::Return { values, .. } => Some(values),
            _ => None,
        })
        .expect("expected a return statement");
    assert_eq!(ret.len(), 4);
    // The return should list the variable for 1 first (top), then 2, 3, 4.
    assert_eq!(ret[0], *consts[3].0, "return[0] should hold value 1 (TOS)");
    assert_eq!(ret[1], *consts[2].0, "return[1] should hold value 2");
    assert_eq!(ret[2], *consts[1].0, "return[2] should hold value 3");
    assert_eq!(ret[3], *consts[0].0, "return[3] should hold value 4");
}

/// All destinations in the push-slice output must be unique.
#[test]
fn push_slice_full_destinations_are_unique() {
    let stmts = decompile("push_slice_full");

    let mut dests: Vec<_> = stmts
        .iter()
        .filter_map(|s| match s {
            Stmt::Assign { dest, .. } => Some(dest),
            _ => None,
        })
        .collect();
    let total = dests.len();
    dests.sort();
    dests.dedup();
    assert_eq!(
        dests.len(),
        total,
        "push_slice destinations must all be unique: {stmts:?}"
    );
}

#[test]
fn push_slice_full_names_defined_when_used() {
    let stmts = decompile("push_slice_full");
    assert_names_defined_when_used("push_slice_full", &stmts);
}
