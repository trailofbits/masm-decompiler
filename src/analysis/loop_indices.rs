//! Compute optional loop-index expressions for stack-carried variables.
//!
//! This is intentionally conservative: we only attach an affine expression of a single loop
//! counter when we can prove that the loop body applies a uniform stack shift each iteration.

use std::collections::HashMap;

use crate::ssa::{Expr, Stmt, Var};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IndexExpr {
    /// Unchanged name.
    Base,
    /// base + stride * counter
    Affine {
        base: i64,
        stride: i64,
        counter: Var,
    },
}

type VarMap = HashMap<Var, IndexExpr>;

/// Walk structured code and compute loop-dependent index expressions for stack-carried vars.
pub fn compute_loop_indices(code: &[Stmt]) -> VarMap {
    let mut out = HashMap::new();
    for stmt in code {
        walk_stmt(stmt, &mut out);
    }
    out
}

fn walk_stmt(stmt: &Stmt, out: &mut VarMap) {
    match stmt {
        Stmt::While { cond, body } => {
            if let Some(counter) = loop_counter_from_cond(cond) {
                if let Some(map) = analyze_loop_body(body, counter) {
                    out.extend(map);
                }
            }
            for s in body {
                walk_stmt(s, out);
            }
        }
        Stmt::For {
            cond, step, body, ..
        } => {
            if let Some(counter) = loop_counter_from_cond(cond) {
                if let Some(map) = analyze_loop_body(body, counter) {
                    out.extend(map);
                }
            }
            walk_stmt(step, out);
            for s in body {
                walk_stmt(s, out);
            }
        }
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            for s in then_body.iter().chain(else_body.iter()) {
                walk_stmt(s, out);
            }
        }
        Stmt::Switch { cases, default, .. } => {
            for (_, body) in cases {
                for s in body {
                    walk_stmt(s, out);
                }
            }
            for s in default {
                walk_stmt(s, out);
            }
        }
        _ => {}
    }
}

fn loop_counter_from_cond(cond: &Expr) -> Option<Var> {
    if let Expr::BinOp(crate::ssa::BinOp::Lt, lhs, rhs) = cond {
        if matches!(rhs.as_ref(), Expr::Constant(_)) {
            if let Expr::Var(v) = lhs.as_ref() {
                return Some(*v);
            }
        }
    }
    None
}

#[derive(Clone, Debug)]
struct Slot {
    var: Var,
    depth: i64,
}

fn seed_missing(stack: &mut Vec<Slot>, needed: usize) {
    if stack.len() >= needed {
        return;
    }
    // Add missing slots so that the top of stack aligns with the upcoming pops.
    let missing = needed - stack.len();
    for i in 0..missing {
        let depth = (missing - i - 1) as i64;
        stack.insert(
            0,
            Slot {
                var: Var::no_sub(depth as u32),
                depth,
            },
        );
    }
}

/// Attempt to prove a uniform stack shift per iteration and produce affine names.
fn analyze_loop_body(body: &[Stmt], counter: Var) -> Option<VarMap> {
    // Simulate stack with depth indices; top = last element.
    let mut stack: Vec<Slot> = Vec::new();
    let mut entry_depths: HashMap<Var, i64> = HashMap::new();

    for stmt in body {
        match stmt {
            Stmt::StackOp(op) => {
                // Seed missing depths so that pops can occur.
                if op.pops.len() > stack.len() {
                    seed_missing(&mut stack, op.pops.len());
                }

                // Pop requested vars and remember their depths.
                let mut popped: Vec<Slot> = Vec::new();
                for v in op.pops.iter() {
                    if let Some(slot) = stack.pop() {
                        entry_depths.entry(*v).or_insert(slot.depth);
                        popped.push(slot);
                    } else {
                        return None;
                    }
                }
                popped.reverse();

                if op.pushes.len() != op.pops.len() {
                    // Not a pure permutation; cannot derive a stable shift.
                    return None;
                }

                let popped_ids: std::collections::HashSet<_> =
                    popped.iter().map(|s| s.var).collect();
                let pushed_ids: std::collections::HashSet<_> = op.pushes.iter().copied().collect();
                if popped_ids != pushed_ids {
                    return None;
                }

                for dst in &op.pushes {
                    if let Some(slot) = popped.iter().find(|s| s.var == *dst) {
                        stack.push(slot.clone());
                    } else {
                        return None;
                    }
                }
            }
            // Nested control flow can alter stack shape in non-uniform ways; bail out.
            Stmt::If { .. }
            | Stmt::Switch { .. }
            | Stmt::While { .. }
            | Stmt::For { .. }
            | Stmt::RepeatInit { .. }
            | Stmt::RepeatCond { .. }
            | Stmt::RepeatStep { .. }
            | Stmt::Return(_) => return None,
            Stmt::Assign { .. }
            | Stmt::Expr(..)
            | Stmt::Phi { .. }
            | Stmt::Branch(..)
            | Stmt::Instr(..)
            | Stmt::MemLoad(..)
            | Stmt::MemStore(..)
            | Stmt::AdvLoad(..)
            | Stmt::AdvStore(..)
            | Stmt::LocalLoad(..)
            | Stmt::LocalStore(..)
            | Stmt::Call(..)
            | Stmt::Exec(..)
            | Stmt::SysCall(..)
            | Stmt::DynCall { .. }
            | Stmt::Intrinsic(..)
            | Stmt::Unknown
            | Stmt::Nop
            | Stmt::Break
            | Stmt::Continue => {
                // Ignore non-stack mutations.
            }
        }
    }

    let exit_map: HashMap<Var, i64> = stack.iter().map(|s| (s.var, s.depth)).collect();
    if entry_depths.is_empty() || exit_map.is_empty() {
        return None;
    }

    // Check uniform shift: depth_after = depth_before + k.
    let mut shift: Option<i64> = None;
    for (var, before) in entry_depths.iter() {
        if let Some(after) = exit_map.get(var) {
            let delta = after - before;
            if let Some(s) = shift {
                if s != delta {
                    return None;
                }
            } else {
                shift = Some(delta);
            }
        } else {
            return None;
        }
    }

    let k = shift.unwrap_or(0);
    if k == 0 {
        return None;
    }

    let mut result = HashMap::new();
    for (var, base) in entry_depths {
        if exit_map.contains_key(&var) {
            result.insert(
                var,
                IndexExpr::Affine {
                    base,
                    stride: k,
                    counter,
                },
            );
        }
    }
    Some(result)
}
