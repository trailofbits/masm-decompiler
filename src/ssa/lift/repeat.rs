//! Repeat-loop pattern detection helpers.

use crate::{
    signature::StackEffect,
    ssa::{BinOp, Condition, Constant, Expr, Stmt, Var},
};

#[derive(Debug, Clone)]
pub(super) struct RepeatInfo {
    pub(super) count: usize,
    /// Loop counter variable (iteration index). Allocated during SSA lifting.
    pub(super) loop_var: Option<Var>,
}

#[derive(Debug, Clone)]
pub(super) struct RepeatBodySummary {
    pub(super) pops: usize,
    pub(super) outputs: Vec<Var>,
}

/// Extract a repeat loop count if the block matches the expected pattern.
pub(super) fn extract_repeat_info(code: &[Stmt]) -> Option<RepeatInfo> {
    // Look for a RepeatBranch with a Count condition.
    let count = code.iter().find_map(|stmt| match stmt {
        Stmt::RepeatBranch(Condition::Count { count, .. }) => Some(*count),
        _ => None,
    })?;

    Some(RepeatInfo {
        count,
        loop_var: None,
    })
}

pub(super) fn summarize_repeat_body(
    code: &[Stmt],
    loop_var: &Var,
) -> Option<RepeatBodySummary> {
    let mut outputs: Vec<Var> = Vec::new();
    let mut effect = StackEffect::known(0, 0);
    for stmt in code {
        let summary = summarize_stmt(stmt, loop_var)?;
        effect = effect.then(summary.effect);
        let (pops, _) = effect_parts(summary.effect)?;
        pop_outputs(&mut outputs, pops);
        outputs.extend(summary.outputs);
    }
    let (pops, _) = effect_parts(effect)?;
    Some(RepeatBodySummary { pops, outputs })
}

struct StmtSummary {
    effect: StackEffect,
    outputs: Vec<Var>,
}

fn summarize_stmt(stmt: &Stmt, loop_var: &Var) -> Option<StmtSummary> {
    match stmt {
        Stmt::Assign { dest, expr } => {
            if is_loop_counter_increment(expr, loop_var) {
                return Some(StmtSummary {
                    effect: StackEffect::known(0, 0),
                    outputs: Vec::new(),
                });
            }
            let pops = expr_pops(expr)?;
            let effect = StackEffect::known(pops, 1);
            Some(StmtSummary {
                effect,
                outputs: vec![dest.clone()],
            })
        }
        Stmt::MemLoad(load) => {
            let pops = load.address.len();
            let pushes = load.outputs.len();
            let effect = StackEffect::known(pops, pushes);
            Some(StmtSummary {
                effect,
                outputs: load.outputs.clone(),
            })
        }
        Stmt::MemStore(store) => {
            let pops = store.address.len() + store.values.len();
            let effect = StackEffect::known(pops, 0);
            Some(StmtSummary {
                effect,
                outputs: Vec::new(),
            })
        }
        Stmt::AdvLoad(load) => {
            let pushes = load.outputs.len();
            let effect = StackEffect::known(0, pushes);
            Some(StmtSummary {
                effect,
                outputs: load.outputs.clone(),
            })
        }
        Stmt::AdvStore(store) => {
            let pops = store.values.len();
            let effect = StackEffect::known(pops, 0);
            Some(StmtSummary {
                effect,
                outputs: Vec::new(),
            })
        }
        Stmt::LocalLoad(load) => {
            let pushes = load.outputs.len();
            let effect = StackEffect::known(0, pushes);
            Some(StmtSummary {
                effect,
                outputs: load.outputs.clone(),
            })
        }
        Stmt::LocalStore(store) => {
            let pops = store.values.len();
            let effect = StackEffect::known(pops, 0);
            Some(StmtSummary {
                effect,
                outputs: Vec::new(),
            })
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            let pops = call.args.len();
            let pushes = call.results.len();
            let effect = StackEffect::known(pops, pushes);
            Some(StmtSummary {
                effect,
                outputs: call.results.clone(),
            })
        }
        Stmt::DynCall { args, results } => {
            let pops = args.len();
            let pushes = results.len();
            let effect = StackEffect::known(pops, pushes);
            Some(StmtSummary {
                effect,
                outputs: results.clone(),
            })
        }
        Stmt::Intrinsic(intr) => {
            let pops = intr.args.len();
            let pushes = intr.results.len();
            let effect = StackEffect::known(pops, pushes);
            Some(StmtSummary {
                effect,
                outputs: intr.results.clone(),
            })
        }
        Stmt::Phi { .. } | Stmt::Nop => Some(StmtSummary {
            effect: StackEffect::known(0, 0),
            outputs: Vec::new(),
        }),
        Stmt::IfBranch(_)
        | Stmt::WhileBranch(_)
        | Stmt::RepeatBranch(_)
        | Stmt::Return(_)
        | Stmt::Inst(_)
        | Stmt::Repeat { .. }
        | Stmt::If { .. }
        | Stmt::While { .. }
        | Stmt::Break
        | Stmt::Continue => None,
    }
}

fn is_loop_counter_increment(expr: &Expr, loop_var: &Var) -> bool {
    match expr {
        Expr::Binary(BinOp::Add, lhs, rhs) => {
            (is_var(lhs, loop_var) && is_one(rhs)) || (is_var(rhs, loop_var) && is_one(lhs))
        }
        _ => false,
    }
}

fn is_var(expr: &Expr, var: &Var) -> bool {
    matches!(expr, Expr::Var(v) if v == var)
}

fn is_one(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(Constant::Felt(1)))
}

fn expr_pops(expr: &Expr) -> Option<usize> {
    match expr {
        Expr::Binary(_, _, _) => Some(2),
        Expr::Unary(_, _) => Some(1),
        Expr::Var(_) | Expr::Constant(_) | Expr::True => Some(0),
        Expr::Unknown => None,
    }
}

fn effect_parts(effect: StackEffect) -> Option<(usize, usize)> {
    match effect {
        StackEffect::Known { pops, pushes, .. } => Some((pops, pushes)),
        StackEffect::Unknown => None,
    }
}

fn pop_outputs(stack: &mut Vec<Var>, pops: usize) {
    let len = stack.len();
    let keep = len.saturating_sub(pops);
    stack.truncate(keep);
}
