use std::collections::HashMap;

use crate::{signature::StackEffect, ssa::{Expr, IndexExpr, Stmt, Var}};

/// Compute loop-driven index expressions for variables produced by repeat loops.
pub fn compute_loop_indices(code: &[Stmt]) -> HashMap<Var, IndexExpr> {
    let mut subscripts: HashMap<usize, IndexExpr> = HashMap::new();
    let _ = assign_block(code, &IndexExpr::Const(0), &mut subscripts);
    subscripts
        .into_iter()
        .map(|(idx, expr)| (Var::new(idx), expr))
        .collect()
}

struct BlockSummary {
    effect: StackEffect,
    outputs: Vec<Var>,
}

struct StmtSummary {
    effect: StackEffect,
    outputs: Vec<Var>,
}

fn assign_block(
    code: &[Stmt],
    base_expr: &IndexExpr,
    subscripts: &mut HashMap<usize, IndexExpr>,
) -> bool {
    let mut outputs: Vec<Var> = Vec::new();
    for stmt in code {
        match stmt {
            Stmt::Repeat {
                loop_var,
                loop_count,
                body,
            } => {
                let Some(body_summary) = summarize_block(body) else {
                    return false;
                };
                let per_iter_pops = match effect_parts(body_summary.effect) {
                    Some((pops, _)) => pops,
                    None => return false,
                };
                let per_iter_outputs = body_summary.outputs;
                let delta = per_iter_outputs.len().saturating_sub(per_iter_pops);
                let Some(offset_expr) = add_const(base_expr.clone(), outputs.len()) else {
                    return false;
                };
                let loop_base = if delta > 0 {
                    let loop_term = match mul_loop_var(loop_var.index, delta) {
                        Some(term) => term,
                        None => return false,
                    };
                    match add_index_expr(offset_expr.clone(), loop_term) {
                        Some(expr) => expr,
                        None => return false,
                    }
                } else {
                    offset_expr.clone()
                };

                // Only assign LoopVar-based subscripts for producing loops (delta > 0).
                // For consuming loops (delta <= 0), variables represent accumulator states,
                // not iteration-indexed values. Let the renaming pass assign simple numeric
                // subscripts to consuming loop vars instead.
                if delta > 0 {
                    for (offset, var) in per_iter_outputs.iter().take(delta).enumerate() {
                        let Some(expr) = add_const(loop_base.clone(), offset) else {
                            return false;
                        };
                        insert_subscript(subscripts, var.index, expr);
                    }

                    // Only recurse into the body for producing loops.
                    // This assigns LoopVar subscripts to variables defined inside the loop.
                    if !assign_block(body, &loop_base, subscripts) {
                        return false;
                    }
                }

                let total_effect = match repeat_effect(body_summary.effect, *loop_count) {
                    Some(effect) => effect,
                    None => return false,
                };
                let total_pops = match effect_parts(total_effect) {
                    Some((pops, _)) => pops,
                    None => return false,
                };
                let total_outputs =
                    match repeat_outputs(&per_iter_outputs, per_iter_pops, *loop_count) {
                        Some(outputs) => outputs,
                        None => return false,
                    };
                pop_outputs(&mut outputs, total_pops);
                outputs.extend(total_outputs);
            }
            Stmt::While { body, .. } => {
                let Some(body_summary) = summarize_block(body) else {
                    return false;
                };
                if !effect_is_zero(body_summary.effect) || !body_summary.outputs.is_empty() {
                    return false;
                }
                let Some(offset_expr) = add_const(base_expr.clone(), outputs.len()) else {
                    return false;
                };
                if !assign_block(body, &offset_expr, subscripts) {
                    return false;
                }
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                let Some(then_summary) = summarize_block(then_body) else {
                    return false;
                };
                let Some(else_summary) = summarize_block(else_body) else {
                    return false;
                };
                if !effect_is_zero(then_summary.effect)
                    || !effect_is_zero(else_summary.effect)
                    || !then_summary.outputs.is_empty()
                    || !else_summary.outputs.is_empty()
                {
                    return false;
                }
                let Some(offset_expr) = add_const(base_expr.clone(), outputs.len()) else {
                    return false;
                };
                if !assign_block(then_body, &offset_expr, subscripts) {
                    return false;
                }
                if !assign_block(else_body, &offset_expr, subscripts) {
                    return false;
                }
            }
            _ => {
                let Some(summary) = summarize_stmt(stmt) else {
                    return false;
                };
                let Some((pops, _)) = effect_parts(summary.effect) else {
                    return false;
                };
                pop_outputs(&mut outputs, pops);
                outputs.extend(summary.outputs);
            }
        }
    }
    true
}

fn summarize_block(code: &[Stmt]) -> Option<BlockSummary> {
    let mut outputs: Vec<Var> = Vec::new();
    let mut effect = StackEffect::known(0, 0);
    for stmt in code {
        let summary = summarize_stmt(stmt)?;
        effect = effect.then(summary.effect);
        let (pops, _) = effect_parts(summary.effect)?;
        pop_outputs(&mut outputs, pops);
        outputs.extend(summary.outputs);
    }
    Some(BlockSummary { effect, outputs })
}

fn summarize_stmt(stmt: &Stmt) -> Option<StmtSummary> {
    match stmt {
        Stmt::Assign { dest, expr } => {
            // Simple var-to-var copies (carriers) don't affect stack - they just
            // maintain state across iterations. Treat them as no-ops.
            if matches!(expr, Expr::Var(_)) {
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
        Stmt::Phi { .. } => Some(StmtSummary {
            effect: StackEffect::known(0, 0),
            outputs: Vec::new(),
        }),
        Stmt::Repeat {
            loop_count,
            body,
            ..
        } => {
            let body_summary = summarize_block(body)?;
            let per_iter_effect = body_summary.effect;
            let per_iter_outputs = body_summary.outputs;
            let (per_iter_pops, _) = effect_parts(per_iter_effect)?;
            let total_effect = repeat_effect(per_iter_effect, *loop_count)?;
            let outputs = repeat_outputs(&per_iter_outputs, per_iter_pops, *loop_count)?;
            Some(StmtSummary {
                effect: total_effect,
                outputs,
            })
        }
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            let then_summary = summarize_block(then_body)?;
            let else_summary = summarize_block(else_body)?;
            if !effect_is_zero(then_summary.effect)
                || !effect_is_zero(else_summary.effect)
                || !then_summary.outputs.is_empty()
                || !else_summary.outputs.is_empty()
            {
                return None;
            }
            Some(StmtSummary {
                effect: StackEffect::known(0, 0),
                outputs: Vec::new(),
            })
        }
        Stmt::While { body, .. } => {
            let body_summary = summarize_block(body)?;
            if !effect_is_zero(body_summary.effect) || !body_summary.outputs.is_empty() {
                return None;
            }
            Some(StmtSummary {
                effect: StackEffect::known(0, 0),
                outputs: Vec::new(),
            })
        }
        Stmt::IfBranch(_)
        | Stmt::WhileBranch(_)
        | Stmt::RepeatBranch(_)
        | Stmt::Return(_)
        | Stmt::Inst(_)
        | Stmt::Nop
        | Stmt::Break
        | Stmt::Continue => None,
    }
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

fn effect_is_zero(effect: StackEffect) -> bool {
    matches!(
        effect,
        StackEffect::Known {
            pops: 0,
            pushes: 0,
            ..
        }
    )
}

fn repeat_effect(effect: StackEffect, count: usize) -> Option<StackEffect> {
    let mut acc = StackEffect::known(0, 0);
    for _ in 0..count {
        acc = acc.then(effect);
        if matches!(acc, StackEffect::Unknown) {
            return None;
        }
    }
    Some(acc)
}

fn repeat_outputs(outputs: &[Var], pops: usize, count: usize) -> Option<Vec<Var>> {
    let mut stack: Vec<Var> = Vec::new();
    let total_len = outputs.len().checked_mul(count)?;
    stack.reserve(total_len);
    for _ in 0..count {
        pop_outputs(&mut stack, pops);
        stack.extend(outputs.iter().cloned());
    }
    Some(stack)
}

fn pop_outputs(stack: &mut Vec<Var>, pops: usize) {
    let len = stack.len();
    let keep = len.saturating_sub(pops);
    stack.truncate(keep);
}

fn add_const(base: IndexExpr, offset: usize) -> Option<IndexExpr> {
    let off = i64::try_from(offset).ok()?;
    add_index_expr(base, IndexExpr::Const(off))
}

fn mul_loop_var(loop_idx: usize, factor: usize) -> Option<IndexExpr> {
    let factor = i64::try_from(factor).ok()?;
    let term = IndexExpr::LoopVar(loop_idx);
    mul_index_expr_const(term, factor)
}

fn add_index_expr(lhs: IndexExpr, rhs: IndexExpr) -> Option<IndexExpr> {
    match (lhs, rhs) {
        (IndexExpr::Const(a), IndexExpr::Const(b)) => a.checked_add(b).map(IndexExpr::Const),
        (IndexExpr::Const(0), other) | (other, IndexExpr::Const(0)) => Some(other),
        (a, b) => Some(IndexExpr::Add(Box::new(a), Box::new(b))),
    }
}

fn mul_index_expr_const(expr: IndexExpr, factor: i64) -> Option<IndexExpr> {
    match expr {
        IndexExpr::Const(v) => v.checked_mul(factor).map(IndexExpr::Const),
        other if factor == 0 => Some(IndexExpr::Const(0)),
        other if factor == 1 => Some(other),
        other => Some(IndexExpr::Mul(
            Box::new(IndexExpr::Const(factor)),
            Box::new(other),
        )),
    }
}

fn insert_subscript(
    subscripts: &mut HashMap<usize, IndexExpr>,
    idx: usize,
    expr: IndexExpr,
) {
    let replace = match subscripts.get(&idx) {
        Some(existing) => index_expr_complexity(&expr) > index_expr_complexity(existing),
        None => true,
    };
    if replace {
        subscripts.insert(idx, expr);
    }
}

fn index_expr_complexity(expr: &IndexExpr) -> usize {
    match expr {
        IndexExpr::Const(_) | IndexExpr::LoopVar(_) => 1,
        IndexExpr::Add(a, b) | IndexExpr::Mul(a, b) => {
            1 + index_expr_complexity(a) + index_expr_complexity(b)
        }
    }
}
