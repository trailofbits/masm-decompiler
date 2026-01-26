//! Phi-node construction and stack reconciliation for SSA lifting.

use std::collections::{HashSet, VecDeque};

use crate::cfg::NodeId;

use super::context::{Frame, SsaContext};
use super::repeat::RepeatInfo;
use super::{SsaError, SsaResult};
use crate::ssa::{Expr, SsaStack, Stmt, Var};

/// Per-stack-slot phi information for a block.
#[derive(Default, Clone)]
pub(super) struct PhiInfo {
    /// Phi variable assigned to this stack slot, if any.
    pub(super) var: Option<Var>,
    /// Incoming source variables seen so far.
    pub(super) sources: Vec<Var>,
    /// Predecessors that have contributed to this phi.
    pub(super) seen_preds: HashSet<NodeId>,
}

/// Per-block phi state tracked during merging.
#[derive(Default, Clone)]
pub(super) struct BlockPhiState {
    /// Phi metadata per stack slot.
    pub(super) stack: Vec<PhiInfo>,
}

/// Emit phi statements for any stack slots with multiple sources.
pub(super) fn emit_phis(phis: &BlockPhiState, code: &mut Vec<Stmt>) {
    for phi in &phis.stack {
        if let Some(var) = &phi.var {
            if phi.sources.len() > 1 {
                code.push(Stmt::Phi {
                    var: var.clone(),
                    sources: phi.sources.clone(),
                });
            }
        }
    }
}

/// Reconcile stack lengths across edges, handling repeat loops on back edges.
pub(super) fn reconcile_stack_len(
    block: NodeId,
    is_back_edge: bool,
    existing_stack: &mut SsaStack,
    incoming_stack: &mut SsaStack,
    repeat_infos: &[Option<RepeatInfo>],
    base_stack_len: &[Option<usize>],
    phi_state: &mut [BlockPhiState],
    ctx: &mut SsaContext,
) -> SsaResult<usize> {
    let existing_len = existing_stack.len();
    let incoming_len = incoming_stack.len();
    if existing_len == incoming_len {
        return Ok(existing_len);
    }
    if !is_back_edge {
        return Err(SsaError::UnbalancedIf);
    }
    if repeat_infos.get(block).and_then(|r| r.as_ref()).is_none() {
        if std::env::var("DEBUG_SSA").is_ok() {
            eprintln!(
                "non-neutral while at block {}: existing_len {}, incoming_len {}",
                block, existing_len, incoming_len
            );
        }
        return Err(SsaError::NonNeutralWhile);
    }
    let target_len = base_stack_len
        .get(block)
        .and_then(|v| *v)
        .unwrap_or(existing_len);
    if incoming_len > target_len {
        incoming_stack.truncate_front(target_len);
    } else if incoming_len < target_len {
        let padding = target_len - incoming_len;
        incoming_stack.pad_front(padding, || ctx.new_var());
    }
    if let Some(phi) = phi_state.get_mut(block) {
        if phi.stack.len() < target_len {
            phi.stack.resize_with(target_len, PhiInfo::default);
        } else if phi.stack.len() > target_len {
            phi.stack.truncate(target_len);
        }
    }
    Ok(target_len)
}

/// Merge an incoming frame into a block, updating phi state and stack vars.
pub(super) fn merge_into_block(
    block: NodeId,
    pred: NodeId,
    is_back_edge: bool,
    incoming: &Frame,
    in_state: &mut [Option<Frame>],
    phi_state: &mut [BlockPhiState],
    repeat_infos: &[Option<RepeatInfo>],
    base_stack_len: &mut [Option<usize>],
    ctx: &mut SsaContext,
) -> SsaResult<bool> {
    match &in_state[block] {
        None => {
            in_state[block] = Some(incoming.clone());
            base_stack_len[block] = Some(incoming.stack.len());
            let mut phi = BlockPhiState::default();
            phi.stack = vec![PhiInfo::default(); incoming.stack.len()];
            phi_state[block] = phi;
            Ok(true)
        }
        Some(existing) => {
            let mut existing_stack = existing.stack.clone();
            let mut incoming_stack = incoming.stack.clone();
            let target_len = reconcile_stack_len(
                block,
                is_back_edge,
                &mut existing_stack,
                &mut incoming_stack,
                repeat_infos,
                base_stack_len,
                phi_state,
                ctx,
            )?;

            let mut changed = false;
            let mut new_exprs = existing.exprs.clone();
            let phis = phi_state.get_mut(block).unwrap();
            if phis.stack.len() < target_len {
                phis.stack.resize_with(target_len, PhiInfo::default);
            } else if phis.stack.len() > target_len {
                phis.stack.truncate(target_len);
            }

            let mut new_stack: VecDeque<Var> = VecDeque::with_capacity(target_len);
            for i in 0..target_len {
                let existing_var = existing_stack.get(i).unwrap();
                let mut incoming_var = incoming_stack.get(i).unwrap();
                let phi_slot = &mut phis.stack[i];
                if let Some(phi_var) = &phi_slot.var {
                    if phi_slot.seen_preds.contains(&pred) {
                        incoming_var = phi_var.clone();
                    }
                }

                if existing_var != incoming_var {
                    let phi_var = phi_slot.var.clone().unwrap_or_else(|| {
                        let v = ctx.new_var();
                        phi_slot.var = Some(v.clone());
                        v
                    });
                    if phi_slot.sources.is_empty() {
                        phi_slot.sources.push(existing_var);
                    }
                    if !phi_slot.sources.contains(&incoming_var) {
                        phi_slot.sources.push(incoming_var);
                    }
                    phi_slot.seen_preds.insert(pred);
                    new_stack.push_back(phi_var.clone());
                    new_exprs.insert(phi_var.clone(), Expr::Var(phi_var));
                    changed = true;
                } else {
                    phi_slot.seen_preds.insert(pred);
                    if let Some(expr) = incoming.exprs.get(&existing_var).cloned() {
                        new_exprs.insert(existing_var.clone(), expr);
                    }
                    new_stack.push_back(existing_var);
                }
            }

            let new_required_depth = existing
                .stack
                .required_depth()
                .max(incoming.stack.required_depth());
            let new_frame = Frame {
                stack: SsaStack::from_parts(new_stack, new_required_depth),
                exprs: new_exprs,
            };
            let changed_frame = in_state[block]
                .as_ref()
                .map(|prev| prev.stack != new_frame.stack)
                .unwrap_or(true);
            if changed_frame {
                changed = true;
            }
            in_state[block] = Some(new_frame);
            Ok(changed)
        }
    }
}
