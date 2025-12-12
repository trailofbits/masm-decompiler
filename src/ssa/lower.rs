use miden_assembly_syntax::ast::{Immediate, Instruction, InvocationTarget, Op, Procedure};

use crate::{
    cfg::{Cfg, Edge, NodeId},
    signature::{InstructionEffect, ProcSignature, SignatureMap, stack_effect},
};

use std::collections::{HashMap, HashSet};

use super::{
    AdvLoad, AdvStore, BinOp, Call, Constant, Expr, Intrinsic, LocalId, LocalLoad, LocalStore,
    MemLoad, MemStore, StackOp, Stmt, UnOp, Var,
};

#[derive(Clone, PartialEq)]
struct Frame {
    stack: Vec<Var>,
    locals: HashMap<LocalId, Var>,
    inputs: u32,
    unknown: bool,
    exprs: HashMap<Var, Expr>,
}

#[derive(Default, Clone)]
struct PhiInfo {
    var: Option<Var>,
    sources: Vec<Var>,
    seen_preds: HashSet<NodeId>,
}

#[derive(Default, Clone)]
struct BlockPhiState {
    stack: Vec<PhiInfo>,
    locals: HashMap<LocalId, PhiInfo>,
}

/// Result of lowering a procedure body into SSA-like stack ops.
#[derive(Debug)]
pub struct LowerResult {
    pub code: Vec<Stmt>,
    pub inputs: u32,
    pub outputs: u32,
}

/// Lower a procedure body to a linear SSA-ish sequence of `Stmt::StackOp`, inserting
/// `Unknown` when stack effects are not known. Control-flow is ignored for now; this
/// is intended to be replaced by a CFG-aware lowering but provides early coverage and tests.
pub fn lower_proc_to_ssa(proc: &Procedure, module_path: &str, sigs: &SignatureMap) -> LowerResult {
    let mut state = LowerState::new();
    for op in proc.body().iter() {
        state.lower_op(op, module_path, sigs);
    }
    LowerResult {
        code: state.code,
        inputs: state.inputs,
        outputs: state.stack.len() as u32,
    }
}

/// Result of CFG-aware lowering.
#[derive(Debug)]
pub struct CfgLowerResult {
    pub cfg: Cfg,
    pub inputs: u32,
    pub outputs: Option<u32>,
}

/// Lower a CFG of a procedure to SSA-style stack ops, inserting `Unknown` when stack
/// effects or merge shapes are not known. This is a conservative, simplified analogue of
/// rewasm's SSA construction.
pub fn lower_cfg_to_ssa(
    mut cfg: Cfg,
    module_path: &str,
    proc_path: &str,
    sigs: &SignatureMap,
) -> CfgLowerResult {
    let original_codes: Vec<Vec<Stmt>> = cfg.nodes.iter().map(|n| n.code.clone()).collect();
    let mut in_state: Vec<Option<Frame>> = vec![None; cfg.nodes.len()];
    let mut phi_state: Vec<BlockPhiState> = vec![BlockPhiState::default(); cfg.nodes.len()];
    let mut queue: Vec<NodeId> = Vec::new();
    let mut ctx = LowerCtx::new();
    let mut def_cache: Vec<Vec<Vec<Var>>> = vec![Vec::new(); cfg.nodes.len()];
    // Seed entry stack when we know the exact input count; otherwise allow underflows to
    // synthesize arguments.
    let mut entry_stack = Vec::new();
    let mut entry_exprs = HashMap::new();
    if let Some(ProcSignature::Known { inputs, .. }) = sigs.signatures.get(proc_path) {
        for _ in 0..inputs.min {
            let v = ctx.fresh_var();
            entry_exprs.insert(v, Expr::Var(v));
            entry_stack.push(v);
        }
    }
    let entry_inputs = entry_stack.len() as u32;
    in_state[0] = Some(Frame {
        stack: entry_stack,
        locals: HashMap::new(),
        inputs: entry_inputs,
        unknown: false,
        exprs: entry_exprs,
    });
    queue.push(0);

    // Worklist traversal including back-edges; should converge quickly for small graphs.
    let mut iters = 0;
    while let Some(node) = queue.pop() {
        iters += 1;
        if iters > 10_000 {
            // Avoid runaway in pathological graphs
            break;
        }
        let frame = match &in_state[node] {
            Some(f) => f.clone(),
            None => continue,
        };
        let mut state = frame.clone();
        if std::env::var("DEBUG_LOOP").is_ok() {
            eprintln!(
                "enter block {node} with stack_len {} locals {:?} unknown {}",
                state.stack.len(),
                state.locals.keys().collect::<Vec<_>>(),
                state.unknown
            );
        }
        let mut new_code: Vec<Stmt> = Vec::new();
        let orig_code = original_codes[node].clone();

        // Emit PHIs at block entry if needed
        if let Some(phis) = phi_state.get(node) {
            for phi in &phis.stack {
                if let Some(var) = phi.var {
                    if phi.sources.len() > 1 {
                        new_code.push(Stmt::Phi {
                            var,
                            sources: phi.sources.clone(),
                        });
                    }
                }
            }
            let mut local_keys: Vec<_> = phis.locals.keys().copied().collect();
            local_keys.sort();
            for k in local_keys {
                if let Some(phi) = phis.locals.get(&k) {
                    if let Some(var) = phi.var {
                        if phi.sources.len() > 1 {
                            new_code.push(Stmt::Phi {
                                var,
                                sources: phi.sources.clone(),
                            });
                        }
                    }
                }
            }
        }

        if state.unknown {
            new_code.push(Stmt::Unknown);
        } else {
            for (stmt_idx, stmt) in orig_code.iter().enumerate() {
                let mut alloc = alloc_scope(&mut def_cache, node, stmt_idx);
                match stmt {
                    Stmt::Instr(inst) => {
                        if let Some(stmt) = lower_inst_to_stmt(
                            inst,
                            module_path,
                            sigs,
                            &mut state,
                            &mut ctx,
                            &mut alloc,
                        ) {
                            new_code.push(stmt);
                            if state.unknown {
                                break;
                            }
                        } else {
                            new_code.push(Stmt::Unknown);
                            state.stack.clear();
                            state.unknown = true;
                            break;
                        }
                    }
                    Stmt::Unknown => {
                        if std::env::var("DEBUG_LOOP").is_ok() {
                            eprintln!("lower: encountered Unknown stmt in block {node}");
                        }
                        new_code.push(Stmt::Unknown);
                        state.stack.clear();
                        state.unknown = true;
                        break;
                    }
                    Stmt::RepeatInit { local, count: _ } => {
                        let var = alloc.alloc(&mut ctx);
                        let expr = Expr::Constant(Constant::Felt(0));
                        state.locals.insert(*local, var);
                        state.exprs.insert(var, expr.clone());
                        new_code.push(Stmt::Assign { dst: var, expr });
                    }
                    Stmt::RepeatCond { local, count } => {
                        let counter = match state.locals.get(local) {
                            Some(v) => *v,
                            None => {
                                if std::env::var("DEBUG_LOOP").is_ok() {
                                    eprintln!(
                                        "lower: missing counter local for RepeatCond in block {node}"
                                    );
                                }
                                new_code.push(Stmt::Unknown);
                                state.stack.clear();
                                state.unknown = true;
                                break;
                            }
                        };
                        let cond_var = ctx
                            .push_many_with_alloc(&mut state, 1, &mut alloc)
                            .pop()
                            .unwrap();
                        let cond_expr = Expr::BinOp(
                            BinOp::Lt,
                            Box::new(Expr::Var(counter)),
                            Box::new(Expr::Constant(Constant::Felt(*count as u64))),
                        );
                        state.exprs.insert(cond_var, cond_expr.clone());
                        new_code.push(Stmt::Assign {
                            dst: cond_var,
                            expr: cond_expr,
                        });
                    }
                    Stmt::RepeatStep { local } => {
                        let counter = match state.locals.get(local) {
                            Some(v) => *v,
                            None => {
                                if std::env::var("DEBUG_LOOP").is_ok() {
                                    eprintln!(
                                        "lower: missing counter local for RepeatStep in block {node}"
                                    );
                                }
                                new_code.push(Stmt::Unknown);
                                state.stack.clear();
                                state.unknown = true;
                                break;
                            }
                        };
                        let new_counter = alloc.alloc(&mut ctx);
                        let expr = Expr::BinOp(
                            BinOp::Add,
                            Box::new(Expr::Var(counter)),
                            Box::new(Expr::Constant(Constant::Felt(1))),
                        );
                        state.locals.insert(*local, new_counter);
                        state.exprs.insert(new_counter, expr.clone());
                        new_code.push(Stmt::Assign {
                            dst: new_counter,
                            expr,
                        });
                    }
                    _ => new_code.push(stmt.clone()),
                }
            }
        }

        cfg.nodes[node].code = new_code;

        // Consume branch condition if this block has a conditional edge
        if !state.unknown {
            let has_conditional = cfg.nodes[node]
                .next
                .iter()
                .any(|e| matches!(e.cond.edge_type, crate::cfg::EdgeType::Conditional(_)));
            if has_conditional {
                let mut tmp_alloc = FreshAlloc;
                let cond_var = ctx
                    .pop_many_with_alloc(&mut state, 1, &mut tmp_alloc)
                    .pop()
                    .unwrap();
                let cond_expr = state
                    .exprs
                    .get(&cond_var)
                    .cloned()
                    .unwrap_or(Expr::Var(cond_var));
                cfg.nodes[node].code.push(Stmt::Branch(cond_expr));
            }
        }

        if std::env::var("DEBUG_LOOP").is_ok() {
            eprintln!(
                "after block {node} code len {} stack_len {} locals {:?} unknown {}",
                cfg.nodes[node].code.len(),
                state.stack.len(),
                state.locals.keys().collect::<Vec<_>>(),
                state.unknown
            );
        }

        if !state.unknown {
            let mut live: HashSet<Var> = state.stack.iter().copied().collect();
            live.extend(state.locals.values().copied());
            state.exprs.retain(|k, _| live.contains(k));
        }

        // Propagate to successors
        for Edge {
            node: succ,
            back_edge: _,
            ..
        } in cfg.nodes[node].next.clone()
        {
            let next_frame = if state.unknown {
                Frame {
                    stack: Vec::new(),
                    locals: HashMap::new(),
                    inputs: state.inputs,
                    unknown: true,
                    exprs: HashMap::new(),
                }
            } else {
                Frame {
                    stack: state.stack.clone(),
                    locals: state.locals.clone(),
                    inputs: state.inputs,
                    unknown: false,
                    exprs: state.exprs.clone(),
                }
            };
            if std::env::var("DEBUG_LOOP").is_ok() {
                eprintln!(
                    "propagate from {node} to {succ} with stack_len={} locals={:?} unknown={}",
                    next_frame.stack.len(),
                    next_frame.locals.keys().collect::<Vec<_>>(),
                    next_frame.unknown
                );
            }
            let updated = merge_into_block(
                succ,
                node,
                &next_frame,
                &mut in_state,
                &mut phi_state,
                &mut ctx,
            );
            if updated {
                queue.push(succ);
            }
        }
    }

    let inputs = in_state
        .iter()
        .filter_map(|f| f.as_ref().map(|f| f.inputs))
        .max()
        .unwrap_or(0);
    let mut outputs: Option<u32> = None;
    for (idx, bb) in cfg.nodes.iter().enumerate() {
        let has_forward_succ = bb.next.iter().any(|e| !e.back_edge);
        if !has_forward_succ {
            if let Some(frame) = &in_state[idx] {
                if frame.unknown {
                    outputs = None;
                    break;
                }
                match outputs {
                    None => outputs = Some(frame.stack.len() as u32),
                    Some(prev) if prev == frame.stack.len() as u32 => {}
                    _ => {
                        outputs = None;
                        break;
                    }
                }
            }
        }
    }

    CfgLowerResult {
        cfg,
        inputs,
        outputs,
    }
}

fn merge_into_block(
    block: NodeId,
    pred: NodeId,
    incoming: &Frame,
    in_state: &mut [Option<Frame>],
    phi_state: &mut [BlockPhiState],
    ctx: &mut LowerCtx,
) -> bool {
    match &in_state[block] {
        None => {
            in_state[block] = Some(incoming.clone());
            let mut phi = BlockPhiState::default();
            phi.stack = vec![PhiInfo::default(); incoming.stack.len()];
            for k in incoming.locals.keys() {
                phi.locals.insert(*k, PhiInfo::default());
            }
            phi_state[block] = phi;
            true
        }
        Some(existing) => {
            if existing.unknown || incoming.unknown {
                if std::env::var("DEBUG_LOOP").is_ok() {
                    eprintln!("merge: unknown frame at block {block}");
                }
                let new_frame = Frame {
                    stack: Vec::new(),
                    locals: HashMap::new(),
                    inputs: existing.inputs.max(incoming.inputs),
                    unknown: true,
                    exprs: HashMap::new(),
                };
                let changed = in_state[block].as_ref() != Some(&new_frame);
                in_state[block] = Some(new_frame);
                return changed;
            }
            let mut existing_stack = existing.stack.clone();
            let mut incoming_stack = incoming.stack.clone();
            if existing_stack.len() != incoming_stack.len() {
                let target_len = existing_stack.len().max(incoming_stack.len());
                if std::env::var("DEBUG_LOOP").is_ok() {
                    eprintln!(
                        "merge: stack len mismatch at block {block}: {} vs {}, padding to {target_len}",
                        existing_stack.len(),
                        incoming_stack.len()
                    );
                }
                while existing_stack.len() < target_len {
                    existing_stack.push(ctx.fresh_var());
                }
                while incoming_stack.len() < target_len {
                    incoming_stack.push(ctx.fresh_var());
                }
                if let Some(phi) = phi_state.get_mut(block) {
                    if phi.stack.len() < target_len {
                        phi.stack.resize_with(target_len, PhiInfo::default);
                    }
                }
            }

            let existing_keys: HashSet<_> = existing.locals.keys().copied().collect();
            let incoming_keys: HashSet<_> = incoming.locals.keys().copied().collect();
            if existing_keys != incoming_keys {
                if std::env::var("DEBUG_LOOP").is_ok() {
                    eprintln!(
                        "merge: local key mismatch at block {block}: {:?} vs {:?}",
                        existing_keys, incoming_keys
                    );
                }
                let new_frame = Frame {
                    stack: Vec::new(),
                    locals: HashMap::new(),
                    inputs: existing.inputs.max(incoming.inputs),
                    unknown: true,
                    exprs: HashMap::new(),
                };
                let changed = in_state[block].as_ref() != Some(&new_frame);
                in_state[block] = Some(new_frame);
                return changed;
            }

            let mut changed = false;
            let mut new_locals = existing.locals.clone();
            let mut new_exprs = existing.exprs.clone();
            let phis = phi_state.get_mut(block).unwrap();
            let target_len = existing_stack.len().max(incoming_stack.len());
            if phis.stack.len() < target_len {
                phis.stack.resize_with(target_len, PhiInfo::default);
            }

            let mut new_stack: Vec<Var> = Vec::with_capacity(target_len);
            for i in 0..target_len {
                match (existing_stack.get(i), incoming_stack.get(i)) {
                    (Some(cur), Some(inc_raw)) => {
                        let phi_slot = &mut phis.stack[i];
                        let mut inc = *inc_raw;
                        if let Some(phi_var) = phi_slot.var {
                            if phi_slot.seen_preds.contains(&pred) {
                                inc = phi_var;
                            }
                        }

                        if cur != &inc {
                            let phi_var = phi_slot.var.unwrap_or_else(|| {
                                let v = ctx.fresh_var();
                                phi_slot.var = Some(v);
                                v
                            });
                            if phi_slot.sources.is_empty() {
                                phi_slot.sources.push(*cur);
                            }
                            if !phi_slot.sources.contains(&inc) {
                                phi_slot.sources.push(inc);
                            }
                            phi_slot.seen_preds.insert(pred);
                            new_stack.push(phi_var);
                            new_exprs.insert(phi_var, Expr::Var(phi_var));
                            changed = true;
                        } else {
                            phi_slot.seen_preds.insert(pred);
                            if let Some(expr) = incoming.exprs.get(cur).cloned() {
                                new_exprs.insert(*cur, expr);
                            }
                            new_stack.push(*cur);
                        }
                    }
                    (Some(cur), None) => {
                        new_stack.push(*cur);
                        if let Some(expr) = existing.exprs.get(cur).cloned() {
                            new_exprs.insert(*cur, expr);
                        }
                    }
                    (None, Some(inc)) => {
                        new_stack.push(*inc);
                        if let Some(expr) = incoming.exprs.get(inc).cloned() {
                            new_exprs.insert(*inc, expr);
                        }
                        changed = true;
                    }
                    (None, None) => {}
                }
            }

            for k in existing_keys.iter() {
                let phi_slot = phis.locals.entry(*k).or_default();
                let cur = existing.locals.get(k).copied().unwrap();
                let mut inc = incoming.locals.get(k).copied().unwrap();
                if let Some(phi_var) = phi_slot.var {
                    if phi_slot.seen_preds.contains(&pred) {
                        inc = phi_var;
                    }
                }

                if cur != inc {
                    let phi_var = phi_slot.var.unwrap_or_else(|| {
                        let v = ctx.fresh_var();
                        phi_slot.var = Some(v);
                        v
                    });
                    if phi_slot.sources.is_empty() {
                        phi_slot.sources.push(cur);
                    }
                    if !phi_slot.sources.contains(&inc) {
                        phi_slot.sources.push(inc);
                    }
                    phi_slot.seen_preds.insert(pred);
                    new_locals.insert(*k, phi_var);
                    new_exprs.insert(phi_var, Expr::Var(phi_var));
                    changed = true;
                } else {
                    phi_slot.seen_preds.insert(pred);
                    if let Some(expr) = incoming.exprs.get(&cur).cloned() {
                        new_exprs.insert(cur, expr);
                    }
                }
            }

            let new_inputs = existing.inputs.max(incoming.inputs);
            let new_frame = Frame {
                stack: new_stack,
                locals: new_locals,
                inputs: new_inputs,
                unknown: false,
                exprs: new_exprs,
            };
            let changed_frame = in_state[block]
                .as_ref()
                .map(|prev| {
                    prev.stack != new_frame.stack
                        || prev.locals != new_frame.locals
                        || prev.inputs != new_frame.inputs
                        || prev.unknown != new_frame.unknown
                })
                .unwrap_or(true);
            if changed_frame {
                changed = true;
            }
            in_state[block] = Some(new_frame);
            changed
        }
    }
}

fn lower_effect_for_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
) -> Option<(u32, u32)> {
    match inst {
        Instruction::Exec(t) | Instruction::Call(t) | Instruction::SysCall(t) => {
            call_effect(t, module_path, sigs)
        }
        Instruction::DynExec | Instruction::DynCall => None,
        _ => match stack_effect(inst) {
            InstructionEffect::Known { pops, pushes, .. } => Some((pops as u32, pushes as u32)),
            InstructionEffect::Unknown => None,
        },
    }
}

fn lower_inst_to_stmt(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut LowerCtx,
    alloc: &mut impl VarAlloc,
) -> Option<Stmt> {
    match inst {
        Instruction::Exec(t) => lower_call_like(
            t,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
            Stmt::Exec,
        ),
        Instruction::Call(t) => lower_call_like(
            t,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
            Stmt::Call,
        ),
        Instruction::SysCall(t) => lower_call_like(
            t,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
            Stmt::SysCall,
        ),
        Instruction::DynExec | Instruction::DynCall => {
            state.stack.clear();
            state.unknown = true;
            Some(Stmt::DynCall {
                args: Vec::new(),
                results: Vec::new(),
            })
        }
        Instruction::Add => Some(lower_binop(inst.clone(), BinOp::Add, state, ctx, alloc)),
        Instruction::AddImm(imm) => Some(lower_binop_imm(
            inst.clone(),
            BinOp::Add,
            imm.clone(),
            state,
            ctx,
            alloc,
        )),
        Instruction::Sub => Some(lower_binop(inst.clone(), BinOp::Sub, state, ctx, alloc)),
        Instruction::SubImm(imm) => Some(lower_binop_imm(
            inst.clone(),
            BinOp::Sub,
            imm.clone(),
            state,
            ctx,
            alloc,
        )),
        Instruction::Mul => Some(lower_binop(inst.clone(), BinOp::Mul, state, ctx, alloc)),
        Instruction::MulImm(imm) => Some(lower_binop_imm(
            inst.clone(),
            BinOp::Mul,
            imm.clone(),
            state,
            ctx,
            alloc,
        )),
        Instruction::Div => Some(lower_binop(inst.clone(), BinOp::Div, state, ctx, alloc)),
        Instruction::DivImm(imm) => Some(lower_binop_imm(
            inst.clone(),
            BinOp::Div,
            imm.clone(),
            state,
            ctx,
            alloc,
        )),
        Instruction::And => Some(lower_binop(inst.clone(), BinOp::And, state, ctx, alloc)),
        Instruction::Or => Some(lower_binop(inst.clone(), BinOp::Or, state, ctx, alloc)),
        Instruction::Xor => Some(lower_binop(inst.clone(), BinOp::Xor, state, ctx, alloc)),
        Instruction::Eq => Some(lower_binop(inst.clone(), BinOp::Eq, state, ctx, alloc)),
        Instruction::EqImm(imm) => Some(lower_binop_imm(
            inst.clone(),
            BinOp::Eq,
            imm.clone(),
            state,
            ctx,
            alloc,
        )),
        Instruction::Neq => Some(lower_binop(inst.clone(), BinOp::Neq, state, ctx, alloc)),
        Instruction::Lt => Some(lower_binop(inst.clone(), BinOp::Lt, state, ctx, alloc)),
        Instruction::Lte => Some(lower_binop(inst.clone(), BinOp::Lte, state, ctx, alloc)),
        Instruction::Gt => Some(lower_binop(inst.clone(), BinOp::Gt, state, ctx, alloc)),
        Instruction::Gte => Some(lower_binop(inst.clone(), BinOp::Gte, state, ctx, alloc)),
        Instruction::Not => Some(lower_unop(inst.clone(), UnOp::Not, state, ctx, alloc)),
        Instruction::Neg => Some(lower_unop(inst.clone(), UnOp::Neg, state, ctx, alloc)),
        Instruction::Drop => {
            let v = ctx.pop_many_with_alloc(state, 1, alloc).pop().unwrap();
            Some(Stmt::StackOp(StackOp {
                inst: inst.clone(),
                pops: vec![v],
                pushes: vec![],
            }))
        }
        Instruction::PadW => {
            let pushed = ctx.push_many_with_alloc(state, 4, alloc);
            Some(Stmt::StackOp(StackOp {
                inst: inst.clone(),
                pops: vec![],
                pushes: pushed,
            }))
        }
        Instruction::Dup0
        | Instruction::Dup1
        | Instruction::Dup2
        | Instruction::Dup3
        | Instruction::Dup4
        | Instruction::Dup5
        | Instruction::Dup6
        | Instruction::Dup7
        | Instruction::Dup8
        | Instruction::Dup9
        | Instruction::Dup10
        | Instruction::Dup11
        | Instruction::Dup12
        | Instruction::Dup13
        | Instruction::Dup14
        | Instruction::Dup15 => {
            let idx = dup_index(inst)? as usize;
            while state.stack.len() <= idx {
                let v = alloc.alloc(ctx);
                state.inputs += 1;
                state.stack.push(v);
            }
            let _slot = state.stack[state.stack.len() - idx - 1];
            let pushed = ctx.push_many_with_alloc(state, 1, alloc);
            Some(Stmt::StackOp(StackOp {
                inst: inst.clone(),
                pops: vec![],
                pushes: pushed,
            }))
        }
        Instruction::Swap1
        | Instruction::Swap2
        | Instruction::Swap3
        | Instruction::Swap4
        | Instruction::Swap5
        | Instruction::Swap6
        | Instruction::Swap7
        | Instruction::Swap8
        | Instruction::Swap9
        | Instruction::Swap10
        | Instruction::Swap11
        | Instruction::Swap12
        | Instruction::Swap13
        | Instruction::Swap14
        | Instruction::Swap15 => {
            let idx = swap_index(inst)? as usize;
            while state.stack.len() < idx + 1 {
                let v = alloc.alloc(ctx);
                state.inputs += 1;
                state.stack.push(v);
            }
            let top = state.stack.pop().unwrap();
            let tgt_index = state.stack.len() - idx;
            let other = state.stack.get_mut(tgt_index)?;
            let tmp = *other;
            *other = top;
            state.stack.push(tmp);
            Some(Stmt::StackOp(StackOp {
                inst: inst.clone(),
                pops: vec![top, tmp],
                pushes: vec![tmp, top],
            }))
        }
        Instruction::MemLoad
        | Instruction::MemLoadImm(_)
        | Instruction::MemLoadWBe
        | Instruction::MemLoadWBeImm(_)
        | Instruction::MemLoadWLe
        | Instruction::MemLoadWLeImm(_) => {
            let (pops, pushes) = lower_effect_for_inst(inst, module_path, sigs)?;
            let address = ctx.pop_many_with_alloc(state, pops, alloc);
            let outputs = ctx.push_many_with_alloc(state, pushes, alloc);
            Some(Stmt::MemLoad(MemLoad { address, outputs }))
        }
        Instruction::MemStore
        | Instruction::MemStoreImm(_)
        | Instruction::MemStoreWBe
        | Instruction::MemStoreWBeImm(_)
        | Instruction::MemStoreWLe
        | Instruction::MemStoreWLeImm(_) => {
            let (pops, _pushes) = lower_effect_for_inst(inst, module_path, sigs)?;
            let args = ctx.pop_many_with_alloc(state, pops, alloc);
            Some(Stmt::MemStore(MemStore {
                address: Vec::new(),
                values: args,
            }))
        }
        Instruction::LocLoad(idx) | Instruction::LocLoadWBe(idx) | Instruction::LocLoadWLe(idx) => {
            let (pops, pushes) = lower_effect_for_inst(inst, module_path, sigs)?;
            let _ = ctx.pop_many_with_alloc(state, pops, alloc);
            let outputs = ctx.push_many_with_alloc(state, pushes, alloc);
            Some(Stmt::LocalLoad(LocalLoad {
                index: idx.expect_value(),
                outputs,
            }))
        }
        Instruction::LocStore(idx)
        | Instruction::LocStoreWBe(idx)
        | Instruction::LocStoreWLe(idx) => {
            let (pops, _pushes) = lower_effect_for_inst(inst, module_path, sigs)?;
            let values = ctx.pop_many_with_alloc(state, pops, alloc);
            Some(Stmt::LocalStore(LocalStore {
                index: idx.expect_value(),
                values,
            }))
        }
        Instruction::AdvLoadW => {
            let (pops, pushes) = lower_effect_for_inst(inst, module_path, sigs)?;
            let _ = ctx.pop_many_with_alloc(state, pops, alloc);
            let outputs = ctx.push_many_with_alloc(state, pushes, alloc);
            Some(Stmt::AdvLoad(AdvLoad { outputs }))
        }
        Instruction::AdvPush(_) | Instruction::AdvPipe => {
            let (pops, _pushes) = lower_effect_for_inst(inst, module_path, sigs)?;
            let values = ctx.pop_many_with_alloc(state, pops, alloc);
            Some(Stmt::AdvStore(AdvStore { values }))
        }
        Instruction::Hash => lower_intrinsic("hash", inst, module_path, sigs, state, ctx, alloc),
        Instruction::HMerge => {
            lower_intrinsic("hmerge", inst, module_path, sigs, state, ctx, alloc)
        }
        Instruction::HPerm => lower_intrinsic("hperm", inst, module_path, sigs, state, ctx, alloc),
        Instruction::MTreeGet => {
            lower_intrinsic("mtree_get", inst, module_path, sigs, state, ctx, alloc)
        }
        Instruction::MTreeSet => {
            lower_intrinsic("mtree_set", inst, module_path, sigs, state, ctx, alloc)
        }
        Instruction::MTreeMerge => lower_intrinsic(
            "mtree_merge",
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::MTreeVerify => lower_intrinsic(
            "mtree_verify",
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::MTreeVerifyWithError(err) => lower_intrinsic(
            &format!("mtree_verify_{err}"),
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::CryptoStream => lower_intrinsic(
            "crypto_stream",
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::FriExt2Fold4 => lower_intrinsic(
            "fri_ext2fold4",
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::HornerBase => lower_intrinsic(
            "horner_eval_base",
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::HornerExt => lower_intrinsic(
            "horner_eval_ext",
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::LogPrecompile => lower_intrinsic(
            "log_precompile",
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::EvalCircuit => lower_intrinsic(
            "eval_circuit",
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::Emit => {
            lower_intrinsic("emit", inst, module_path, sigs, state, ctx, alloc)
        }
        Instruction::EmitImm(imm) => lower_intrinsic(
            &format!("emit_{imm}"),
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::Trace(kind) => lower_intrinsic(
            &format!("trace_{kind}"),
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::SysEvent(event) => lower_intrinsic(
            &format!("sys_event_{event:?}"),
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        ),
        Instruction::Push(imm) => {
            let pushed = ctx.push_many_with_alloc(state, 1, alloc);
            if let Some(dst) = pushed.last() {
                let expr = expr_from_push_immediate(imm);
                state.exprs.insert(*dst, expr.clone());
                Some(Stmt::Assign { dst: *dst, expr })
            } else {
                None
            }
        }
        // Default: use raw stack effect
        _ => {
            if let Some((pops, pushes)) = lower_effect_for_inst(inst, module_path, sigs) {
                let popped = ctx.pop_many_with_alloc(state, pops, alloc);
                let pushed = ctx.push_many_with_alloc(state, pushes, alloc);
                Some(Stmt::StackOp(StackOp {
                    inst: inst.clone(),
                    pops: popped,
                    pushes: pushed,
                }))
            } else {
                None
            }
        }
    }
}

fn lower_call_like<F>(
    target: &InvocationTarget,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut LowerCtx,
    alloc: &mut impl VarAlloc,
    ctor: F,
) -> Option<Stmt>
where
    F: Fn(Call) -> Stmt,
{
    if let Some((pops, pushes)) = call_effect(target, module_path, sigs) {
        let popped = ctx.pop_many_with_alloc(state, pops, alloc);
        let pushed = ctx.push_many_with_alloc(state, pushes, alloc);
        let name = call_name(target, module_path)?;
        return Some(ctor(Call {
            target: name,
            args: popped,
            results: pushed,
        }));
    }
    None
}

fn lower_intrinsic(
    name: impl Into<String>,
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut LowerCtx,
    alloc: &mut impl VarAlloc,
) -> Option<Stmt> {
    if let Some((pops, pushes)) = lower_effect_for_inst(inst, module_path, sigs) {
        let args = ctx.pop_many_with_alloc(state, pops, alloc);
        let results = ctx.push_many_with_alloc(state, pushes, alloc);
        return Some(Stmt::Intrinsic(Intrinsic {
            name: name.into(),
            args,
            results,
        }));
    }
    None
}

fn lower_binop(
    _inst: Instruction,
    op: BinOp,
    state: &mut Frame,
    ctx: &mut LowerCtx,
    alloc: &mut impl VarAlloc,
) -> Stmt {
    let b = ctx.pop_many_with_alloc(state, 1, alloc).pop().unwrap();
    let a = ctx.pop_many_with_alloc(state, 1, alloc).pop().unwrap();
    let res = ctx.push_many_with_alloc(state, 1, alloc).pop().unwrap();
    let expr = Expr::BinOp(
        op,
        Box::new(ctx.lookup_expr(state, a)),
        Box::new(ctx.lookup_expr(state, b)),
    );
    state.exprs.insert(res, expr.clone());
    Stmt::Assign { dst: res, expr }
}

fn lower_unop(
    _inst: Instruction,
    op: UnOp,
    state: &mut Frame,
    ctx: &mut LowerCtx,
    alloc: &mut impl VarAlloc,
) -> Stmt {
    let a = ctx.pop_many_with_alloc(state, 1, alloc).pop().unwrap();
    let res = ctx.push_many_with_alloc(state, 1, alloc).pop().unwrap();
    let expr = Expr::Unary(op, Box::new(ctx.lookup_expr(state, a)));
    state.exprs.insert(res, expr.clone());
    Stmt::Assign { dst: res, expr }
}

fn lower_binop_imm(
    _inst: Instruction,
    op: BinOp,
    imm: miden_assembly_syntax::ast::ImmFelt,
    state: &mut Frame,
    ctx: &mut LowerCtx,
    alloc: &mut impl VarAlloc,
) -> Stmt {
    let a = ctx.pop_many_with_alloc(state, 1, alloc).pop().unwrap();
    let res = ctx.push_many_with_alloc(state, 1, alloc).pop().unwrap();
    let rhs = expr_from_felt_immediate(&imm);
    let expr = Expr::BinOp(op, Box::new(ctx.lookup_expr(state, a)), Box::new(rhs));
    state.exprs.insert(res, expr.clone());
    Stmt::Assign { dst: res, expr }
}

fn dup_index(inst: &Instruction) -> Option<u8> {
    match inst {
        Instruction::Dup0 => Some(0),
        Instruction::Dup1 => Some(1),
        Instruction::Dup2 => Some(2),
        Instruction::Dup3 => Some(3),
        Instruction::Dup4 => Some(4),
        Instruction::Dup5 => Some(5),
        Instruction::Dup6 => Some(6),
        Instruction::Dup7 => Some(7),
        Instruction::Dup8 => Some(8),
        Instruction::Dup9 => Some(9),
        Instruction::Dup10 => Some(10),
        Instruction::Dup11 => Some(11),
        Instruction::Dup12 => Some(12),
        Instruction::Dup13 => Some(13),
        Instruction::Dup14 => Some(14),
        Instruction::Dup15 => Some(15),
        _ => None,
    }
}

fn swap_index(inst: &Instruction) -> Option<u8> {
    match inst {
        Instruction::Swap1 => Some(1),
        Instruction::Swap2 => Some(2),
        Instruction::Swap3 => Some(3),
        Instruction::Swap4 => Some(4),
        Instruction::Swap5 => Some(5),
        Instruction::Swap6 => Some(6),
        Instruction::Swap7 => Some(7),
        Instruction::Swap8 => Some(8),
        Instruction::Swap9 => Some(9),
        Instruction::Swap10 => Some(10),
        Instruction::Swap11 => Some(11),
        Instruction::Swap12 => Some(12),
        Instruction::Swap13 => Some(13),
        Instruction::Swap14 => Some(14),
        Instruction::Swap15 => Some(15),
        _ => None,
    }
}

fn expr_from_felt_immediate(imm: &miden_assembly_syntax::ast::ImmFelt) -> Expr {
    match imm {
        Immediate::Value(_span) => Expr::Constant(Constant::from(imm.clone())),
        Immediate::Constant(id) => Expr::Constant(Constant::Defined(id.to_string())),
    }
}

fn expr_from_push_immediate(imm: &Immediate<miden_assembly_syntax::parser::PushValue>) -> Expr {
    match imm {
        Immediate::Value(span) => Expr::Constant(Constant::from(span.inner().clone())),
        Immediate::Constant(id) => Expr::Constant(Constant::Defined(id.to_string())),
    }
}

fn call_effect(
    target: &InvocationTarget,
    module_path: &str,
    sigs: &SignatureMap,
) -> Option<(u32, u32)> {
    let callee = call_name(target, module_path)?;
    match sigs.signatures.get(&callee) {
        Some(ProcSignature::Known {
            inputs, outputs, ..
        }) => {
            let in_min = inputs.min;
            let out_min = outputs.min;
            let out_max = outputs.max?;
            if Some(out_min) != Some(out_max) || inputs.max != Some(in_min) {
                return None;
            }
            Some((in_min, out_min))
        }
        _ => None,
    }
}

fn call_name(target: &InvocationTarget, module_path: &str) -> Option<String> {
    let name = match target {
        InvocationTarget::Symbol(ident) => format!("{module_path}::{}", ident.as_str()),
        InvocationTarget::Path(path) => path.to_string(),
        InvocationTarget::MastRoot(_) => return None,
    };
    Some(name)
}

trait VarAlloc {
    fn alloc(&mut self, ctx: &mut LowerCtx) -> Var;
}

struct AllocScope<'a> {
    cache: &'a mut Vec<Var>,
    cursor: usize,
}

impl<'a> VarAlloc for AllocScope<'a> {
    fn alloc(&mut self, ctx: &mut LowerCtx) -> Var {
        if let Some(existing) = self.cache.get(self.cursor).copied() {
            self.cursor += 1;
            existing
        } else {
            let v = ctx.fresh_var();
            self.cache.push(v);
            self.cursor += 1;
            v
        }
    }
}

struct FreshAlloc;

impl VarAlloc for FreshAlloc {
    fn alloc(&mut self, ctx: &mut LowerCtx) -> Var {
        ctx.fresh_var()
    }
}

fn alloc_scope<'a>(
    def_cache: &'a mut Vec<Vec<Vec<Var>>>,
    node: NodeId,
    stmt_idx: usize,
) -> AllocScope<'a> {
    if def_cache.len() <= node {
        def_cache.resize_with(node + 1, Vec::new);
    }
    if def_cache[node].len() <= stmt_idx {
        def_cache[node].resize_with(stmt_idx + 1, Vec::new);
    }
    let cache = &mut def_cache[node][stmt_idx];
    AllocScope { cache, cursor: 0 }
}

struct LowerCtx {
    next_var: u32,
}

impl LowerCtx {
    fn new() -> Self {
        Self { next_var: 0 }
    }

    fn fresh_var(&mut self) -> Var {
        let v = Var::no_sub(self.next_var);
        self.next_var += 1;
        v
    }

    fn lookup_expr(&self, frame: &Frame, var: Var) -> Expr {
        frame.exprs.get(&var).cloned().unwrap_or(Expr::Var(var))
    }

    fn pop_many_with_alloc<A: VarAlloc>(
        &mut self,
        state: &mut LowerStateFrame,
        count: u32,
        alloc: &mut A,
    ) -> Vec<Var> {
        let mut out = Vec::with_capacity(count as usize);
        for _ in 0..count {
            if let Some(v) = state.stack.pop() {
                out.push(v);
            } else {
                let var = alloc.alloc(self);
                state.inputs += 1;
                out.push(var);
            }
        }
        out
    }

    fn push_many_with_alloc<A: VarAlloc>(
        &mut self,
        state: &mut LowerStateFrame,
        count: u32,
        alloc: &mut A,
    ) -> Vec<Var> {
        let mut vars = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let v = alloc.alloc(self);
            state.stack.push(v);
            vars.push(v);
        }
        vars
    }
}

type LowerStateFrame = Frame;

struct LowerState {
    stack: Vec<Var>,
    next_var: u32,
    inputs: u32,
    code: Vec<Stmt>,
    exprs: HashMap<Var, Expr>,
}

impl LowerState {
    fn new() -> Self {
        Self {
            stack: Vec::new(),
            next_var: 0,
            inputs: 0,
            code: Vec::new(),
            exprs: HashMap::new(),
        }
    }

    fn lower_op(&mut self, op: &Op, module_path: &str, sigs: &SignatureMap) {
        match op {
            Op::Inst(inst) => self.lower_inst(inst.inner(), module_path, sigs),
            Op::If { .. } | Op::Repeat { .. } | Op::While { .. } => {
                // Control flow not handled in linear lowering; treat as unknown barrier.
                self.code.push(Stmt::Unknown);
                self.stack.clear();
            }
        }
    }

    fn lower_inst(&mut self, inst: &Instruction, module_path: &str, sigs: &SignatureMap) {
        match inst {
            Instruction::Exec(t) => self.lower_call_like(t, module_path, sigs, Stmt::Exec),
            Instruction::Call(t) => self.lower_call_like(t, module_path, sigs, Stmt::Call),
            Instruction::SysCall(t) => self.lower_call_like(t, module_path, sigs, Stmt::SysCall),
            Instruction::DynExec | Instruction::DynCall => {
                self.code.push(Stmt::DynCall {
                    args: Vec::new(),
                    results: Vec::new(),
                });
                self.stack.clear();
            }
            Instruction::Push(imm) => {
                let pushed = self.push_many(1);
                if let Some(dst) = pushed.last() {
                    let expr = expr_from_push_immediate(imm);
                    self.code.push(Stmt::Assign { dst: *dst, expr });
                } else {
                    self.code.push(Stmt::Unknown);
                    self.stack.clear();
                }
            }
            Instruction::MemLoad
            | Instruction::MemLoadImm(_)
            | Instruction::MemLoadWBe
            | Instruction::MemLoadWBeImm(_)
            | Instruction::MemLoadWLe
            | Instruction::MemLoadWLeImm(_)
            | Instruction::LocLoad(_)
            | Instruction::LocLoadWBe(_)
            | Instruction::LocLoadWLe(_) => match stack_effect(inst) {
                InstructionEffect::Known { pops, pushes, .. } => {
                    let _ = self.pop_many(pops as u32);
                    let outputs = self.push_many(pushes as u32);
                    if let Instruction::LocLoad(idx)
                    | Instruction::LocLoadWBe(idx)
                    | Instruction::LocLoadWLe(idx) = inst
                    {
                        self.code.push(Stmt::LocalLoad(LocalLoad {
                            index: idx.expect_value(),
                            outputs,
                        }));
                    } else {
                        self.code.push(Stmt::MemLoad(MemLoad {
                            address: Vec::new(),
                            outputs,
                        }));
                    }
                }
                InstructionEffect::Unknown => {
                    self.code.push(Stmt::Unknown);
                    self.stack.clear();
                }
            },
            Instruction::MemStore
            | Instruction::MemStoreImm(_)
            | Instruction::MemStoreWBe
            | Instruction::MemStoreWBeImm(_)
            | Instruction::MemStoreWLe
            | Instruction::MemStoreWLeImm(_)
            | Instruction::LocStore(_)
            | Instruction::LocStoreWBe(_)
            | Instruction::LocStoreWLe(_) => match stack_effect(inst) {
                InstructionEffect::Known { pops, .. } => {
                    let args = self.pop_many(pops as u32);
                    if let Instruction::LocStore(idx)
                    | Instruction::LocStoreWBe(idx)
                    | Instruction::LocStoreWLe(idx) = inst
                    {
                        self.code.push(Stmt::LocalStore(LocalStore {
                            index: idx.expect_value(),
                            values: args,
                        }));
                    } else {
                        self.code.push(Stmt::MemStore(MemStore {
                            address: Vec::new(),
                            values: args,
                        }));
                    }
                }
                InstructionEffect::Unknown => {
                    self.code.push(Stmt::Unknown);
                    self.stack.clear();
                }
            },
            Instruction::AdvLoadW => match stack_effect(inst) {
                InstructionEffect::Known { pops, pushes, .. } => {
                    let _ = self.pop_many(pops as u32);
                    let outputs = self.push_many(pushes as u32);
                    self.code.push(Stmt::AdvLoad(AdvLoad { outputs }));
                }
                InstructionEffect::Unknown => {
                    self.code.push(Stmt::Unknown);
                    self.stack.clear();
                }
            },
            Instruction::AdvPush(_) | Instruction::AdvPipe => match stack_effect(inst) {
                InstructionEffect::Known { pops, .. } => {
                    let values = self.pop_many(pops as u32);
                    self.code.push(Stmt::AdvStore(AdvStore { values }));
                }
                InstructionEffect::Unknown => {
                    self.code.push(Stmt::Unknown);
                    self.stack.clear();
                }
            },
            Instruction::Hash
            | Instruction::HMerge
            | Instruction::HPerm
            | Instruction::MTreeGet
            | Instruction::MTreeSet
            | Instruction::MTreeMerge
            | Instruction::MTreeVerify
            | Instruction::MTreeVerifyWithError(_)
            | Instruction::CryptoStream
            | Instruction::FriExt2Fold4
            | Instruction::HornerBase
            | Instruction::HornerExt
            | Instruction::LogPrecompile
            | Instruction::EvalCircuit
            | Instruction::Emit
            | Instruction::EmitImm(_)
            | Instruction::Trace(_)
            | Instruction::SysEvent(_) => match stack_effect(inst) {
                InstructionEffect::Known { pops, pushes, .. } => {
                    let args = self.pop_many(pops as u32);
                    let results = self.push_many(pushes as u32);
                    self.code.push(Stmt::Intrinsic(Intrinsic {
                        name: format!("{inst:?}"),
                        args,
                        results,
                    }));
                }
                InstructionEffect::Unknown => {
                    self.code.push(Stmt::Unknown);
                    self.stack.clear();
                }
            },
            _ => match stack_effect(inst) {
                InstructionEffect::Known { pops, pushes, .. } => {
                    let popped = self.pop_many(pops as u32);
                    let pushed = self.push_many(pushes as u32);
                    self.code.push(Stmt::StackOp(StackOp {
                        inst: inst.clone(),
                        pops: popped,
                        pushes: pushed,
                    }));
                }
                InstructionEffect::Unknown => {
                    self.code.push(Stmt::Unknown);
                    self.stack.clear();
                }
            },
        }
    }

    fn lower_call_like<F>(
        &mut self,
        target: &InvocationTarget,
        module_path: &str,
        sigs: &SignatureMap,
        ctor: F,
    ) where
        F: Fn(Call) -> Stmt,
    {
        if let Some((pops, pushes)) = self.call_effect(target, module_path, sigs) {
            let args = self.pop_many(pops);
            let results = self.push_many(pushes);
            let name = call_name(target, module_path).unwrap_or_else(|| "<unknown>".to_string());
            self.code.push(ctor(Call {
                target: name,
                args,
                results,
            }));
        } else {
            self.code.push(Stmt::Unknown);
            self.stack.clear();
        }
    }

    fn call_effect(
        &self,
        target: &InvocationTarget,
        module_path: &str,
        sigs: &SignatureMap,
    ) -> Option<(u32, u32)> {
        let callee = match target {
            InvocationTarget::Symbol(ident) => format!("{module_path}::{}", ident.as_str()),
            InvocationTarget::Path(path) => path.to_string(),
            InvocationTarget::MastRoot(_) => return None,
        };
        match sigs.signatures.get(&callee) {
            Some(ProcSignature::Known {
                inputs, outputs, ..
            }) => {
                let in_min = inputs.min;
                let out_min = outputs.min;
                let out_max = outputs.max?;
                if Some(out_min) != Some(out_max) || inputs.max != Some(in_min) {
                    return None;
                }
                Some((in_min, out_min))
            }
            _ => None,
        }
    }

    fn pop_many(&mut self, count: u32) -> Vec<Var> {
        let mut out = Vec::with_capacity(count as usize);
        for _ in 0..count {
            if let Some(v) = self.stack.pop() {
                out.push(v);
            } else {
                let var = Var::no_sub(self.next_var);
                self.next_var += 1;
                self.inputs += 1;
                out.push(var);
            }
        }
        out
    }

    fn push_many(&mut self, count: u32) -> Vec<Var> {
        let mut vars = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let v = Var::no_sub(self.next_var);
            self.next_var += 1;
            self.stack.push(v);
            vars.push(v);
            self.exprs.insert(v, Expr::Unknown);
        }
        vars
    }
}
