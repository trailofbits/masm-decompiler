use miden_assembly_syntax::ast::{Immediate, Instruction, InvocationTarget, Op, Procedure};

use crate::{
    cfg::{Cfg, Edge, NodeId},
    signature::{stack_effect, InstructionEffect, ProcSignature, SignatureMap},
};

use std::collections::HashMap;

use super::{BinOp, Constant, Expr, StackOp, Stmt, UnOp, Var};

#[derive(Clone, PartialEq)]
struct Frame {
    stack: Vec<Var>,
    inputs: u32,
    unknown: bool,
    exprs: HashMap<Var, Expr>,
}

#[derive(Default, Clone)]
struct PhiInfo {
    var: Option<Var>,
    sources: Vec<Var>,
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
pub fn lower_proc_to_ssa(
    proc: &Procedure,
    module_path: &str,
    sigs: &SignatureMap,
) -> LowerResult {
    let mut state = LowerState::new();
    for op in proc.body().iter() {
        state.lower_op(op, module_path, sigs);
    }
    LowerResult { code: state.code, inputs: state.inputs, outputs: state.stack.len() as u32 }
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
    sigs: &SignatureMap,
) -> CfgLowerResult {
    let mut in_state: Vec<Option<Frame>> = vec![None; cfg.nodes.len()];
    let mut phi_state: Vec<Vec<PhiInfo>> = vec![Vec::new(); cfg.nodes.len()];
    let mut queue: Vec<NodeId> = Vec::new();
    let mut ctx = LowerCtx { next_var: 0 };
    in_state[0] = Some(Frame { stack: Vec::new(), inputs: 0, unknown: false, exprs: HashMap::new() });
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
        let mut new_code: Vec<Stmt> = Vec::new();
        let orig_code = cfg.nodes[node].code.clone();

        // Emit PHIs at block entry if needed
        if let Some(phis) = phi_state.get(node) {
            for phi in phis {
                if let Some(var) = phi.var {
                    if phi.sources.len() > 1 {
                        new_code.push(Stmt::Phi { var, sources: phi.sources.clone() });
                    }
                }
            }
        }

        if state.unknown {
            new_code.push(Stmt::Unknown);
        } else {
            for stmt in orig_code.iter() {
                match stmt {
                    Stmt::Instr(inst) => {
                        if let Some(stmt) =
                            lower_inst_to_stmt(inst, module_path, sigs, &mut state, &mut ctx)
                        {
                            new_code.push(stmt);
                        } else {
                            new_code.push(Stmt::Unknown);
                            state.stack.clear();
                            state.unknown = true;
                            break;
                        }
                    }
                    Stmt::Unknown => {
                        new_code.push(Stmt::Unknown);
                        state.stack.clear();
                        state.unknown = true;
                        break;
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
                let cond_var = ctx.pop_many(&mut state, 1).pop().unwrap();
                let cond_expr = state.exprs.get(&cond_var).cloned().unwrap_or(Expr::Var(cond_var));
                cfg.nodes[node].code.push(Stmt::Branch(cond_expr));
            }
        }

        // Propagate to successors
        for Edge { node: succ, back_edge: _, .. } in cfg.nodes[node].next.clone() {
            let next_frame = if state.unknown {
                Frame { stack: Vec::new(), inputs: state.inputs, unknown: true, exprs: HashMap::new() }
            } else {
                Frame { stack: state.stack.clone(), inputs: state.inputs, unknown: false, exprs: state.exprs.clone() }
            };
            let updated =
                merge_into_block(succ, &next_frame, &mut in_state, &mut phi_state, &mut ctx);
            if updated {
                queue.push(succ);
            }
        }
    }

    let inputs = in_state.iter().filter_map(|f| f.as_ref().map(|f| f.inputs)).max().unwrap_or(0);
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

    CfgLowerResult { cfg, inputs, outputs }
}

fn merge_into_block(
    block: NodeId,
    incoming: &Frame,
    in_state: &mut [Option<Frame>],
    phi_state: &mut [Vec<PhiInfo>],
    ctx: &mut LowerCtx,
) -> bool {
    match &in_state[block] {
        None => {
            in_state[block] = Some(incoming.clone());
            phi_state[block] = vec![PhiInfo::default(); incoming.stack.len()];
            true
        }
        Some(existing) => {
            if existing.unknown || incoming.unknown {
                let new_frame = Frame {
                    stack: Vec::new(),
                    inputs: existing.inputs.max(incoming.inputs),
                    unknown: true,
                    exprs: HashMap::new(),
                };
                let changed = in_state[block].as_ref() != Some(&new_frame);
                in_state[block] = Some(new_frame);
                return changed;
            }
            if existing.stack.len() != incoming.stack.len() {
                let new_frame = Frame {
                    stack: Vec::new(),
                    inputs: existing.inputs.max(incoming.inputs),
                    unknown: true,
                    exprs: HashMap::new(),
                };
                let changed = in_state[block].as_ref() != Some(&new_frame);
                in_state[block] = Some(new_frame);
                return changed;
            }

            let mut changed = false;
            let mut new_stack = existing.stack.clone();
            let mut new_exprs = existing.exprs.clone();
            let phis = phi_state.get_mut(block).unwrap();
            if phis.len() < new_stack.len() {
                phis.resize_with(new_stack.len(), PhiInfo::default);
            }

            for (i, (cur, inc)) in existing.stack.iter().zip(incoming.stack.iter()).enumerate() {
                if cur == inc {
                    continue;
                }
                let phi_slot = &mut phis[i];
                let phi_var = phi_slot.var.unwrap_or_else(|| {
                    let v = Var::no_sub(ctx.next_var);
                    ctx.next_var += 1;
                    phi_slot.var = Some(v);
                    v
                });
                let mut sources = vec![*cur, *inc];
                sources.sort();
                sources.dedup();
                phi_slot.sources = sources;
                let merged_expr = match (existing.exprs.get(cur), incoming.exprs.get(inc)) {
                    (Some(a), Some(b)) if a == b => a.clone(),
                    _ => Expr::Unknown,
                };
                new_exprs.insert(phi_var, merged_expr);
                new_stack[i] = phi_var;
                changed = true;
            }

            let new_inputs = existing.inputs.max(incoming.inputs);
            let new_frame = Frame { stack: new_stack, inputs: new_inputs, unknown: false, exprs: new_exprs };
            if in_state[block].as_ref() != Some(&new_frame) {
                in_state[block] = Some(new_frame);
                changed = true;
            }
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
) -> Option<Stmt> {
    match inst {
        Instruction::Exec(t) | Instruction::Call(t) | Instruction::SysCall(t) => {
            if let Some((pops, pushes)) = call_effect(t, module_path, sigs) {
                let popped = ctx.pop_many(state, pops);
                let pushed = ctx.push_many(state, pushes);
                return Some(Stmt::StackOp(StackOp {
                    inst: inst.clone(),
                    pops: popped,
                    pushes: pushed,
                }));
            }
            None
        }
        Instruction::DynExec | Instruction::DynCall => None,
        Instruction::Add => Some(lower_binop(inst.clone(), BinOp::Add, state, ctx)),
        Instruction::AddImm(imm) => Some(lower_binop_imm(inst.clone(), BinOp::Add, imm.clone(), state, ctx)),
        Instruction::Sub => Some(lower_binop(inst.clone(), BinOp::Sub, state, ctx)),
        Instruction::SubImm(imm) => Some(lower_binop_imm(inst.clone(), BinOp::Sub, imm.clone(), state, ctx)),
        Instruction::Mul => Some(lower_binop(inst.clone(), BinOp::Mul, state, ctx)),
        Instruction::MulImm(imm) => Some(lower_binop_imm(inst.clone(), BinOp::Mul, imm.clone(), state, ctx)),
        Instruction::Div => Some(lower_binop(inst.clone(), BinOp::Div, state, ctx)),
        Instruction::DivImm(imm) => Some(lower_binop_imm(inst.clone(), BinOp::Div, imm.clone(), state, ctx)),
        Instruction::And => Some(lower_binop(inst.clone(), BinOp::And, state, ctx)),
        Instruction::Or => Some(lower_binop(inst.clone(), BinOp::Or, state, ctx)),
        Instruction::Xor => Some(lower_binop(inst.clone(), BinOp::Xor, state, ctx)),
        Instruction::Eq => Some(lower_binop(inst.clone(), BinOp::Eq, state, ctx)),
        Instruction::EqImm(imm) => Some(lower_binop_imm(inst.clone(), BinOp::Eq, imm.clone(), state, ctx)),
        Instruction::Neq => Some(lower_binop(inst.clone(), BinOp::Neq, state, ctx)),
        Instruction::Lt => Some(lower_binop(inst.clone(), BinOp::Lt, state, ctx)),
        Instruction::Lte => Some(lower_binop(inst.clone(), BinOp::Lte, state, ctx)),
        Instruction::Gt => Some(lower_binop(inst.clone(), BinOp::Gt, state, ctx)),
        Instruction::Gte => Some(lower_binop(inst.clone(), BinOp::Gte, state, ctx)),
        Instruction::Not => Some(lower_unop(inst.clone(), UnOp::Not, state, ctx)),
        Instruction::Neg => Some(lower_unop(inst.clone(), UnOp::Neg, state, ctx)),
        Instruction::Drop => {
            let v = ctx.pop_many(state, 1).pop().unwrap();
            Some(Stmt::StackOp(StackOp { inst: inst.clone(), pops: vec![v], pushes: vec![] }))
        }
        Instruction::PadW => {
            let pushed = ctx.push_many(state, 4);
            Some(Stmt::StackOp(StackOp { inst: inst.clone(), pops: vec![], pushes: pushed }))
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
            if state.stack.len() <= idx {
                return None;
            }
            let _slot = state.stack[state.stack.len() - idx - 1];
            let pushed = ctx.push_many(state, 1);
            Some(Stmt::StackOp(StackOp { inst: inst.clone(), pops: vec![], pushes: pushed }))
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
            if state.stack.len() < idx + 1 {
                return None;
            }
            let top = state.stack.pop().unwrap();
            let tgt_index = state.stack.len() - idx;
            let other = state.stack.get_mut(tgt_index)?;
            let tmp = *other;
            *other = top;
            state.stack.push(tmp);
            Some(Stmt::StackOp(StackOp { inst: inst.clone(), pops: vec![], pushes: vec![] }))
        }
        Instruction::Push(imm) => {
            let pushed = ctx.push_many(state, 1);
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
                let popped = ctx.pop_many(state, pops);
                let pushed = ctx.push_many(state, pushes);
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

fn lower_binop(_inst: Instruction, op: BinOp, state: &mut Frame, ctx: &mut LowerCtx) -> Stmt {
    let b = ctx.pop_many(state, 1).pop().unwrap();
    let a = ctx.pop_many(state, 1).pop().unwrap();
    let res = ctx.push_many(state, 1).pop().unwrap();
    let expr = Expr::BinOp(op, Box::new(ctx.lookup_expr(state, a)), Box::new(ctx.lookup_expr(state, b)));
    state.exprs.insert(res, expr.clone());
    Stmt::Assign {
        dst: res,
        expr,
    }
}

fn lower_unop(_inst: Instruction, op: UnOp, state: &mut Frame, ctx: &mut LowerCtx) -> Stmt {
    let a = ctx.pop_many(state, 1).pop().unwrap();
    let res = ctx.push_many(state, 1).pop().unwrap();
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
) -> Stmt {
    let a = ctx.pop_many(state, 1).pop().unwrap();
    let res = ctx.push_many(state, 1).pop().unwrap();
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
    let callee = match target {
        InvocationTarget::Symbol(ident) => format!("{module_path}::{}", ident.as_str()),
        InvocationTarget::Path(path) => path.to_string(),
        InvocationTarget::MastRoot(_) => return None,
    };
    match sigs.signatures.get(&callee) {
        Some(ProcSignature::Known { inputs, outputs, .. }) => {
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

struct LowerCtx {
    next_var: u32,
}

impl LowerCtx {
    fn lookup_expr(&self, frame: &Frame, var: Var) -> Expr {
        frame.exprs.get(&var).cloned().unwrap_or(Expr::Var(var))
    }
}

impl LowerCtx {
    fn pop_many(&mut self, state: &mut LowerStateFrame, count: u32) -> Vec<Var> {
        let mut out = Vec::with_capacity(count as usize);
        for _ in 0..count {
            if let Some(v) = state.stack.pop() {
                out.push(v);
            } else {
                let var = Var::no_sub(self.next_var);
                self.next_var += 1;
                state.inputs += 1;
                out.push(var);
            }
        }
        out
    }

    fn push_many(&mut self, state: &mut LowerStateFrame, count: u32) -> Vec<Var> {
        let mut vars = Vec::with_capacity(count as usize);
        for _ in 0..count {
            let v = Var::no_sub(self.next_var);
            self.next_var += 1;
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
        Self { stack: Vec::new(), next_var: 0, inputs: 0, code: Vec::new(), exprs: HashMap::new() }
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

    fn lower_inst(
        &mut self,
        inst: &Instruction,
        module_path: &str,
        sigs: &SignatureMap,
    ) {
        match inst {
            Instruction::Exec(t)
            | Instruction::Call(t)
            | Instruction::SysCall(t) => {
                if let Some((pops, pushes)) = self.call_effect(t, module_path, sigs) {
                    let popped = self.pop_many(pops);
                    let pushed = self.push_many(pushes);
                    self.code.push(Stmt::StackOp(StackOp {
                        inst: inst.clone(),
                        pops: popped,
                        pushes: pushed,
                    }));
                } else {
                    self.code.push(Stmt::Unknown);
                    self.stack.clear();
                }
            }
            Instruction::DynExec | Instruction::DynCall => {
                self.code.push(Stmt::Unknown);
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
            Some(ProcSignature::Known { inputs, outputs, .. }) => {
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
