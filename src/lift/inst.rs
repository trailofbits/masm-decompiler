//! Instruction-level lifting from MASM to IR statements.

use miden_assembly_syntax::ast::{ImmFelt, ImmU32, Immediate, Instruction, InvocationTarget};

use crate::ir::{
    AdvLoad, BinOp, Call, Constant, Expr, Intrinsic, LocalLoad, LocalStore, MemLoad, MemStore,
    Stmt, UnOp, Var,
};
use crate::signature::{SignatureMap, StackEffect};

use super::stack::SymbolicStack;
use super::{LiftingError, LiftingResult, LoopContext};

/// Lift a single instruction into one or more IR statements.
pub(super) fn lift_inst(
    inst: &Instruction,
    stack: &mut SymbolicStack,
    _loop_ctx: &mut LoopContext,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<Vec<Stmt>> {
    // Try each instruction category in turn.
    if let Some(stmts) = lift_call_inst(inst, module_path, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_arith_inst(inst, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_stack_inst(inst, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_mem_inst(inst, module_path, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_local_inst(inst, module_path, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_adv_inst(inst, module_path, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_intrinsic_inst(inst, module_path, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_push_inst(inst, stack)? {
        return Ok(stmts);
    }
    Err(LiftingError::UnsupportedInstruction(inst.clone()))
}

/// Lift call-like instructions (`exec`, `call`, `syscall`).
fn lift_call_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    let stmts = match inst {
        Instruction::Exec(t) => {
            vec![lift_call_like(t, module_path, sigs, stack, Stmt::Exec)?]
        }
        Instruction::Call(t) => {
            vec![lift_call_like(t, module_path, sigs, stack, Stmt::Call)?]
        }
        Instruction::SysCall(t) => {
            vec![lift_call_like(t, module_path, sigs, stack, Stmt::SysCall)?]
        }
        Instruction::DynExec | Instruction::DynCall => {
            return Err(LiftingError::UnsupportedInstruction(inst.clone()));
        }
        _ => return Ok(None),
    };
    Ok(Some(stmts))
}

/// Lift arithmetic and comparison instructions.
fn lift_arith_inst(
    inst: &Instruction,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    let stmt = match inst {
        Instruction::Add => lift_binop(BinOp::Add, stack),
        Instruction::AddImm(imm) => lift_binop_imm(BinOp::Add, imm, stack),
        Instruction::Sub => lift_binop(BinOp::Sub, stack),
        Instruction::SubImm(imm) => lift_binop_imm(BinOp::Sub, imm, stack),
        Instruction::Mul => lift_binop(BinOp::Mul, stack),
        Instruction::MulImm(imm) => lift_binop_imm(BinOp::Mul, imm, stack),
        Instruction::Div => lift_binop(BinOp::Div, stack),
        Instruction::DivImm(imm) => lift_binop_imm(BinOp::Div, imm, stack),
        Instruction::And => lift_binop(BinOp::And, stack),
        Instruction::Or => lift_binop(BinOp::Or, stack),
        Instruction::Xor => lift_binop(BinOp::Xor, stack),
        Instruction::Eq => lift_binop(BinOp::Eq, stack),
        Instruction::EqImm(imm) => lift_binop_imm(BinOp::Eq, imm, stack),
        Instruction::Neq => lift_binop(BinOp::Neq, stack),
        Instruction::NeqImm(imm) => lift_binop_imm(BinOp::Neq, imm, stack),
        Instruction::Lt => lift_binop(BinOp::Lt, stack),
        Instruction::Lte => lift_binop(BinOp::Lte, stack),
        Instruction::Gt => lift_binop(BinOp::Gt, stack),
        Instruction::Gte => lift_binop(BinOp::Gte, stack),
        Instruction::Not => lift_unop(UnOp::Not, stack),
        Instruction::Neg => lift_unop(UnOp::Neg, stack),
        Instruction::Incr => lift_incr(stack),
        _ => return Ok(None),
    };
    Ok(Some(vec![stmt]))
}

/// Lift stack manipulation instructions.
fn lift_stack_inst(
    inst: &Instruction,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::Drop => {
            stack.pop();
            Ok(Some(Vec::new()))
        }
        Instruction::DropW => {
            for _ in 0..4 {
                stack.pop();
            }
            Ok(Some(Vec::new()))
        }
        Instruction::PadW => Ok(Some(lift_padw(stack))),
        Instruction::Dup0 => lift_dup(0, stack),
        Instruction::Dup1 => lift_dup(1, stack),
        Instruction::Dup2 => lift_dup(2, stack),
        Instruction::Dup3 => lift_dup(3, stack),
        Instruction::Dup4 => lift_dup(4, stack),
        Instruction::Dup5 => lift_dup(5, stack),
        Instruction::Dup6 => lift_dup(6, stack),
        Instruction::Dup7 => lift_dup(7, stack),
        Instruction::Dup8 => lift_dup(8, stack),
        Instruction::Dup9 => lift_dup(9, stack),
        Instruction::Dup10 => lift_dup(10, stack),
        Instruction::Dup11 => lift_dup(11, stack),
        Instruction::Dup12 => lift_dup(12, stack),
        Instruction::Dup13 => lift_dup(13, stack),
        Instruction::Dup14 => lift_dup(14, stack),
        Instruction::Dup15 => lift_dup(15, stack),
        Instruction::DupW0 => lift_dupw(0, stack),
        Instruction::DupW1 => lift_dupw(1, stack),
        Instruction::DupW2 => lift_dupw(2, stack),
        Instruction::DupW3 => lift_dupw(3, stack),
        Instruction::Swap1 => {
            stack.swap(1);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap2 => {
            stack.swap(2);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap3 => {
            stack.swap(3);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap4 => {
            stack.swap(4);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap5 => {
            stack.swap(5);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap6 => {
            stack.swap(6);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap7 => {
            stack.swap(7);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap8 => {
            stack.swap(8);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap9 => {
            stack.swap(9);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap10 => {
            stack.swap(10);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap11 => {
            stack.swap(11);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap12 => {
            stack.swap(12);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap13 => {
            stack.swap(13);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap14 => {
            stack.swap(14);
            Ok(Some(Vec::new()))
        }
        Instruction::Swap15 => {
            stack.swap(15);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp2 => {
            stack.movup(2);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp3 => {
            stack.movup(3);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp4 => {
            stack.movup(4);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp5 => {
            stack.movup(5);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp6 => {
            stack.movup(6);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp7 => {
            stack.movup(7);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp8 => {
            stack.movup(8);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp9 => {
            stack.movup(9);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp10 => {
            stack.movup(10);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp11 => {
            stack.movup(11);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp12 => {
            stack.movup(12);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp13 => {
            stack.movup(13);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp14 => {
            stack.movup(14);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp15 => {
            stack.movup(15);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn2 => {
            stack.movdn(2);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn3 => {
            stack.movdn(3);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn4 => {
            stack.movdn(4);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn5 => {
            stack.movdn(5);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn6 => {
            stack.movdn(6);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn7 => {
            stack.movdn(7);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn8 => {
            stack.movdn(8);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn9 => {
            stack.movdn(9);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn10 => {
            stack.movdn(10);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn11 => {
            stack.movdn(11);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn12 => {
            stack.movdn(12);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn13 => {
            stack.movdn(13);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn14 => {
            stack.movdn(14);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn15 => {
            stack.movdn(15);
            Ok(Some(Vec::new()))
        }
        Instruction::Nop | Instruction::Debug(_) => Ok(Some(Vec::new())),
        _ => Ok(None),
    }
}

/// Lift memory load/store instructions.
fn lift_mem_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::MemLoad => {
            let effect = effect_for_inst(inst, module_path, sigs)?;
            let (popped, pushed) =
                stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
            Ok(Some(vec![Stmt::MemLoad(MemLoad {
                address: popped,
                outputs: pushed,
            })]))
        }
        Instruction::MemLoadImm(imm) => {
            let effect = effect_for_inst(inst, module_path, sigs)?;
            let (_, pushed) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
            let (addr_var, assign) = assign_from_u32_immediate(imm, stack);
            Ok(Some(vec![
                assign,
                Stmt::MemLoad(MemLoad {
                    address: vec![addr_var],
                    outputs: pushed,
                }),
            ]))
        }
        Instruction::MemStore => {
            let effect = effect_for_inst(inst, module_path, sigs)?;
            let (mut popped, _) = stack.apply(effect.pops(), 0, effect.required_depth());
            if popped.is_empty() {
                return Err(LiftingError::UnsupportedInstruction(inst.clone()));
            }
            let address = popped.remove(0);
            Ok(Some(vec![Stmt::MemStore(MemStore {
                address: vec![address],
                values: popped,
            })]))
        }
        Instruction::MemStoreImm(imm) => {
            let effect = effect_for_inst(inst, module_path, sigs)?;
            let (popped, _) = stack.apply(effect.pops(), 0, effect.required_depth());
            let (addr_var, assign) = assign_from_u32_immediate(imm, stack);
            Ok(Some(vec![
                assign,
                Stmt::MemStore(MemStore {
                    address: vec![addr_var],
                    values: popped,
                }),
            ]))
        }
        _ => Ok(None),
    }
}

/// Lift local-variable load/store instructions.
fn lift_local_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::LocLoad(idx) => {
            let effect = effect_for_inst(inst, module_path, sigs)?;
            let (_, pushed) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
            Ok(Some(vec![Stmt::LocalLoad(LocalLoad {
                index: idx.expect_value(),
                outputs: pushed,
            })]))
        }
        Instruction::LocStore(idx) => {
            let effect = effect_for_inst(inst, module_path, sigs)?;
            let (popped, _) = stack.apply(effect.pops(), 0, effect.required_depth());
            Ok(Some(vec![Stmt::LocalStore(LocalStore {
                index: idx.expect_value(),
                values: popped,
            })]))
        }
        _ => Ok(None),
    }
}

/// Lift advice provider instructions.
fn lift_adv_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::AdvLoadW => {
            let effect = effect_for_inst(inst, module_path, sigs)?;
            let (_, pushed) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
            Ok(Some(vec![Stmt::AdvLoad(AdvLoad { outputs: pushed })]))
        }
        Instruction::AdvPush(imm) => {
            let count = match imm {
                Immediate::Value(span) => *span.inner() as usize,
                Immediate::Constant(_) => {
                    return Err(LiftingError::UnsupportedInstruction(inst.clone()));
                }
            };
            if count == 0 || count > 16 {
                return Err(LiftingError::UnsupportedInstruction(inst.clone()));
            }
            let (_, pushed) = stack.apply(0, count, 0);
            Ok(Some(vec![Stmt::Intrinsic(Intrinsic {
                name: format!("adv_push.{imm}"),
                args: Vec::new(),
                results: pushed,
            })]))
        }
        _ => Ok(None),
    }
}

/// Lift intrinsic-style instructions.
fn lift_intrinsic_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    let name = match inst {
        Instruction::Assert => "assert".to_string(),
        Instruction::AssertWithError(err) => format!("assert.{err}"),
        Instruction::AssertEq => "assert_eq".to_string(),
        Instruction::AssertEqWithError(err) => format!("assert_eq.{err}"),
        Instruction::Assertz => "assertz".to_string(),
        Instruction::AssertzWithError(err) => format!("assertz.{err}"),
        Instruction::Hash => "hash".to_string(),
        Instruction::HMerge => "hmerge".to_string(),
        Instruction::HPerm => "hperm".to_string(),
        Instruction::MTreeGet => "mtree_get".to_string(),
        Instruction::MTreeSet => "mtree_set".to_string(),
        Instruction::MTreeMerge => "mtree_merge".to_string(),
        Instruction::MTreeVerify => "mtree_verify".to_string(),
        Instruction::MTreeVerifyWithError(err) => format!("mtree_verify.{err}"),
        Instruction::Emit => "emit".to_string(),
        Instruction::EmitImm(imm) => format!("emit.{imm}"),
        Instruction::Trace(kind) => format!("trace_{kind}"),
        _ => return Ok(None),
    };
    let effect = effect_for_inst(inst, module_path, sigs)?;
    let (args, results) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
    Ok(Some(vec![Stmt::Intrinsic(Intrinsic {
        name,
        args,
        results,
    })]))
}

/// Lift push immediates into assignments.
fn lift_push_inst(
    inst: &Instruction,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::Push(imm) => {
            let depth = stack.len();
            let dest = Var::new(depth);
            stack.push(dest.clone());
            let expr: Expr = imm.into();
            Ok(Some(vec![Stmt::Assign { dest, expr }]))
        }
        _ => Ok(None),
    }
}

// Helper functions

fn effect_for_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<StackEffect> {
    match inst {
        Instruction::Exec(t) | Instruction::Call(t) | Instruction::SysCall(t) => {
            call_effect(t, module_path, sigs)
        }
        _ => {
            let effect = StackEffect::from(inst);
            match effect {
                StackEffect::Known { .. } => Ok(effect),
                StackEffect::Unknown => Err(LiftingError::UnsupportedInstruction(inst.clone())),
            }
        }
    }
}

fn lift_call_like<F>(
    target: &InvocationTarget,
    module_path: &str,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
    ctor: F,
) -> LiftingResult<Stmt>
where
    F: Fn(Call) -> Stmt,
{
    let effect = call_effect(target, module_path, sigs)?;
    let (args, results) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
    let name = call_name(target, module_path)
        .ok_or_else(|| LiftingError::UnknownCallTarget(format!("{target}")))?;
    Ok(ctor(Call {
        target: name,
        args,
        results,
    }))
}

fn lift_binop(op: BinOp, stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(2);
    let b = stack.pop();
    let a = stack.pop();
    let depth = stack.len();
    let dest = Var::new(depth);
    stack.push(dest.clone());
    Stmt::Assign {
        dest,
        expr: Expr::Binary(op, Box::new(Expr::Var(a)), Box::new(Expr::Var(b))),
    }
}

fn lift_binop_imm(op: BinOp, imm: &ImmFelt, stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(1);
    let a = stack.pop();
    let depth = stack.len();
    let dest = Var::new(depth);
    stack.push(dest.clone());
    let rhs: Expr = imm.into();
    Stmt::Assign {
        dest,
        expr: Expr::Binary(op, Box::new(Expr::Var(a)), Box::new(rhs)),
    }
}

fn lift_unop(op: UnOp, stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(1);
    let a = stack.pop();
    let depth = stack.len();
    let dest = Var::new(depth);
    stack.push(dest.clone());
    Stmt::Assign {
        dest,
        expr: Expr::Unary(op, Box::new(Expr::Var(a))),
    }
}

fn lift_incr(stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(1);
    let a = stack.pop();
    let depth = stack.len();
    let dest = Var::new(depth);
    stack.push(dest.clone());
    Stmt::Assign {
        dest,
        expr: Expr::Binary(
            BinOp::Add,
            Box::new(Expr::Var(a)),
            Box::new(Expr::Constant(Constant::Felt(1))),
        ),
    }
}

fn lift_padw(stack: &mut SymbolicStack) -> Vec<Stmt> {
    let mut stmts = Vec::with_capacity(4);
    for _ in 0..4 {
        let depth = stack.len();
        let dest = Var::new(depth);
        stack.push(dest.clone());
        stmts.push(Stmt::Assign {
            dest,
            expr: Expr::Constant(Constant::Felt(0)),
        });
    }
    stmts
}

fn lift_dup(idx: usize, stack: &mut SymbolicStack) -> LiftingResult<Option<Vec<Stmt>>> {
    let required_depth = idx + 1;
    stack.ensure_depth(required_depth);
    let src = stack.peek(idx).cloned().unwrap();
    let depth = stack.len();
    let dest = Var::new(depth);
    stack.push(dest.clone());
    Ok(Some(vec![Stmt::Assign {
        dest,
        expr: Expr::Var(src),
    }]))
}

fn lift_dupw(idx: usize, stack: &mut SymbolicStack) -> LiftingResult<Option<Vec<Stmt>>> {
    let required_depth = (idx + 1) * 4;
    stack.ensure_depth(required_depth);
    let offset = idx * 4;
    let mut stmts = Vec::with_capacity(4);
    // Peek the word (4 elements starting at offset from top).
    let mut word = Vec::with_capacity(4);
    for i in 0..4 {
        if let Some(v) = stack.peek(offset + 3 - i) {
            word.push(v.clone());
        }
    }
    for src in word {
        let depth = stack.len();
        let dest = Var::new(depth);
        stack.push(dest.clone());
        stmts.push(Stmt::Assign {
            dest,
            expr: Expr::Var(src),
        });
    }
    Ok(Some(stmts))
}

fn assign_from_u32_immediate(imm: &ImmU32, stack: &mut SymbolicStack) -> (Var, Stmt) {
    let depth = stack.len();
    let dest = Var::new(depth);
    // Note: we don't push this to the stack - it's just a temporary for the address.
    let expr: Expr = imm.into();
    (dest.clone(), Stmt::Assign { dest, expr })
}

fn call_effect(
    target: &InvocationTarget,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<StackEffect> {
    let callee = call_name(target, module_path)
        .ok_or_else(|| LiftingError::UnknownCallTarget(format!("{target}")))?;
    let signature = sigs
        .get(&callee)
        .ok_or_else(|| LiftingError::UnknownCallTarget(callee.clone()))?;
    let effect: StackEffect = signature.into();
    match effect {
        StackEffect::Known { .. } => Ok(effect),
        StackEffect::Unknown => Err(LiftingError::UnknownCallTarget(callee)),
    }
}

fn call_name(target: &InvocationTarget, module_path: &str) -> Option<String> {
    match target {
        InvocationTarget::Symbol(ident) => Some(format!("{module_path}::{}", ident.as_str())),
        InvocationTarget::Path(path) => Some(path.to_string()),
        InvocationTarget::MastRoot(_) => None,
    }
}

// Extension trait for StackEffect to get individual fields.
trait StackEffectExt {
    fn pops(&self) -> usize;
    fn pushes(&self) -> usize;
    fn required_depth(&self) -> usize;
}

impl StackEffectExt for StackEffect {
    fn pops(&self) -> usize {
        match self {
            StackEffect::Known { pops, .. } => *pops,
            StackEffect::Unknown => 0,
        }
    }

    fn pushes(&self) -> usize {
        match self {
            StackEffect::Known { pushes, .. } => *pushes,
            StackEffect::Unknown => 0,
        }
    }

    fn required_depth(&self) -> usize {
        match self {
            StackEffect::Known { required_depth, .. } => *required_depth,
            StackEffect::Unknown => 0,
        }
    }
}
