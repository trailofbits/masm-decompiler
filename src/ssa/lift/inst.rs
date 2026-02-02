//! Instruction-level lifting from MASM to SSA statements.

use miden_assembly_syntax::ast::{ImmFelt, ImmU32, Immediate, Instruction, InvocationTarget};

use crate::signature::{SignatureMap, StackEffect};

use super::context::{Frame, SsaContext, VarAlloc};
use super::{SsaError, SsaResult};
use crate::ssa::{
    AdvLoad, BinOp, Call, Constant, Expr, Intrinsic, LocalLoad, LocalStore, MemLoad, MemStore,
    Stmt, UnOp, Var,
};

/// Lift a single instruction into one or more SSA statements.
/// 
/// Individual handlers return Result<Option<Vec<Stmt>> where
/// 
/// 1. The result signals if the call succeeded or failed.
/// 2. The option signals if the instruction was handled.
pub(super) fn lift_inst_to_stmt(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Vec<Stmt>> {
    if let Some(stmts) = lift_call_inst(inst, module_path, sigs, state, ctx, alloc)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_arith_inst(inst, state, ctx, alloc)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_stack_inst(inst, state, ctx, alloc)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_mem_inst(inst, module_path, sigs, state, ctx, alloc)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_local_inst(inst, module_path, sigs, state, ctx, alloc)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_adv_inst(inst, module_path, sigs, state, ctx, alloc)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_event_inst(inst, module_path, sigs, state, ctx, alloc)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_intrinsic_inst(inst, module_path, sigs, state, ctx, alloc)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_push_inst(inst, state, ctx, alloc)? {
        return Ok(stmts);
    }
    Err(SsaError::UnsupportedInstruction(inst.clone()))
}

/// Lift call-like instructions (`exec`, `call`, `syscall`).
fn lift_call_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Option<Vec<Stmt>>> {
    let stmts = match inst {
        Instruction::Exec(t) => vec![lift_call_like(
            t,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
            Stmt::Exec,
        )?],
        Instruction::Call(t) => vec![lift_call_like(
            t,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
            Stmt::Call,
        )?],
        Instruction::SysCall(t) => vec![lift_call_like(
            t,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
            Stmt::SysCall,
        )?],
        Instruction::DynExec | Instruction::DynCall => {
            return Err(SsaError::UnsupportedInstruction(inst.clone()));
        }
        _ => return Ok(None),
    };
    Ok(Some(stmts))
}

/// Lift arithmetic and comparison instructions.
fn lift_arith_inst(
    inst: &Instruction,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Option<Vec<Stmt>>> {
    let stmt = match inst {
        Instruction::Add => lift_binop(BinOp::Add, state, ctx, alloc),
        Instruction::AddImm(imm) => lift_binop_imm(BinOp::Add, imm, state, ctx, alloc),
        Instruction::Sub => lift_binop(BinOp::Sub, state, ctx, alloc),
        Instruction::SubImm(imm) => lift_binop_imm(BinOp::Sub, imm, state, ctx, alloc),
        Instruction::Mul => lift_binop(BinOp::Mul, state, ctx, alloc),
        Instruction::MulImm(imm) => lift_binop_imm(BinOp::Mul, imm, state, ctx, alloc),
        Instruction::Div => lift_binop(BinOp::Div, state, ctx, alloc),
        Instruction::DivImm(imm) => lift_binop_imm(BinOp::Div, imm, state, ctx, alloc),
        Instruction::And => lift_binop(BinOp::And, state, ctx, alloc),
        Instruction::Or => lift_binop(BinOp::Or, state, ctx, alloc),
        Instruction::Xor => lift_binop(BinOp::Xor, state, ctx, alloc),
        Instruction::Eq => lift_binop(BinOp::Eq, state, ctx, alloc),
        Instruction::EqImm(imm) => lift_binop_imm(BinOp::Eq, imm, state, ctx, alloc),
        Instruction::Neq => lift_binop(BinOp::Neq, state, ctx, alloc),
        Instruction::NeqImm(imm) => lift_binop_imm(BinOp::Neq, imm, state, ctx, alloc),
        Instruction::Lt => lift_binop(BinOp::Lt, state, ctx, alloc),
        Instruction::Lte => lift_binop(BinOp::Lte, state, ctx, alloc),
        Instruction::Gt => lift_binop(BinOp::Gt, state, ctx, alloc),
        Instruction::Gte => lift_binop(BinOp::Gte, state, ctx, alloc),
        Instruction::Not => lift_unop(UnOp::Not, state, ctx, alloc),
        Instruction::Neg => lift_unop(UnOp::Neg, state, ctx, alloc),
        Instruction::Incr => lift_incr(state, ctx, alloc),
        _ => return Ok(None),
    };
    Ok(Some(vec![stmt]))
}

/// Lift stack manipulation instructions.
fn lift_stack_inst(
    inst: &Instruction,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::Drop => {
            let _ = state.pop_many(ctx, alloc, 1, 1);
            Ok(Some(Vec::new()))
        }
        Instruction::DropW => {
            let _ = state.pop_many(ctx, alloc, 4, 4);
            Ok(Some(Vec::new()))
        }
        Instruction::PadW => Ok(Some(lift_padw(state, ctx, alloc))),
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
            let idx = dup_index(inst)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?
                as usize;
            Ok(Some(lift_dup(inst, idx, state, ctx, alloc)?))
        }
        Instruction::DupW0 | Instruction::DupW1 | Instruction::DupW2 | Instruction::DupW3 => {
            let idx = dup_index(inst)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?
                as usize;
            Ok(Some(lift_dupw(inst, idx, state, ctx, alloc)?))
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
            let idx = swap_index(inst)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?
                as usize;
            lift_swap(idx, state, ctx, alloc);
            Ok(Some(Vec::new()))
        }
        Instruction::SwapW1 | Instruction::SwapW2 | Instruction::SwapW3 => {
            let idx = swap_index(inst)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?
                as usize;
            lift_swapw(idx, state, ctx, alloc);
            Ok(Some(Vec::new()))
        }
        Instruction::SwapDw => {
            lift_swapdw(state, ctx, alloc);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUp2
        | Instruction::MovUp3
        | Instruction::MovUp4
        | Instruction::MovUp5
        | Instruction::MovUp6
        | Instruction::MovUp7
        | Instruction::MovUp8
        | Instruction::MovUp9
        | Instruction::MovUp10
        | Instruction::MovUp11
        | Instruction::MovUp12
        | Instruction::MovUp13
        | Instruction::MovUp14
        | Instruction::MovUp15 => {
            let depth = mov_index(inst)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?
                as usize;
            lift_movup(depth, state, ctx, alloc);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDn2
        | Instruction::MovDn3
        | Instruction::MovDn4
        | Instruction::MovDn5
        | Instruction::MovDn6
        | Instruction::MovDn7
        | Instruction::MovDn8
        | Instruction::MovDn9
        | Instruction::MovDn10
        | Instruction::MovDn11
        | Instruction::MovDn12
        | Instruction::MovDn13
        | Instruction::MovDn14
        | Instruction::MovDn15 => {
            let depth = mov_index(inst)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?
                as usize;
            lift_movdn(depth, state, ctx, alloc);
            Ok(Some(Vec::new()))
        }
        Instruction::MovUpW2 | Instruction::MovUpW3 => {
            let depth = mov_index(inst)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?
                as usize;
            lift_movupw(depth, state, ctx, alloc);
            Ok(Some(Vec::new()))
        }
        Instruction::MovDnW2 | Instruction::MovDnW3 => {
            let depth = mov_index(inst)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?
                as usize;
            lift_movdnw(depth, state, ctx, alloc);
            Ok(Some(Vec::new()))
        }
        Instruction::Reversew => {
            lift_reversew(state, ctx, alloc);
            Ok(Some(Vec::new()))
        }
        Instruction::Reversedw => {
            lift_reversedw(state, ctx, alloc);
            Ok(Some(Vec::new()))
        }
        _ => Ok(None),
    }
}

/// Lift memory load/store instructions.
fn lift_mem_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::MemLoad => {
            let StackEffect::Known {
                pops,
                pushes,
                required_depth,
            } = lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            let address = state.pop_many(ctx, alloc, pops, required_depth);
            let outputs = state.push_many(ctx, alloc, pushes);
            Ok(Some(vec![Stmt::MemLoad(MemLoad { address, outputs })]))
        }
        Instruction::MemLoadImm(imm) => {
            let StackEffect::Known {
                pops,
                pushes,
                required_depth,
            } = lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            let _ = state.pop_many(ctx, alloc, pops, required_depth);
            let (address, assign) = assign_from_u32_immediate(imm, state, ctx, alloc);
            let outputs = state.push_many(ctx, alloc, pushes);
            Ok(Some(vec![
                assign,
                Stmt::MemLoad(MemLoad {
                    address: vec![address],
                    outputs,
                }),
            ]))
        }
        Instruction::MemLoadWBe | Instruction::MemLoadWLe => {
            let StackEffect::Known {
                pops,
                pushes,
                required_depth,
            } = lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            let popped = state.pop_many(ctx, alloc, pops, required_depth);
            let address = popped
                .first()
                .cloned()
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?;
            let outputs = state.push_many(ctx, alloc, pushes);
            Ok(Some(vec![Stmt::MemLoad(MemLoad {
                address: vec![address],
                outputs,
            })]))
        }
        Instruction::MemLoadWBeImm(imm) | Instruction::MemLoadWLeImm(imm) => {
            let StackEffect::Known {
                pops,
                pushes,
                required_depth,
            } = lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            let _ = state.pop_many(ctx, alloc, pops, required_depth);
            let (address, assign) = assign_from_u32_immediate(imm, state, ctx, alloc);
            let outputs = state.push_many(ctx, alloc, pushes);
            Ok(Some(vec![
                assign,
                Stmt::MemLoad(MemLoad {
                    address: vec![address],
                    outputs,
                }),
            ]))
        }
        Instruction::MemStore => {
            let StackEffect::Known {
                pops,
                required_depth,
                ..
            } = lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            let mut args = state.pop_many(ctx, alloc, pops, required_depth);
            if args.is_empty() {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            }
            let address = args.remove(0);
            Ok(Some(vec![Stmt::MemStore(MemStore {
                address: vec![address],
                values: args,
            })]))
        }
        Instruction::MemStoreImm(imm) => {
            let StackEffect::Known {
                pops,
                required_depth,
                ..
            } = lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            let values = state.pop_many(ctx, alloc, pops, required_depth);
            let (address, assign) = assign_from_u32_immediate(imm, state, ctx, alloc);
            Ok(Some(vec![
                assign,
                Stmt::MemStore(MemStore {
                    address: vec![address],
                    values,
                }),
            ]))
        }
        Instruction::MemStoreWBe | Instruction::MemStoreWLe => {
            let StackEffect::Known { required_depth, .. } =
                lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            let address = state.pop_one(ctx, alloc, required_depth);
            let values = state
                .stack
                .peek_range_from_top(0, 4)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?;
            Ok(Some(vec![Stmt::MemStore(MemStore {
                address: vec![address],
                values,
            })]))
        }
        Instruction::MemStoreWBeImm(imm) | Instruction::MemStoreWLeImm(imm) => {
            let StackEffect::Known { required_depth, .. } =
                lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            state.ensure_depth(ctx, alloc, required_depth);
            let values = state
                .stack
                .peek_range_from_top(0, 4)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?;
            let (address, assign) = assign_from_u32_immediate(imm, state, ctx, alloc);
            Ok(Some(vec![
                assign,
                Stmt::MemStore(MemStore {
                    address: vec![address],
                    values,
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
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::LocLoad(idx) | Instruction::LocLoadWBe(idx) | Instruction::LocLoadWLe(idx) => {
            let StackEffect::Known {
                pops,
                pushes,
                required_depth,
            } = lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            let _ = state.pop_many(ctx, alloc, pops, required_depth);
            let outputs = state.push_many(ctx, alloc, pushes);
            Ok(Some(vec![Stmt::LocalLoad(LocalLoad {
                index: idx.expect_value(),
                outputs,
            })]))
        }
        Instruction::LocStore(idx) => {
            let StackEffect::Known {
                pops,
                required_depth,
                ..
            } = lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            let values = state.pop_many(ctx, alloc, pops, required_depth);
            Ok(Some(vec![Stmt::LocalStore(LocalStore {
                index: idx.expect_value(),
                values,
            })]))
        }
        Instruction::LocStoreWBe(idx) | Instruction::LocStoreWLe(idx) => {
            let StackEffect::Known { required_depth, .. } =
                lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            state.ensure_depth(ctx, alloc, required_depth);
            let values = state
                .stack
                .peek_range_from_top(0, 4)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?;
            Ok(Some(vec![Stmt::LocalStore(LocalStore {
                index: idx.expect_value(),
                values,
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
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::AdvLoadW => {
            let StackEffect::Known {
                pops,
                pushes,
                required_depth,
            } = lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            let _ = state.pop_many(ctx, alloc, pops, required_depth);
            let outputs = state.push_many(ctx, alloc, pushes);
            Ok(Some(vec![Stmt::AdvLoad(AdvLoad { outputs })]))
        }
        Instruction::AdvPush(imm) => {
            let count = match imm {
                Immediate::Value(span) => *span.inner() as usize,
                Immediate::Constant(_) => {
                    return Err(SsaError::UnsupportedInstruction(inst.clone()));
                }
            };
            if count == 0 || count > 16 {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            }
            let outputs = state.push_many(ctx, alloc, count);
            Ok(Some(vec![Stmt::Intrinsic(Intrinsic {
                name: format!("adv_push.{imm}"),
                args: Vec::new(),
                results: outputs,
            })]))
        }
        Instruction::AdvPipe => {
            let StackEffect::Known { required_depth, .. } =
                lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            if required_depth != 13 {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            }
            state.ensure_depth(ctx, alloc, required_depth);
            let addr_in = state
                .stack
                .peek_range_from_top(0, required_depth)
                .and_then(|seg| seg.first().cloned())
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?;
            let addr_out = alloc.alloc(ctx);
            let mut word_d = Vec::with_capacity(4);
            let mut word_e = Vec::with_capacity(4);
            for _ in 0..4 {
                word_d.push(alloc.alloc(ctx));
            }
            for _ in 0..4 {
                word_e.push(alloc.alloc(ctx));
            }
            let mut results = Vec::with_capacity(1 + word_d.len() + word_e.len());
            results.push(addr_out.clone());
            results.extend(word_d.iter().cloned());
            results.extend(word_e.iter().cloned());
            // Create explicit assignment for addr_out = addr_in + 2
            let addr_expr = Expr::Binary(
                BinOp::Add,
                Box::new(Expr::Var(addr_in.clone())),
                Box::new(Expr::Constant(Constant::Felt(2))),
            );
            let addr_assign = Stmt::Assign {
                dest: addr_out.clone(),
                expr: addr_expr,
            };
            let _ = state.stack.permute_top(
                required_depth,
                || alloc.alloc(ctx),
                |seg| {
                    seg[0] = addr_out.clone();
                    for i in 0..4 {
                        seg[5 + i] = word_d[i].clone();
                    }
                    for i in 0..4 {
                        seg[9 + i] = word_e[i].clone();
                    }
                },
            );
            Ok(Some(vec![
                Stmt::Intrinsic(Intrinsic {
                    name: "adv_pipe".to_string(),
                    args: vec![addr_in],
                    results,
                }),
                addr_assign,
            ]))
        }
        _ => Ok(None),
    }
}

/// Lift event, emit, trace, and system event instructions.
fn lift_event_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::Emit => {
            let StackEffect::Known { required_depth, .. } =
                lift_effect_for_inst(inst, module_path, sigs)?
            else {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            };
            if required_depth == 0 {
                return Err(SsaError::UnsupportedInstruction(inst.clone()));
            }
            state.ensure_depth(ctx, alloc, required_depth);
            let arg = state
                .stack
                .peek_from_top(0)
                .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?;
            Ok(Some(vec![Stmt::Intrinsic(Intrinsic {
                name: "emit".to_string(),
                args: vec![arg],
                results: Vec::new(),
            })]))
        }
        Instruction::EmitImm(imm) => Ok(Some(vec![lift_intrinsic(
            format!("emit.{imm}"),
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        )?])),
        Instruction::Trace(kind) => Ok(Some(vec![lift_intrinsic(
            format!("trace_{kind}"),
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        )?])),
        Instruction::SysEvent(event) => Ok(Some(vec![lift_intrinsic(
            format!("sys_event_{event:?}"),
            inst,
            module_path,
            sigs,
            state,
            ctx,
            alloc,
        )?])),
        _ => Ok(None),
    }
}

/// Lift intrinsic-style instructions that map to named operations.
fn lift_intrinsic_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Option<Vec<Stmt>>> {
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
        Instruction::CryptoStream => "crypto_stream".to_string(),
        Instruction::FriExt2Fold4 => "fri_ext2fold4".to_string(),
        Instruction::HornerBase => "horner_eval_base".to_string(),
        Instruction::HornerExt => "horner_eval_ext".to_string(),
        Instruction::LogPrecompile => "log_precompile".to_string(),
        Instruction::EvalCircuit => "eval_circuit".to_string(),
        Instruction::EmitImm(_)
        | Instruction::Emit
        | Instruction::Trace(_)
        | Instruction::SysEvent(_) => return Ok(None),
        _ => return Ok(None),
    };
    Ok(Some(vec![lift_intrinsic(
        name,
        inst,
        module_path,
        sigs,
        state,
        ctx,
        alloc,
    )?]))
}

/// Lift push immediates into SSA assignments.
fn lift_push_inst(
    inst: &Instruction,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::Push(imm) => {
            let dst = state.push_many(ctx, alloc, 1).pop().unwrap();
            let expr: Expr = imm.into();
            Ok(Some(vec![Stmt::Assign { dest: dst, expr }]))
        }
        _ => Ok(None),
    }
}

/// Resolve stack effects for a specific instruction.
fn lift_effect_for_inst(
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
) -> SsaResult<StackEffect> {
    match inst {
        Instruction::Exec(t) | Instruction::Call(t) | Instruction::SysCall(t) => {
            call_effect(t, module_path, sigs)
        }
        _ => {
            let effect = StackEffect::from(inst);
            match effect {
                StackEffect::Known { .. } => Ok(effect),
                StackEffect::Unknown => Err(SsaError::UnsupportedInstruction(inst.clone())),
            }
        }
    }
}

/// Lift a call-like instruction using its signature-derived stack effect.
fn lift_call_like<F>(
    target: &InvocationTarget,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
    ctor: F,
) -> SsaResult<Stmt>
where
    F: Fn(Call) -> Stmt,
{
    let StackEffect::Known {
        pops,
        pushes,
        required_depth,
    } = call_effect(target, module_path, sigs)?
    else {
        return Err(SsaError::UnknownStackEffect(target.clone()));
    };
    let popped = state.pop_many(ctx, alloc, pops, required_depth);
    let pushed = state.push_many(ctx, alloc, pushes);
    let name = call_name(target, module_path)
        .ok_or_else(|| SsaError::UnknownStackEffect(target.clone()))?;
    Ok(ctor(Call {
        target: name,
        args: popped,
        results: pushed,
    }))
}

/// Lift a generic intrinsic by applying its stack effect.
fn lift_intrinsic(
    name: impl Into<String>,
    inst: &Instruction,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Stmt> {
    let StackEffect::Known {
        pops,
        pushes,
        required_depth,
    } = lift_effect_for_inst(inst, module_path, sigs)?
    else {
        return Err(SsaError::UnsupportedInstruction(inst.clone()));
    };
    let args = state.pop_many(ctx, alloc, pops, required_depth);
    let results = state.push_many(ctx, alloc, pushes);
    Ok(Stmt::Intrinsic(Intrinsic {
        name: name.into(),
        args,
        results,
    }))
}

/// Lift a binary operation using two stack arguments.
fn lift_binop(
    op: BinOp,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> Stmt {
    let popped = state.pop_many(ctx, alloc, 2, 2);
    let b = popped[0].clone();
    let a = popped[1].clone();
    let res = state.push_many(ctx, alloc, 1).pop().unwrap();
    let expr = Expr::Binary(op, Box::new(Expr::Var(a)), Box::new(Expr::Var(b)));
    Stmt::Assign { dest: res, expr }
}

/// Lift a unary operation using the top stack argument.
fn lift_unop(op: UnOp, state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) -> Stmt {
    let a = state.pop_one(ctx, alloc, 1);
    let res = state.push_many(ctx, alloc, 1).pop().unwrap();
    let expr = Expr::Unary(op, Box::new(Expr::Var(a)));
    Stmt::Assign { dest: res, expr }
}

fn lift_incr(state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) -> Stmt {
    let a = state.pop_one(ctx, alloc, 1);
    let res = state.push_many(ctx, alloc, 1).pop().unwrap();
    let expr = Expr::Binary(
        BinOp::Add,
        Box::new(Expr::Var(a)),
        Box::new(Expr::Constant(Constant::Felt(1))),
    );
    Stmt::Assign { dest: res, expr }
}

/// Lift a binary operation with an immediate RHS.
fn lift_binop_imm(
    op: BinOp,
    imm: &ImmFelt,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> Stmt {
    let a = state.pop_one(ctx, alloc, 1);
    let res = state.push_many(ctx, alloc, 1).pop().unwrap();
    let rhs: Expr = imm.into();
    let expr = Expr::Binary(op, Box::new(Expr::Var(a)), Box::new(rhs));
    Stmt::Assign { dest: res, expr }
}

/// Push four zero constants onto the stack.
fn lift_padw(state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) -> Vec<Stmt> {
    let pushed = state.push_many(ctx, alloc, 4);
    let mut stmts = Vec::with_capacity(pushed.len());
    for dst in pushed {
        let expr = Expr::Constant(Constant::Felt(0));
        stmts.push(Stmt::Assign { dest: dst, expr });
    }
    stmts
}

/// Duplicate a stack value at the given depth.
fn lift_dup(
    inst: &Instruction,
    idx: usize,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Vec<Stmt>> {
    let required_depth = idx + 1;
    state.ensure_depth(ctx, alloc, required_depth);
    let src = state
        .stack
        .peek_from_top(idx)
        .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?;
    let dst = state.push_many(ctx, alloc, 1).pop().unwrap();
    let expr = Expr::Var(src);
    Ok(vec![Stmt::Assign { dest: dst, expr }])
}

/// Duplicate a word from the stack at the given word depth.
fn lift_dupw(
    inst: &Instruction,
    idx: usize,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<Vec<Stmt>> {
    let required_depth = (idx + 1) * 4;
    state.ensure_depth(ctx, alloc, required_depth);
    let offset = idx * 4;
    let word = state
        .stack
        .peek_range_from_top(offset, 4)
        .ok_or_else(|| SsaError::UnsupportedInstruction(inst.clone()))?;
    let mut stmts = Vec::with_capacity(4);
    for src in word {
        let dst = state.push_many(ctx, alloc, 1).pop().unwrap();
        let expr = Expr::Var(src);
        stmts.push(Stmt::Assign { dest: dst, expr });
    }
    Ok(stmts)
}

/// Swap the stack top with a value at the given depth.
fn lift_swap(idx: usize, state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) {
    let count = idx + 1;
    let _ = state.stack.permute_top(
        count,
        || alloc.alloc(ctx),
        |seg| {
            let top_idx = seg.len() - 1;
            let tgt_idx = seg.len() - 1 - idx;
            seg.swap(top_idx, tgt_idx);
        },
    );
}

/// Swap the stack top word with a word at the given depth.
fn lift_swapw(idx: usize, state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) {
    let count = (idx + 1) * 4;
    let _ = state.stack.permute_top(
        count,
        || alloc.alloc(ctx),
        |seg| {
            let len = seg.len();
            let top_start = len - 4;
            for i in 0..4 {
                seg.swap(i, top_start + i);
            }
        },
    );
}

/// Swap the top double-word segments in place.
fn lift_swapdw(state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) {
    let _ = state.stack.permute_top(
        16,
        || alloc.alloc(ctx),
        |seg| {
            for i in 0..4 {
                seg.swap(i, 8 + i);
                seg.swap(4 + i, 12 + i);
            }
        },
    );
}

/// Move a value up from the given depth to the top.
fn lift_movup(depth: usize, state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) {
    let count = depth + 1;
    let _ = state.stack.permute_top(
        count,
        || alloc.alloc(ctx),
        |seg| {
            let idx = seg.len() - 1 - depth;
            let v = seg.remove(idx);
            seg.push(v);
        },
    );
}

/// Move the top value down to the given depth.
fn lift_movdn(depth: usize, state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) {
    let count = depth + 1;
    let _ = state.stack.permute_top(
        count,
        || alloc.alloc(ctx),
        |seg| {
            if let Some(top) = seg.pop() {
                seg.insert(0, top);
            }
        },
    );
}

/// Move a word up from the given word depth to the top.
fn lift_movupw(depth: usize, state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) {
    let count = (depth + 1) * 4;
    let _ = state.stack.permute_top(
        count,
        || alloc.alloc(ctx),
        |seg| {
            let word: Vec<Var> = seg.drain(0..4).collect();
            seg.extend(word);
        },
    );
}

/// Move the top word down to the given word depth.
fn lift_movdnw(depth: usize, state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) {
    let count = (depth + 1) * 4;
    let _ = state.stack.permute_top(
        count,
        || alloc.alloc(ctx),
        |seg| {
            let len = seg.len();
            let word: Vec<Var> = seg.drain(len - 4..).collect();
            seg.splice(0..0, word);
        },
    );
}

/// Reverse the top word in place.
fn lift_reversew(state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) {
    let _ = state.stack.permute_top(4, || alloc.alloc(ctx), |seg| seg.reverse());
}

/// Reverse the top double-word in place.
fn lift_reversedw(state: &mut Frame, ctx: &mut SsaContext, alloc: &mut impl VarAlloc) {
    let _ = state.stack.permute_top(8, || alloc.alloc(ctx), |seg| seg.reverse());
}

/// Extract the duplicate depth for dup instructions.
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
        Instruction::DupW0 => Some(0),
        Instruction::DupW1 => Some(1),
        Instruction::DupW2 => Some(2),
        Instruction::DupW3 => Some(3),
        _ => None,
    }
}

/// Extract the swap depth for swap instructions.
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
        Instruction::SwapW1 => Some(1),
        Instruction::SwapW2 => Some(2),
        Instruction::SwapW3 => Some(3),
        _ => None,
    }
}

/// Extract the move depth for mov instructions.
fn mov_index(inst: &Instruction) -> Option<u8> {
    match inst {
        Instruction::MovUp2 | Instruction::MovDn2 | Instruction::MovUpW2 | Instruction::MovDnW2 => {
            Some(2)
        }
        Instruction::MovUp3 | Instruction::MovDn3 | Instruction::MovUpW3 | Instruction::MovDnW3 => {
            Some(3)
        }
        Instruction::MovUp4 | Instruction::MovDn4 => Some(4),
        Instruction::MovUp5 | Instruction::MovDn5 => Some(5),
        Instruction::MovUp6 | Instruction::MovDn6 => Some(6),
        Instruction::MovUp7 | Instruction::MovDn7 => Some(7),
        Instruction::MovUp8 | Instruction::MovDn8 => Some(8),
        Instruction::MovUp9 | Instruction::MovDn9 => Some(9),
        Instruction::MovUp10 | Instruction::MovDn10 => Some(10),
        Instruction::MovUp11 | Instruction::MovDn11 => Some(11),
        Instruction::MovUp12 | Instruction::MovDn12 => Some(12),
        Instruction::MovUp13 | Instruction::MovDn13 => Some(13),
        Instruction::MovUp14 | Instruction::MovDn14 => Some(14),
        Instruction::MovUp15 | Instruction::MovDn15 => Some(15),
        _ => None,
    }
}

/// Assign an SSA variable from a u32 immediate.
fn assign_from_u32_immediate(
    imm: &ImmU32,
    _state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> (Var, Stmt) {
    let dest = alloc.alloc(ctx);
    let expr: Expr = imm.into();
    (dest.clone(), Stmt::Assign { dest, expr })
}

/// Resolve a call target to a known stack effect.
fn call_effect(
    target: &InvocationTarget,
    module_path: &str,
    sigs: &SignatureMap,
) -> SsaResult<StackEffect> {
    let callee = call_name(target, module_path)
        .ok_or_else(|| SsaError::UnknownStackEffect(target.clone()))?;
    let Some(signature) = sigs.get(&callee) else {
        return Err(SsaError::UnknownStackEffect(target.clone()));
    };
    let effect: StackEffect = signature.into();
    match effect {
        StackEffect::Known { .. } => Ok(effect),
        StackEffect::Unknown => Err(SsaError::UnknownStackEffect(target.clone())),
    }
}

/// Resolve a call target into a fully-qualified name.
fn call_name(target: &InvocationTarget, module_path: &str) -> Option<String> {
    let name = match target {
        InvocationTarget::Symbol(ident) => format!("{module_path}::{}", ident.as_str()),
        InvocationTarget::Path(path) => path.to_string(),
        InvocationTarget::MastRoot(_) => return None,
    };
    Some(name)
}
