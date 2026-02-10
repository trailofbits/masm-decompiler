//! Instruction-level lifting from MASM to IR statements.

use miden_assembly_syntax::ast::{ImmFelt, ImmU32, Immediate, Instruction, InvocationTarget};
use miden_assembly_syntax::debuginfo::SourceSpan;

use crate::ir::{
    AdvLoad, BinOp, Call, Constant, Expr, Intrinsic, LocalLoad, LocalStore, LocalStoreW, MemLoad,
    MemStore, Stmt, UnOp, Var,
};
use crate::signature::{SignatureMap, StackEffect};
use crate::symbol::path::SymbolPath;
use crate::symbol::resolution::SymbolResolver;

use super::stack::SymbolicStack;
use super::{LiftingError, LiftingResult, LoopContext};

/// Lift a single instruction into one or more IR statements.
pub(super) fn lift_inst(
    inst: &Instruction,
    span: SourceSpan,
    stack: &mut SymbolicStack,
    _loop_ctx: &mut LoopContext,
    resolver: &SymbolResolver<'_>,
    sigs: &SignatureMap,
) -> LiftingResult<Vec<Stmt>> {
    // Try each instruction category in turn.
    if let Some(stmts) = lift_call_inst(inst, span, resolver, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_u32_inst(inst, span, resolver, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_arith_inst(inst, span, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_stack_inst(inst, span, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_mem_inst(inst, span, resolver, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_local_inst(inst, span, resolver, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_adv_inst(inst, span, resolver, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_intrinsic_inst(inst, span, resolver, sigs, stack)? {
        return Ok(stmts);
    }
    if let Some(stmts) = lift_push_inst(inst, span, stack)? {
        return Ok(stmts);
    }
    Err(LiftingError::UnsupportedInstruction {
        span,
        instruction: inst.clone(),
    })
}

/// Lift call-like instructions (`exec`, `call`, `syscall`).
fn lift_call_inst(
    inst: &Instruction,
    span: SourceSpan,
    resolver: &SymbolResolver<'_>,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    let stmts = match inst {
        Instruction::Exec(t) => {
            vec![lift_call_like(t, span, resolver, sigs, stack, |call| {
                Stmt::Exec { span, call }
            })?]
        }
        Instruction::Call(t) => {
            vec![lift_call_like(t, span, resolver, sigs, stack, |call| {
                Stmt::Call { span, call }
            })?]
        }
        Instruction::SysCall(t) => {
            vec![lift_call_like(t, span, resolver, sigs, stack, |call| {
                Stmt::SysCall { span, call }
            })?]
        }
        Instruction::DynExec | Instruction::DynCall => {
            return Err(LiftingError::UnsupportedInstruction {
                span,
                instruction: inst.clone(),
            });
        }
        _ => return Ok(None),
    };
    Ok(Some(stmts))
}

/// Lift arithmetic and comparison instructions.
fn lift_arith_inst(
    inst: &Instruction,
    span: SourceSpan,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    let stmt = match inst {
        Instruction::Add => lift_binop(span, BinOp::Add, stack),
        Instruction::AddImm(imm) => lift_binop_imm(span, BinOp::Add, imm, stack),
        Instruction::Sub => lift_binop(span, BinOp::Sub, stack),
        Instruction::SubImm(imm) => lift_binop_imm(span, BinOp::Sub, imm, stack),
        Instruction::Mul => lift_binop(span, BinOp::Mul, stack),
        Instruction::MulImm(imm) => lift_binop_imm(span, BinOp::Mul, imm, stack),
        Instruction::Div => lift_binop(span, BinOp::Div, stack),
        Instruction::DivImm(imm) => lift_binop_imm(span, BinOp::Div, imm, stack),
        Instruction::And => lift_binop(span, BinOp::And, stack),
        Instruction::Or => lift_binop(span, BinOp::Or, stack),
        Instruction::Xor => lift_binop(span, BinOp::Xor, stack),
        Instruction::Eq => lift_binop(span, BinOp::Eq, stack),
        Instruction::EqImm(imm) => lift_binop_imm(span, BinOp::Eq, imm, stack),
        Instruction::Neq => lift_binop(span, BinOp::Neq, stack),
        Instruction::NeqImm(imm) => lift_binop_imm(span, BinOp::Neq, imm, stack),
        Instruction::Lt => lift_binop(span, BinOp::Lt, stack),
        Instruction::Lte => lift_binop(span, BinOp::Lte, stack),
        Instruction::Gt => lift_binop(span, BinOp::Gt, stack),
        Instruction::Gte => lift_binop(span, BinOp::Gte, stack),
        Instruction::Not => lift_unop(span, UnOp::Not, stack),
        Instruction::Neg => lift_unop(span, UnOp::Neg, stack),
        Instruction::Pow2 => lift_unop(span, UnOp::Pow2, stack),
        Instruction::Incr => lift_incr(span, stack),
        _ => return Ok(None),
    };
    Ok(Some(vec![stmt]))
}

/// Lift u32 instructions.
fn lift_u32_inst(
    inst: &Instruction,
    span: SourceSpan,
    resolver: &SymbolResolver<'_>,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    let stmt = match inst {
        Instruction::U32And => lift_binop(span, BinOp::U32And, stack),
        Instruction::U32Or => lift_binop(span, BinOp::U32Or, stack),
        Instruction::U32Xor => lift_binop(span, BinOp::U32Xor, stack),
        Instruction::U32Lt => lift_binop(span, BinOp::U32Lt, stack),
        Instruction::U32Lte => lift_binop(span, BinOp::U32Lte, stack),
        Instruction::U32Gt => lift_binop(span, BinOp::U32Gt, stack),
        Instruction::U32Gte => lift_binop(span, BinOp::U32Gte, stack),
        Instruction::U32WrappingAdd => lift_binop(span, BinOp::U32WrappingAdd, stack),
        Instruction::U32WrappingSub => lift_binop(span, BinOp::U32WrappingSub, stack),
        Instruction::U32WrappingMul => lift_binop(span, BinOp::U32WrappingMul, stack),
        Instruction::U32WrappingAddImm(imm) => {
            lift_binop_u32_imm(span, BinOp::U32WrappingAdd, imm, stack)
        }
        Instruction::U32WrappingSubImm(imm) => {
            lift_binop_u32_imm(span, BinOp::U32WrappingSub, imm, stack)
        }
        Instruction::U32WrappingMulImm(imm) => {
            lift_binop_u32_imm(span, BinOp::U32WrappingMul, imm, stack)
        }
        Instruction::U32Clz => lift_unop(span, UnOp::U32Clz, stack),
        Instruction::U32Ctz => lift_unop(span, UnOp::U32Ctz, stack),
        Instruction::U32Clo => lift_unop(span, UnOp::U32Clo, stack),
        Instruction::U32Cto => lift_unop(span, UnOp::U32Cto, stack),
        Instruction::U32OverflowingAdd => {
            return lift_u32_intrinsic(inst, span, "u32overflowing_add", resolver, sigs, stack);
        }
        Instruction::U32OverflowingAdd3 => {
            return lift_u32_intrinsic(inst, span, "u32overflowing_add3", resolver, sigs, stack);
        }
        Instruction::U32OverflowingSub => {
            return lift_u32_intrinsic(inst, span, "u32overflowing_sub", resolver, sigs, stack);
        }
        Instruction::U32OverflowingMul => {
            return lift_u32_intrinsic(inst, span, "u32overflowing_mul", resolver, sigs, stack);
        }
        Instruction::U32OverflowingMadd => {
            return lift_u32_intrinsic(inst, span, "u32overflowing_madd", resolver, sigs, stack);
        }
        Instruction::U32Split => {
            return Ok(Some(vec![lift_u32split(span, stack)]));
        }
        Instruction::U32Assert2 => {
            return Ok(Some(vec![lift_u32_assert2(span, "u32assert2", stack)]));
        }
        Instruction::U32Assert2WithError(err) => {
            return Ok(Some(vec![lift_u32_assert2(
                span,
                &format!("u32assert2.{err}"),
                stack,
            )]));
        }
        _ => return Ok(None),
    };
    Ok(Some(vec![stmt]))
}

/// Lift stack manipulation instructions.
fn lift_stack_inst(
    inst: &Instruction,
    span: SourceSpan,
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
        Instruction::PadW => Ok(Some(lift_padw(span, stack))),
        Instruction::CDrop => Ok(Some(vec![lift_cdrop(span, stack)])),
        Instruction::CSwap => Ok(Some(lift_cswap(span, stack))),
        Instruction::Dup0 => lift_dup(span, 0, stack),
        Instruction::Dup1 => lift_dup(span, 1, stack),
        Instruction::Dup2 => lift_dup(span, 2, stack),
        Instruction::Dup3 => lift_dup(span, 3, stack),
        Instruction::Dup4 => lift_dup(span, 4, stack),
        Instruction::Dup5 => lift_dup(span, 5, stack),
        Instruction::Dup6 => lift_dup(span, 6, stack),
        Instruction::Dup7 => lift_dup(span, 7, stack),
        Instruction::Dup8 => lift_dup(span, 8, stack),
        Instruction::Dup9 => lift_dup(span, 9, stack),
        Instruction::Dup10 => lift_dup(span, 10, stack),
        Instruction::Dup11 => lift_dup(span, 11, stack),
        Instruction::Dup12 => lift_dup(span, 12, stack),
        Instruction::Dup13 => lift_dup(span, 13, stack),
        Instruction::Dup14 => lift_dup(span, 14, stack),
        Instruction::Dup15 => lift_dup(span, 15, stack),
        Instruction::DupW0 => lift_dupw(span, 0, stack),
        Instruction::DupW1 => lift_dupw(span, 1, stack),
        Instruction::DupW2 => lift_dupw(span, 2, stack),
        Instruction::DupW3 => lift_dupw(span, 3, stack),
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
        Instruction::SwapW1 => {
            stack.swapw(1);
            Ok(Some(Vec::new()))
        }
        Instruction::SwapW2 => {
            stack.swapw(2);
            Ok(Some(Vec::new()))
        }
        Instruction::SwapW3 => {
            stack.swapw(3);
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
        Instruction::Reversew => {
            stack.reversew();
            Ok(Some(Vec::new()))
        }
        Instruction::Nop | Instruction::Debug(_) => Ok(Some(Vec::new())),
        _ => Ok(None),
    }
}

fn lift_u32_intrinsic(
    inst: &Instruction,
    span: SourceSpan,
    name: &str,
    resolver: &SymbolResolver<'_>,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    let effect = effect_for_inst(inst, span, resolver, sigs)?;
    let (args, results) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
    Ok(Some(vec![Stmt::Intrinsic {
        span,
        intrinsic: Intrinsic {
            name: name.to_string(),
            args,
            results,
        },
    }]))
}

fn lift_u32_assert2(span: SourceSpan, name: &str, stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(2);
    let b = stack.peek(0).cloned().expect("u32assert2 stack");
    let a = stack.peek(1).cloned().expect("u32assert2 stack");
    Stmt::Intrinsic {
        span,
        intrinsic: Intrinsic {
            name: name.to_string(),
            args: vec![b, a],
            results: Vec::new(),
        },
    }
}

/// Lift memory load/store instructions.
fn lift_mem_inst(
    inst: &Instruction,
    span: SourceSpan,
    resolver: &SymbolResolver<'_>,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::MemLoad => {
            let effect = effect_for_inst(inst, span, resolver, sigs)?;
            let (popped, pushed) =
                stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
            Ok(Some(vec![Stmt::MemLoad {
                span,
                load: MemLoad {
                    address: popped,
                    outputs: pushed,
                },
            }]))
        }
        Instruction::MemLoadImm(imm) => {
            let effect = effect_for_inst(inst, span, resolver, sigs)?;
            let (_, pushed) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
            let (addr_var, assign) = assign_from_u32_immediate(span, imm, stack);
            Ok(Some(vec![
                assign,
                Stmt::MemLoad {
                    span,
                    load: MemLoad {
                        address: vec![addr_var],
                        outputs: pushed,
                    },
                },
            ]))
        }
        Instruction::MemStore => {
            let effect = effect_for_inst(inst, span, resolver, sigs)?;
            let (mut popped, _) = stack.apply(effect.pops(), 0, effect.required_depth());
            if popped.is_empty() {
                return Err(LiftingError::UnsupportedInstruction {
                    span,
                    instruction: inst.clone(),
                });
            }
            let address = popped.remove(0);
            Ok(Some(vec![Stmt::MemStore {
                span,
                store: MemStore {
                    address: vec![address],
                    values: popped,
                },
            }]))
        }
        Instruction::MemStoreImm(imm) => {
            let effect = effect_for_inst(inst, span, resolver, sigs)?;
            let (popped, _) = stack.apply(effect.pops(), 0, effect.required_depth());
            let (addr_var, assign) = assign_from_u32_immediate(span, imm, stack);
            Ok(Some(vec![
                assign,
                Stmt::MemStore {
                    span,
                    store: MemStore {
                        address: vec![addr_var],
                        values: popped,
                    },
                },
            ]))
        }
        _ => Ok(None),
    }
}

/// Lift local-variable load/store instructions.
fn lift_local_inst(
    inst: &Instruction,
    span: SourceSpan,
    resolver: &SymbolResolver<'_>,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::LocLoad(idx) => {
            let effect = effect_for_inst(inst, span, resolver, sigs)?;
            let (_, pushed) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
            Ok(Some(vec![Stmt::LocalLoad {
                span,
                load: LocalLoad {
                    index: idx.expect_value(),
                    outputs: pushed,
                },
            }]))
        }
        Instruction::LocStore(idx) => {
            let effect = effect_for_inst(inst, span, resolver, sigs)?;
            let (popped, _) = stack.apply(effect.pops(), 0, effect.required_depth());
            Ok(Some(vec![Stmt::LocalStore {
                span,
                store: LocalStore {
                    index: idx.expect_value(),
                    values: popped,
                },
            }]))
        }
        Instruction::LocStoreWBe(idx) => {
            stack.ensure_depth(4);
            let values = stack.top_n(4);
            Ok(Some(vec![Stmt::LocalStoreW {
                span,
                store: LocalStoreW {
                    index: idx.expect_value(),
                    values,
                },
            }]))
        }
        _ => Ok(None),
    }
}

/// Lift advice provider instructions.
fn lift_adv_inst(
    inst: &Instruction,
    span: SourceSpan,
    resolver: &SymbolResolver<'_>,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::AdvLoadW => {
            let effect = effect_for_inst(inst, span, resolver, sigs)?;
            let (_, pushed) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
            Ok(Some(vec![Stmt::AdvLoad {
                span,
                load: AdvLoad { outputs: pushed },
            }]))
        }
        Instruction::AdvPush(imm) => {
            let count = match imm {
                Immediate::Value(value_span) => *value_span.inner() as usize,
                Immediate::Constant(_) => {
                    return Err(LiftingError::UnsupportedInstruction {
                        span,
                        instruction: inst.clone(),
                    });
                }
            };
            if count == 0 || count > 16 {
                return Err(LiftingError::UnsupportedInstruction {
                    span,
                    instruction: inst.clone(),
                });
            }
            let (_, pushed) = stack.apply(0, count, 0);
            Ok(Some(vec![Stmt::Intrinsic {
                span,
                intrinsic: Intrinsic {
                    name: format!("adv_push.{imm}"),
                    args: Vec::new(),
                    results: pushed,
                },
            }]))
        }
        _ => Ok(None),
    }
}

/// Lift intrinsic-style instructions.
fn lift_intrinsic_inst(
    inst: &Instruction,
    span: SourceSpan,
    resolver: &SymbolResolver<'_>,
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
    let effect = effect_for_inst(inst, span, resolver, sigs)?;
    let (args, results) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
    Ok(Some(vec![Stmt::Intrinsic {
        span,
        intrinsic: Intrinsic {
            name,
            args,
            results,
        },
    }]))
}

/// Lift push immediates into assignments.
fn lift_push_inst(
    inst: &Instruction,
    span: SourceSpan,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    match inst {
        Instruction::Push(imm) => {
            let dest = stack.push_fresh();
            let expr: Expr = imm.into();
            Ok(Some(vec![Stmt::Assign { span, dest, expr }]))
        }
        _ => Ok(None),
    }
}

// Helper functions

/// Compute the stack effect for an instruction, resolving call signatures when needed.
pub(crate) fn effect_for_inst(
    inst: &Instruction,
    span: SourceSpan,
    resolver: &SymbolResolver<'_>,
    sigs: &SignatureMap,
) -> LiftingResult<StackEffect> {
    match inst {
        Instruction::Exec(t) | Instruction::Call(t) | Instruction::SysCall(t) => {
            call_effect(t, span, resolver, sigs)
        }
        _ => {
            let effect = StackEffect::from(inst);
            match effect {
                StackEffect::Known { .. } => Ok(effect),
                StackEffect::Unknown => Err(LiftingError::UnsupportedInstruction {
                    span,
                    instruction: inst.clone(),
                }),
            }
        }
    }
}

fn lift_call_like<F>(
    target: &InvocationTarget,
    span: SourceSpan,
    resolver: &SymbolResolver<'_>,
    sigs: &SignatureMap,
    stack: &mut SymbolicStack,
    ctor: F,
) -> LiftingResult<Stmt>
where
    F: Fn(Call) -> Stmt,
{
    let effect = call_effect(target, span, resolver, sigs)?;
    let (args, results) = stack.apply(effect.pops(), effect.pushes(), effect.required_depth());
    let name = call_name(target, resolver).ok_or_else(|| LiftingError::UnknownCallTarget {
        span,
        target: format!("{target}"),
    })?;
    Ok(ctor(Call {
        target: name.to_string(),
        args,
        results,
    }))
}

fn lift_binop(span: SourceSpan, op: BinOp, stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(2);
    let b = stack.pop_entry();
    let a = stack.pop_entry();
    let dest = stack.push_fresh_with_slot_like(a.slot_id, &a.var);
    Stmt::Assign {
        span,
        dest,
        expr: Expr::Binary(op, Box::new(Expr::Var(a.var)), Box::new(Expr::Var(b.var))),
    }
}

fn lift_binop_imm(span: SourceSpan, op: BinOp, imm: &ImmFelt, stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(1);
    let a = stack.pop_entry();
    let dest = stack.push_fresh_with_slot_like(a.slot_id, &a.var);
    let rhs: Expr = imm.into();
    Stmt::Assign {
        span,
        dest,
        expr: Expr::Binary(op, Box::new(Expr::Var(a.var)), Box::new(rhs)),
    }
}

fn lift_unop(span: SourceSpan, op: UnOp, stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(1);
    let a = stack.pop_entry();
    let dest = stack.push_fresh_with_slot_like(a.slot_id, &a.var);
    Stmt::Assign {
        span,
        dest,
        expr: Expr::Unary(op, Box::new(Expr::Var(a.var))),
    }
}

fn lift_incr(span: SourceSpan, stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(1);
    let a = stack.pop_entry();
    let dest = stack.push_fresh_with_slot_like(a.slot_id, &a.var);
    Stmt::Assign {
        span,
        dest,
        expr: Expr::Binary(
            BinOp::Add,
            Box::new(Expr::Var(a.var)),
            Box::new(Expr::Constant(Constant::Felt(1))),
        ),
    }
}

fn lift_binop_u32_imm(
    span: SourceSpan,
    op: BinOp,
    imm: &ImmU32,
    stack: &mut SymbolicStack,
) -> Stmt {
    stack.ensure_depth(1);
    let a = stack.pop_entry();
    let dest = stack.push_fresh_with_slot_like(a.slot_id, &a.var);
    let rhs: Expr = imm.into();
    Stmt::Assign {
        span,
        dest,
        expr: Expr::Binary(op, Box::new(Expr::Var(a.var)), Box::new(rhs)),
    }
}

/// Lift the `cdrop` instruction into a ternary expression assignment.
/// Lift the `cdrop` instruction into a ternary expression assignment.
fn lift_cdrop(span: SourceSpan, stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(3);
    let cond = stack.pop_entry();
    let b = stack.pop_entry();
    let a = stack.pop_entry();
    let dest = stack.push_fresh_with_slot_like(a.slot_id, &a.var);
    Stmt::Assign {
        span,
        dest,
        expr: Expr::Ternary {
            cond: Box::new(Expr::Var(cond.var)),
            then_expr: Box::new(Expr::Var(b.var)),
            else_expr: Box::new(Expr::Var(a.var)),
        },
    }
}

/// Lift the `cswap` instruction into two ternary expression assignments.
fn lift_cswap(span: SourceSpan, stack: &mut SymbolicStack) -> Vec<Stmt> {
    stack.ensure_depth(3);
    let cond = stack.pop_entry();
    let b = stack.pop_entry();
    let a = stack.pop_entry();

    let d = stack.push_fresh_with_slot_like(a.slot_id, &a.var);
    let e = stack.push_fresh_with_slot_like(b.slot_id, &b.var);

    let first = Stmt::Assign {
        span,
        dest: d.clone(),
        expr: Expr::Ternary {
            cond: Box::new(Expr::Var(cond.var.clone())),
            then_expr: Box::new(Expr::Var(b.var.clone())),
            else_expr: Box::new(Expr::Var(a.var.clone())),
        },
    };
    let second = Stmt::Assign {
        span,
        dest: e,
        expr: Expr::Ternary {
            cond: Box::new(Expr::Var(cond.var)),
            then_expr: Box::new(Expr::Var(a.var)),
            else_expr: Box::new(Expr::Var(b.var)),
        },
    };
    vec![first, second]
}

/// Lift the `u32split` instruction into an intrinsic assignment.
fn lift_u32split(span: SourceSpan, stack: &mut SymbolicStack) -> Stmt {
    stack.ensure_depth(1);
    let a = stack.pop_entry();
    let lo = stack.push_fresh_with_slot_like(a.slot_id, &a.var);
    let hi = stack.push_fresh();
    Stmt::Intrinsic {
        span,
        intrinsic: Intrinsic {
            name: "u32split".to_string(),
            args: vec![a.var],
            results: vec![lo, hi],
        },
    }
}

fn lift_padw(span: SourceSpan, stack: &mut SymbolicStack) -> Vec<Stmt> {
    let mut stmts = Vec::with_capacity(4);
    for _ in 0..4 {
        let dest = stack.push_fresh();
        stmts.push(Stmt::Assign {
            span,
            dest,
            expr: Expr::Constant(Constant::Felt(0)),
        });
    }
    stmts
}

fn lift_dup(
    span: SourceSpan,
    idx: usize,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
    let required_depth = idx + 1;
    stack.ensure_depth(required_depth);
    let src = stack.peek(idx).cloned().unwrap();
    let dest = stack.push_fresh();
    Ok(Some(vec![Stmt::Assign {
        span,
        dest,
        expr: Expr::Var(src),
    }]))
}

fn lift_dupw(
    span: SourceSpan,
    idx: usize,
    stack: &mut SymbolicStack,
) -> LiftingResult<Option<Vec<Stmt>>> {
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
        let dest = stack.push_fresh();
        stmts.push(Stmt::Assign {
            span,
            dest,
            expr: Expr::Var(src),
        });
    }
    Ok(Some(stmts))
}

fn assign_from_u32_immediate(
    span: SourceSpan,
    imm: &ImmU32,
    stack: &mut SymbolicStack,
) -> (Var, Stmt) {
    let depth = stack.len();
    let dest = stack.fresh_var(depth);
    // Note: we don't push this to the stack - it's just a temporary for the address.
    let expr: Expr = imm.into();
    (dest.clone(), Stmt::Assign { span, dest, expr })
}

fn call_effect(
    target: &InvocationTarget,
    span: SourceSpan,
    resolver: &SymbolResolver<'_>,
    sigs: &SignatureMap,
) -> LiftingResult<StackEffect> {
    let callee = call_name(target, resolver).ok_or_else(|| LiftingError::UnknownCallTarget {
        span,
        target: format!("{target}"),
    })?;
    let signature = sigs
        .get(&callee)
        .ok_or_else(|| LiftingError::UnknownCallTarget {
            span,
            target: callee.to_string(),
        })?;
    let effect: StackEffect = signature.into();
    match effect {
        StackEffect::Known { .. } => Ok(effect),
        StackEffect::Unknown => Err(LiftingError::UnknownCallTarget {
            span,
            target: callee.to_string(),
        }),
    }
}

fn call_name(target: &InvocationTarget, resolver: &SymbolResolver<'_>) -> Option<SymbolPath> {
    resolver.resolve_target(target)
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Intrinsic;
    use miden_assembly_syntax::debuginfo::SourceSpan;

    /// Ensure u32split emits an intrinsic with low/high ordering and updates stack order.
    #[test]
    fn test_lift_u32split_order() {
        let mut stack = SymbolicStack::new();
        stack.ensure_depth(1);
        let input = stack.peek(0).cloned().expect("input var");

        let stmt = lift_u32split(SourceSpan::UNKNOWN, &mut stack);
        let (lo, hi) = match stmt {
            Stmt::Intrinsic {
                intrinsic:
                    Intrinsic {
                        name,
                        args,
                        results,
                    },
                ..
            } => {
                assert_eq!(name, "u32split");
                assert_eq!(args, vec![input]);
                assert_eq!(results.len(), 2);
                (results[0].clone(), results[1].clone())
            }
            _ => panic!("expected intrinsic from u32split"),
        };

        let top = stack.top_n(2);
        assert_eq!(top.len(), 2);
        assert_eq!(top[0], hi);
        assert_eq!(top[1], lo);
    }

    /// Ensure cswap emits two ternary assignments and preserves stack order.
    #[test]
    fn test_lift_cswap_order() {
        let mut stack = SymbolicStack::new();
        stack.ensure_depth(3);
        let cond = stack.peek(0).cloned().expect("cond");
        let b = stack.peek(1).cloned().expect("b");
        let a = stack.peek(2).cloned().expect("a");

        let stmts = lift_cswap(SourceSpan::UNKNOWN, &mut stack);
        assert_eq!(stmts.len(), 2);

        let (d, first_expr) = match &stmts[0] {
            Stmt::Assign { dest, expr, .. } => (dest.clone(), expr.clone()),
            _ => panic!("expected first cswap assignment"),
        };
        let (e, second_expr) = match &stmts[1] {
            Stmt::Assign { dest, expr, .. } => (dest.clone(), expr.clone()),
            _ => panic!("expected second cswap assignment"),
        };

        match first_expr {
            Expr::Ternary {
                cond: c,
                then_expr,
                else_expr,
            } => {
                assert_eq!(*c, Expr::Var(cond.clone()));
                assert_eq!(*then_expr, Expr::Var(b.clone()));
                assert_eq!(*else_expr, Expr::Var(a.clone()));
            }
            _ => panic!("expected ternary for first cswap assignment"),
        }

        match second_expr {
            Expr::Ternary {
                cond: c,
                then_expr,
                else_expr,
            } => {
                assert_eq!(*c, Expr::Var(cond));
                assert_eq!(*then_expr, Expr::Var(a));
                assert_eq!(*else_expr, Expr::Var(b));
            }
            _ => panic!("expected ternary for second cswap assignment"),
        }

        let top = stack.top_n(2);
        assert_eq!(top.len(), 2);
        assert_eq!(top[0], e);
        assert_eq!(top[1], d);
    }
}
