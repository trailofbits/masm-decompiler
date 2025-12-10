use miden_assembly_syntax::ast::Instruction;

/// Describes the local stack effect of a single instruction.
///
/// `required` is the minimum stack height needed before executing the instruction.
/// For example, `dup4` has `required = 5`, `pops = 0`, `pushes = 1`.
#[derive(Debug, Clone, Copy)]
pub enum InstructionEffect {
    Known { pops: u8, pushes: u8, required: u32 },
    Unknown,
}

impl InstructionEffect {
    pub const fn known(pops: u8, pushes: u8) -> Self {
        InstructionEffect::Known {
            pops,
            pushes,
            required: pops as u32,
        }
    }

    pub const fn with_required(self, required: u32) -> Self {
        match self {
            InstructionEffect::Known { pops, pushes, .. } => {
                InstructionEffect::Known { pops, pushes, required }
            },
            InstructionEffect::Unknown => InstructionEffect::Unknown,
        }
    }
}

/// Returns an `InstructionEffect`; `Unknown` indicates an unmodeled effect.
pub fn stack_effect(instr: &Instruction) -> InstructionEffect {
    use Instruction::*;

    let unary = matches!(
        instr,
        Assert
            | AssertWithError(_)
            | Assertz
            | AssertzWithError(_)
            | Neg
            | ILog2
            | Inv
            | Incr
            | Pow2
            | Exp
            | ExpImm(_)
            | ExpBitLength(_)
            | Not
            | IsOdd
            | U32Test
            | U32TestW
            | U32Assert
            | U32AssertWithError(_)
            | U32AssertW
            | U32AssertWWithError(_)
            | U32Cast
            | U32Not
            | U32Popcnt
            | U32Ctz
            | U32Clz
            | U32Clo
            | U32Cto
            | Locaddr(_)
            | Sdepth
            | Caller
            | Clk
            | MemLoad
            | MemLoadImm(_)
            | MemLoadWBe
            | MemLoadWBeImm(_)
            | MemLoadWLe
            | MemLoadWLeImm(_)
            | LocLoad(_)
            | LocLoadWBe(_)
            | LocLoadWLe(_)
            | AdvLoadW
            | Hash
            | HMerge
            | HPerm
            | FriExt2Fold4
            | HornerBase
            | HornerExt
            | Emit
            | EmitImm(_)
            | Trace(_)
            | ProcRef(_)
    );

    if unary {
        return InstructionEffect::known(1, 1);
    }

    let binary = matches!(
        instr,
        AssertEq
            | AssertEqWithError(_)
            | AssertEqw
            | AssertEqwWithError(_)
            | Add
            | AddImm(_)
            | Sub
            | SubImm(_)
            | Mul
            | MulImm(_)
            | Div
            | DivImm(_)
            | And
            | Or
            | Xor
            | Eq
            | EqImm(_)
            | Neq
            | NeqImm(_)
            | Eqw
            | Lt
            | Lte
            | Gt
            | Gte
            | Ext2Add
            | Ext2Sub
            | Ext2Mul
            | Ext2Div
            | Ext2Neg
            | Ext2Inv
            | U32WrappingAdd
            | U32WrappingAddImm(_)
            | U32OverflowingAdd
            | U32OverflowingAddImm(_)
            | U32OverflowingAdd3
            | U32WrappingAdd3
            | U32WrappingSub
            | U32WrappingSubImm(_)
            | U32OverflowingSub
            | U32OverflowingSubImm(_)
            | U32WrappingMul
            | U32WrappingMulImm(_)
            | U32OverflowingMul
            | U32OverflowingMulImm(_)
            | U32OverflowingMadd
            | U32WrappingMadd
            | U32Div
            | U32DivImm(_)
            | U32Mod
            | U32ModImm(_)
            | U32DivMod
            | U32DivModImm(_)
            | U32And
            | U32Or
            | U32Xor
            | U32Shr
            | U32ShrImm(_)
            | U32Shl
            | U32ShlImm(_)
            | U32Rotr
            | U32RotrImm(_)
            | U32Rotl
            | U32RotlImm(_)
            | U32Lt
            | U32Lte
            | U32Gt
            | U32Gte
            | U32Min
            | U32Max
            | MemStore
            | MemStoreImm(_)
            | MemStoreWBe
            | MemStoreWBeImm(_)
            | MemStoreWLe
            | MemStoreWLeImm(_)
            | LocStore(_)
            | LocStoreWBe(_)
            | LocStoreWLe(_)
            | MTreeGet
            | MTreeSet
            | MTreeMerge
            | MTreeVerify
            | MTreeVerifyWithError(_)
    );

    if binary {
        return InstructionEffect::known(2, 1);
    }

    match instr {
        Nop | Breakpoint => InstructionEffect::known(0, 0),
        Drop => InstructionEffect::known(1, 0),
        DropW | Reversedw => InstructionEffect::known(4, 0),
        PadW => InstructionEffect::known(0, 4),

        Dup0 => InstructionEffect::known(0, 1).with_required(1),
        Dup1 => InstructionEffect::known(0, 1).with_required(2),
        Dup2 => InstructionEffect::known(0, 1).with_required(3),
        Dup3 => InstructionEffect::known(0, 1).with_required(4),
        Dup4 => InstructionEffect::known(0, 1).with_required(5),
        Dup5 => InstructionEffect::known(0, 1).with_required(6),
        Dup6 => InstructionEffect::known(0, 1).with_required(7),
        Dup7 => InstructionEffect::known(0, 1).with_required(8),
        Dup8 => InstructionEffect::known(0, 1).with_required(9),
        Dup9 => InstructionEffect::known(0, 1).with_required(10),
        Dup10 => InstructionEffect::known(0, 1).with_required(11),
        Dup11 => InstructionEffect::known(0, 1).with_required(12),
        Dup12 => InstructionEffect::known(0, 1).with_required(13),
        Dup13 => InstructionEffect::known(0, 1).with_required(14),
        Dup14 => InstructionEffect::known(0, 1).with_required(15),
        Dup15 => InstructionEffect::known(0, 1).with_required(16),
        DupW0 => InstructionEffect::known(0, 4).with_required(4),
        DupW1 => InstructionEffect::known(0, 4).with_required(8),
        DupW2 => InstructionEffect::known(0, 4).with_required(12),
        DupW3 => InstructionEffect::known(0, 4).with_required(16),

        Swap1 | Swap2 | Swap3 | Swap4 | Swap5 | Swap6 | Swap7 | Swap8 | Swap9 | Swap10
        | Swap11 | Swap12 | Swap13 | Swap14 | Swap15 => InstructionEffect::known(2, 2),
        SwapW1 | SwapW2 | SwapW3 | SwapDw | Reversew | CSwap | CSwapW | CDrop | CDropW => {
            InstructionEffect::known(4, 4)
        }

        MovUp2 => InstructionEffect::known(0, 0).with_required(3),
        MovUp3 => InstructionEffect::known(0, 0).with_required(4),
        MovUp4 => InstructionEffect::known(0, 0).with_required(5),
        MovUp5 => InstructionEffect::known(0, 0).with_required(6),
        MovUp6 => InstructionEffect::known(0, 0).with_required(7),
        MovUp7 => InstructionEffect::known(0, 0).with_required(8),
        MovUp8 => InstructionEffect::known(0, 0).with_required(9),
        MovUp9 => InstructionEffect::known(0, 0).with_required(10),
        MovUp10 => InstructionEffect::known(0, 0).with_required(11),
        MovUp11 => InstructionEffect::known(0, 0).with_required(12),
        MovUp12 => InstructionEffect::known(0, 0).with_required(13),
        MovUp13 => InstructionEffect::known(0, 0).with_required(14),
        MovUp14 => InstructionEffect::known(0, 0).with_required(15),
        MovUp15 => InstructionEffect::known(0, 0).with_required(16),

        MovDn2 | MovDn3 | MovDn4 | MovDn5 | MovDn6 | MovDn7 | MovDn8 | MovDn9 | MovDn10
        | MovDn11 | MovDn12 | MovDn13 | MovDn14 | MovDn15 => InstructionEffect::known(0, 0),

        MovUpW2 | MovUpW3 | MovDnW2 | MovDnW3 => InstructionEffect::Unknown, // treat as unknown until modeled precisely

        Push(_) | Locaddr(_) | EmitImm(_) | Trace(_) => InstructionEffect::known(0, 1),
        PushSlice(_, range) => InstructionEffect::known(0, range.len() as u8),
        PushFeltList(vals) => InstructionEffect::known(0, vals.len() as u8),

        MemStream | AdvPipe | AdvPush(_) => InstructionEffect::known(0, 0), // opaque side effects

        SysEvent(_) => InstructionEffect::known(0, 0),

        EvalCircuit | LogPrecompile => InstructionEffect::known(0, 0),

        Exec(_) | Call(_) | SysCall(_) | DynExec | DynCall => InstructionEffect::Unknown,

        Debug(_) => InstructionEffect::known(0, 0),

        Emit => InstructionEffect::known(1, 0),
        _ => InstructionEffect::Unknown,
    }
}
