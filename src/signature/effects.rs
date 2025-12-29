use miden_assembly_syntax::ast::Instruction;

/// Describes the local stack effect of a single instruction.
#[derive(Debug, Clone, Copy)]
pub enum InstructionEffect {
    Known {
        /// The number of elements popped from the stack.
        pops: usize,
        /// The number of new elements pushed onto the stack.
        pushes: usize,
        /// The stack depth required to execute the instruction.
        /// Guaranteed to be greater than or equal to `pops`.
        required_depth: usize,
    },
    Unknown,
}

impl InstructionEffect {
    pub const fn known(pops: usize, pushes: usize) -> Self {
        InstructionEffect::Known {
            pops,
            pushes,
            required_depth: pops,
        }
    }

    pub const fn unknown() -> Self {
        InstructionEffect::Unknown
    }

    pub const fn with_required_depth(self, required_depth: usize) -> Self {
        match self {
            InstructionEffect::Known { pops, pushes, .. } => InstructionEffect::Known {
                pops,
                pushes,
                required_depth,
            },
            InstructionEffect::Unknown => InstructionEffect::Unknown,
        }
    }
}

impl From<&Instruction> for InstructionEffect {
    fn from(inst: &Instruction) -> Self {
        use Instruction::*;

        // Unary instructions
        let unary = matches!(
            inst,
            Exp | ILog2
                | Inv
                | Incr
                | IsOdd
                | Pow2
                | Neg
                | Not
                | AddImm(_)
                | SubImm(_)
                | MulImm(_)
                | U32Cast
                | U32Clz
                | U32Clo
                | U32Cto
                | U32Ctz
                | U32Not
                | U32Popcnt
                | U32WrappingAddImm(_)
                | U32WrappingSubImm(_)
                | U32WrappingMulImm(_)
        );
        if unary {
            return InstructionEffect::known(1, 1);
        }

        let binary = matches!(
            inst,
            Add | Sub
                | Mul
                | Div
                | And
                | Or
                | Xor
                | Eq
                | Neq
                | Eqw
                | Lt
                | Lte
                | Gt
                | Gte
                | U32WrappingAdd
                | U32WrappingSub
                | U32WrappingMul
                | U32Div
                | U32Mod
                | U32And
                | U32Or
                | U32Xor
                | U32Shl
                | U32Shr
                | U32Rotl
                | U32Rotr
                | U32Lt
                | U32Lte
                | U32Gt
                | U32Gte
                | U32Min
                | U32Max
        );

        if binary {
            return InstructionEffect::known(2, 1);
        }

        match inst {
            // Nop
            Nop => InstructionEffect::known(0, 0),

            // Stack operations
            Drop => InstructionEffect::known(1, 0),
            DropW => InstructionEffect::known(4, 0),
            PadW => InstructionEffect::known(0, 4),

            Dup0 => InstructionEffect::known(0, 1).with_required_depth(1),
            Dup1 => InstructionEffect::known(0, 1).with_required_depth(2),
            Dup2 => InstructionEffect::known(0, 1).with_required_depth(3),
            Dup3 => InstructionEffect::known(0, 1).with_required_depth(4),
            Dup4 => InstructionEffect::known(0, 1).with_required_depth(5),
            Dup5 => InstructionEffect::known(0, 1).with_required_depth(6),
            Dup6 => InstructionEffect::known(0, 1).with_required_depth(7),
            Dup7 => InstructionEffect::known(0, 1).with_required_depth(8),
            Dup8 => InstructionEffect::known(0, 1).with_required_depth(9),
            Dup9 => InstructionEffect::known(0, 1).with_required_depth(10),
            Dup10 => InstructionEffect::known(0, 1).with_required_depth(11),
            Dup11 => InstructionEffect::known(0, 1).with_required_depth(12),
            Dup12 => InstructionEffect::known(0, 1).with_required_depth(13),
            Dup13 => InstructionEffect::known(0, 1).with_required_depth(14),
            Dup14 => InstructionEffect::known(0, 1).with_required_depth(15),
            Dup15 => InstructionEffect::known(0, 1).with_required_depth(16),

            DupW0 => InstructionEffect::known(0, 4).with_required_depth(4),
            DupW1 => InstructionEffect::known(0, 4).with_required_depth(8),
            DupW2 => InstructionEffect::known(0, 4).with_required_depth(12),
            DupW3 => InstructionEffect::known(0, 4).with_required_depth(16),

            Swap1 => InstructionEffect::known(0, 0).with_required_depth(2),
            Swap2 => InstructionEffect::known(0, 0).with_required_depth(3),
            Swap3 => InstructionEffect::known(0, 0).with_required_depth(4),
            Swap4 => InstructionEffect::known(0, 0).with_required_depth(5),
            Swap5 => InstructionEffect::known(0, 0).with_required_depth(6),
            Swap6 => InstructionEffect::known(0, 0).with_required_depth(7),
            Swap7 => InstructionEffect::known(0, 0).with_required_depth(8),
            Swap8 => InstructionEffect::known(0, 0).with_required_depth(9),
            Swap9 => InstructionEffect::known(0, 0).with_required_depth(10),
            Swap10 => InstructionEffect::known(0, 0).with_required_depth(11),
            Swap11 => InstructionEffect::known(0, 0).with_required_depth(12),
            Swap12 => InstructionEffect::known(0, 0).with_required_depth(13),
            Swap13 => InstructionEffect::known(0, 0).with_required_depth(14),
            Swap14 => InstructionEffect::known(0, 0).with_required_depth(15),
            Swap15 => InstructionEffect::known(0, 0).with_required_depth(16),

            SwapW1 => InstructionEffect::known(0, 0).with_required_depth(8),
            SwapW2 => InstructionEffect::known(0, 0).with_required_depth(12),
            SwapW3 => InstructionEffect::known(0, 0).with_required_depth(16),
            SwapDw => InstructionEffect::known(0, 0).with_required_depth(16),

            CSwap => InstructionEffect::known(1, 0).with_required_depth(3),
            CSwapW => InstructionEffect::known(1, 0).with_required_depth(9),
            CDrop => InstructionEffect::known(3, 1),
            CDropW => InstructionEffect::known(9, 4),
            Reversew => InstructionEffect::known(4, 4),

            MovUp2 => InstructionEffect::known(0, 0).with_required_depth(3),
            MovUp3 => InstructionEffect::known(0, 0).with_required_depth(4),
            MovUp4 => InstructionEffect::known(0, 0).with_required_depth(5),
            MovUp5 => InstructionEffect::known(0, 0).with_required_depth(6),
            MovUp6 => InstructionEffect::known(0, 0).with_required_depth(7),
            MovUp7 => InstructionEffect::known(0, 0).with_required_depth(8),
            MovUp8 => InstructionEffect::known(0, 0).with_required_depth(9),
            MovUp9 => InstructionEffect::known(0, 0).with_required_depth(10),
            MovUp10 => InstructionEffect::known(0, 0).with_required_depth(11),
            MovUp11 => InstructionEffect::known(0, 0).with_required_depth(12),
            MovUp12 => InstructionEffect::known(0, 0).with_required_depth(13),
            MovUp13 => InstructionEffect::known(0, 0).with_required_depth(14),
            MovUp14 => InstructionEffect::known(0, 0).with_required_depth(15),
            MovUp15 => InstructionEffect::known(0, 0).with_required_depth(16),

            MovDn2 => InstructionEffect::known(0, 0).with_required_depth(3),
            MovDn3 => InstructionEffect::known(0, 0).with_required_depth(4),
            MovDn4 => InstructionEffect::known(0, 0).with_required_depth(5),
            MovDn5 => InstructionEffect::known(0, 0).with_required_depth(6),
            MovDn6 => InstructionEffect::known(0, 0).with_required_depth(7),
            MovDn7 => InstructionEffect::known(0, 0).with_required_depth(8),
            MovDn8 => InstructionEffect::known(0, 0).with_required_depth(9),
            MovDn9 => InstructionEffect::known(0, 0).with_required_depth(10),
            MovDn10 => InstructionEffect::known(0, 0).with_required_depth(11),
            MovDn11 => InstructionEffect::known(0, 0).with_required_depth(12),
            MovDn12 => InstructionEffect::known(0, 0).with_required_depth(13),
            MovDn13 => InstructionEffect::known(0, 0).with_required_depth(14),
            MovDn14 => InstructionEffect::known(0, 0).with_required_depth(15),
            MovDn15 => InstructionEffect::known(0, 0).with_required_depth(16),

            MovUpW2 => InstructionEffect::known(0, 0).with_required_depth(12),
            MovUpW3 => InstructionEffect::known(0, 0).with_required_depth(16),
            MovDnW2 => InstructionEffect::known(0, 0).with_required_depth(12),
            MovDnW3 => InstructionEffect::known(0, 0).with_required_depth(16),

            // Remaining U32 operations
            U32OverflowingAdd => InstructionEffect::known(2, 2),
            U32OverflowingSub => InstructionEffect::known(2, 2),
            U32OverflowingMul => InstructionEffect::known(2, 2),
            U32OverflowingMadd => InstructionEffect::known(2, 3),
            U32OverflowingAdd3 => InstructionEffect::known(2, 3),
            U32WrappingAdd3 => InstructionEffect::known(1, 3),
            U32WrappingMadd => InstructionEffect::known(1, 3),
            U32DivMod => InstructionEffect::known(2, 2),
            U32Test => InstructionEffect::known(1, 0).with_required_depth(1),
            U32TestW => InstructionEffect::known(1, 0).with_required_depth(4),
            U32Assert => InstructionEffect::known(0, 0).with_required_depth(1),
            U32Assert2 => InstructionEffect::known(0, 0).with_required_depth(2),
            U32AssertW => InstructionEffect::known(0, 0).with_required_depth(4),
            U32Split => InstructionEffect::known(1, 2),

            // TODO: Review remaining instruction effects.

            // Cryptographic operations
            Hash => InstructionEffect::known(4, 4),
            HMerge => InstructionEffect::known(8, 4),
            HPerm => InstructionEffect::known(12, 12),
            MTreeGet => InstructionEffect::known(2, 4).with_required_depth(6),
            MTreeSet => InstructionEffect::known(10, 8),
            MTreeMerge => InstructionEffect::known(8, 4),
            MTreeVerify => InstructionEffect::known(0, 0).with_required_depth(10),
            MTreeVerifyWithError(_) => InstructionEffect::known(0, 0).with_required_depth(10),

            // Polynomial/circuit operations
            EvalCircuit => InstructionEffect::known(0, 0).with_required_depth(3),
            HornerBase => InstructionEffect::known(0, 0).with_required_depth(16),
            HornerExt => InstructionEffect::known(0, 0).with_required_depth(16),
            LogPrecompile => InstructionEffect::known(12, 12).with_required_depth(12),

            // FRI folding
            FriExt2Fold4 => InstructionEffect::known(0, 0).with_required_depth(17),

            // Memory loads/stores
            MemLoad => InstructionEffect::known(1, 1).with_required_depth(1),
            MemLoadImm(_) => InstructionEffect::known(0, 1),
            MemLoadWBe => InstructionEffect::known(1, 4).with_required_depth(5),
            MemLoadWBeImm(_) => InstructionEffect::known(0, 4).with_required_depth(4),
            MemLoadWLe => InstructionEffect::known(1, 4).with_required_depth(5),
            MemLoadWLeImm(_) => InstructionEffect::known(0, 4).with_required_depth(4),

            LocLoad(_) => InstructionEffect::known(0, 1),
            LocLoadWBe(_) => InstructionEffect::known(0, 4).with_required_depth(4),
            LocLoadWLe(_) => InstructionEffect::known(0, 4).with_required_depth(4),

            MemStore => InstructionEffect::known(2, 0).with_required_depth(2),
            MemStoreImm(_) => InstructionEffect::known(1, 0).with_required_depth(1),
            MemStoreWBe => InstructionEffect::known(5, 0).with_required_depth(5),
            MemStoreWBeImm(_) => InstructionEffect::known(4, 0).with_required_depth(4),
            MemStoreWLe => InstructionEffect::known(5, 0).with_required_depth(5),
            MemStoreWLeImm(_) => InstructionEffect::known(4, 0).with_required_depth(4),

            LocStore(_) => InstructionEffect::known(1, 0).with_required_depth(1),
            LocStoreWBe(_) => InstructionEffect::known(4, 0).with_required_depth(4),
            LocStoreWLe(_) => InstructionEffect::known(4, 0).with_required_depth(4),

            MemStream => InstructionEffect::known(0, 0).with_required_depth(13),

            Push(_) | Locaddr(_) | EmitImm(_) | Trace(_) => InstructionEffect::known(0, 1),
            PushSlice(_, range) => InstructionEffect::known(0, range.len()),
            PushFeltList(values) => InstructionEffect::known(0, values.len()),

            AdvPipe | AdvPush(_) => InstructionEffect::known(0, 0), // opaque side effects

            SysEvent(_) => InstructionEffect::known(0, 0),

            Exec(_) | Call(_) | SysCall(_) | DynExec | DynCall => InstructionEffect::Unknown,

            Debug(_) => InstructionEffect::known(0, 0),

            Emit => InstructionEffect::known(1, 0),
            _ => InstructionEffect::Unknown,
        }
    }
}
