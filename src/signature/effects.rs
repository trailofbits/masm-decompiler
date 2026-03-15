use miden_assembly_syntax::ast::{Immediate, Instruction};
use miden_assembly_syntax::parser::PushValue;

/// Describes the local stack effect of a single instruction or operation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackEffect {
    Known {
        /// The number of elements popped from the stack.
        pops: usize,
        /// The number of new elements pushed onto the stack.
        pushes: usize,
        /// The stack depth required to execute the instruction or operation.
        /// Guaranteed to be greater than or equal to `pops`.
        required_depth: usize,
    },
    Unknown,
}

impl StackEffect {
    pub const fn known(pops: usize, pushes: usize) -> Self {
        StackEffect::Known {
            pops,
            pushes,
            required_depth: pops,
        }
    }

    pub const fn unknown() -> Self {
        StackEffect::Unknown
    }

    pub const fn with_required_depth(self, required_depth: usize) -> Self {
        match self {
            StackEffect::Known { pops, pushes, .. } => StackEffect::Known {
                pops,
                pushes,
                required_depth,
            },
            StackEffect::Unknown => StackEffect::Unknown,
        }
    }

    /// Returns the net stack effect (pushes - pops) if known.
    pub fn net_effect(&self) -> Option<isize> {
        match self {
            StackEffect::Known { pops, pushes, .. } => Some(*pushes as isize - *pops as isize),
            StackEffect::Unknown => None,
        }
    }

    /// Compose two effects in sequence: `self` followed by `other`.
    ///
    /// Returns `Unknown` if either effect is unknown.
    ///
    /// # Semantics
    ///
    /// After `self` executes, it has popped `self.pops` values and pushed
    /// `self.pushes` new values. The `other` effect then operates on this
    /// modified stack, first consuming from `self`'s pushed values before
    /// reaching the original stack.
    pub fn then(self, other: Self) -> Self {
        let StackEffect::Known {
            pops: self_pops,
            pushes: self_pushes,
            required_depth: self_required_depth,
        } = self
        else {
            return StackEffect::Unknown;
        };

        let StackEffect::Known {
            pops: other_pops,
            pushes: other_pushes,
            required_depth: other_required_depth,
        } = other
        else {
            return StackEffect::Unknown;
        };

        // `other` consumes from `self`'s pushes first, then from original stack.
        let other_pops_from_original = other_pops.saturating_sub(self_pushes);
        let combined_pops = self_pops + other_pops_from_original;

        // Values remaining from `self` after `other`'s consumption, plus `other`'s pushes.
        let remaining_from_self = self_pushes.saturating_sub(other_pops);
        let combined_pushes = remaining_from_self + other_pushes;

        // Required depth calculation:
        // - `self` needs `self_required_depth` on entry
        // - `other` needs `other_required_depth` after `self`, which means
        //   `other_required_depth - self_pushes + self_pops` from original stack
        let self_net = self_pushes as isize - self_pops as isize;
        let other_required_from_original = if self_net >= 0 {
            other_required_depth.saturating_sub(self_net as usize)
        } else {
            other_required_depth + (-self_net) as usize
        };

        // Maintain the invariant: required_depth >= pops
        let combined_required_depth = self_required_depth
            .max(other_required_from_original)
            .max(combined_pops);

        StackEffect::Known {
            pops: combined_pops,
            pushes: combined_pushes,
            required_depth: combined_required_depth,
        }
    }
}

impl From<&Instruction> for StackEffect {
    fn from(inst: &Instruction) -> Self {
        use Instruction::*;

        // Unary instructions
        let unary = matches!(
            inst,
            ExpImm(_)
                | ILog2
                | Inv
                | Incr
                | IsOdd
                | Pow2
                | Neg
                | Not
                | EqImm(_)
                | NeqImm(_)
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
                | U32ShlImm(_)
                | U32ShrImm(_)
                | U32DivImm(_)
                | U32ModImm(_)
                | U32RotlImm(_)
                | U32RotrImm(_)
        );
        if unary {
            return StackEffect::known(1, 1);
        }

        let binary = matches!(
            inst,
            Add | Sub
                | Mul
                | Div
                | Exp
                | ExpBitLength(_)
                | And
                | Or
                | Xor
                | Eq
                | Neq
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
            return StackEffect::known(2, 1);
        }

        match inst {
            // Nop
            Nop => StackEffect::known(0, 0),

            // Assertions
            Assert | AssertWithError(_) | Assertz | AssertzWithError(_) => {
                StackEffect::known(1, 0).with_required_depth(1)
            }
            AssertEq | AssertEqWithError(_) => StackEffect::known(2, 0).with_required_depth(2),
            AssertEqw | AssertEqwWithError(_) => StackEffect::known(8, 0).with_required_depth(8),

            // Stack operations
            Drop => StackEffect::known(1, 0),
            DropW => StackEffect::known(4, 0),
            PadW => StackEffect::known(0, 4),

            Dup0 => StackEffect::known(0, 1).with_required_depth(1),
            Dup1 => StackEffect::known(0, 1).with_required_depth(2),
            Dup2 => StackEffect::known(0, 1).with_required_depth(3),
            Dup3 => StackEffect::known(0, 1).with_required_depth(4),
            Dup4 => StackEffect::known(0, 1).with_required_depth(5),
            Dup5 => StackEffect::known(0, 1).with_required_depth(6),
            Dup6 => StackEffect::known(0, 1).with_required_depth(7),
            Dup7 => StackEffect::known(0, 1).with_required_depth(8),
            Dup8 => StackEffect::known(0, 1).with_required_depth(9),
            Dup9 => StackEffect::known(0, 1).with_required_depth(10),
            Dup10 => StackEffect::known(0, 1).with_required_depth(11),
            Dup11 => StackEffect::known(0, 1).with_required_depth(12),
            Dup12 => StackEffect::known(0, 1).with_required_depth(13),
            Dup13 => StackEffect::known(0, 1).with_required_depth(14),
            Dup14 => StackEffect::known(0, 1).with_required_depth(15),
            Dup15 => StackEffect::known(0, 1).with_required_depth(16),

            DupW0 => StackEffect::known(0, 4).with_required_depth(4),
            DupW1 => StackEffect::known(0, 4).with_required_depth(8),
            DupW2 => StackEffect::known(0, 4).with_required_depth(12),
            DupW3 => StackEffect::known(0, 4).with_required_depth(16),

            // We model stack permutations as simply clobbering the effected stack slots.
            Swap1 => StackEffect::known(2, 2),
            Swap2 => StackEffect::known(3, 3),
            Swap3 => StackEffect::known(4, 4),
            Swap4 => StackEffect::known(5, 5),
            Swap5 => StackEffect::known(6, 6),
            Swap6 => StackEffect::known(7, 7),
            Swap7 => StackEffect::known(8, 8),
            Swap8 => StackEffect::known(9, 9),
            Swap9 => StackEffect::known(10, 10),
            Swap10 => StackEffect::known(11, 11),
            Swap11 => StackEffect::known(12, 12),
            Swap12 => StackEffect::known(13, 13),
            Swap13 => StackEffect::known(14, 14),
            Swap14 => StackEffect::known(15, 15),
            Swap15 => StackEffect::known(16, 16),

            SwapW1 => StackEffect::known(8, 8),
            SwapW2 => StackEffect::known(12, 12),
            SwapW3 => StackEffect::known(16, 16),
            SwapDw => StackEffect::known(16, 16),

            CSwap => StackEffect::known(3, 2),
            CSwapW => StackEffect::known(9, 8),
            CDrop => StackEffect::known(3, 1),
            CDropW => StackEffect::known(9, 4),
            Reversew => StackEffect::known(4, 4),

            MovUp2 => StackEffect::known(3, 3),
            MovUp3 => StackEffect::known(4, 4),
            MovUp4 => StackEffect::known(5, 5),
            MovUp5 => StackEffect::known(6, 6),
            MovUp6 => StackEffect::known(7, 7),
            MovUp7 => StackEffect::known(8, 8),
            MovUp8 => StackEffect::known(9, 9),
            MovUp9 => StackEffect::known(10, 10),
            MovUp10 => StackEffect::known(11, 11),
            MovUp11 => StackEffect::known(12, 12),
            MovUp12 => StackEffect::known(13, 13),
            MovUp13 => StackEffect::known(14, 14),
            MovUp14 => StackEffect::known(15, 15),
            MovUp15 => StackEffect::known(16, 16),

            MovDn2 => StackEffect::known(3, 3),
            MovDn3 => StackEffect::known(4, 4),
            MovDn4 => StackEffect::known(5, 5),
            MovDn5 => StackEffect::known(6, 6),
            MovDn6 => StackEffect::known(7, 7),
            MovDn7 => StackEffect::known(8, 8),
            MovDn8 => StackEffect::known(9, 9),
            MovDn9 => StackEffect::known(10, 10),
            MovDn10 => StackEffect::known(11, 11),
            MovDn11 => StackEffect::known(12, 12),
            MovDn12 => StackEffect::known(13, 13),
            MovDn13 => StackEffect::known(14, 14),
            MovDn14 => StackEffect::known(15, 15),
            MovDn15 => StackEffect::known(16, 16),

            MovUpW2 => StackEffect::known(12, 12),
            MovUpW3 => StackEffect::known(16, 16),
            MovDnW2 => StackEffect::known(12, 12),
            MovDnW3 => StackEffect::known(16, 16),

            // Remaining U32 operations
            U32OverflowingAdd => StackEffect::known(2, 2),
            U32OverflowingAddImm(_) => StackEffect::known(1, 2),
            U32WideningAdd => StackEffect::known(2, 2),
            U32WideningAddImm(_) => StackEffect::known(1, 2),
            U32OverflowingSub => StackEffect::known(2, 2),
            U32OverflowingSubImm(_) => StackEffect::known(1, 2),
            U32WideningMul => StackEffect::known(2, 2),
            U32WideningMulImm(_) => StackEffect::known(1, 2),
            U32WideningMadd => StackEffect::known(3, 2),
            U32WideningAdd3 => StackEffect::known(3, 2),
            U32OverflowingAdd3 => StackEffect::known(3, 2),
            U32WrappingAdd3 => StackEffect::known(3, 1),
            U32WrappingMadd => StackEffect::known(3, 1),
            U32DivMod => StackEffect::known(2, 2),
            U32DivModImm(_) => StackEffect::known(1, 2),
            U32Test => StackEffect::known(0, 1).with_required_depth(1),
            U32TestW => StackEffect::known(0, 1).with_required_depth(4),
            U32Assert | U32AssertWithError(_) => StackEffect::known(0, 0).with_required_depth(1),
            U32Assert2 | U32Assert2WithError(_) => StackEffect::known(0, 0).with_required_depth(2),
            U32AssertW | U32AssertWWithError(_) => StackEffect::known(0, 0).with_required_depth(4),
            U32Split => StackEffect::known(1, 2),

            // Remaining word-size operations.
            Eqw => StackEffect::known(0, 1).with_required_depth(8),

            // Extension field operations.
            Ext2Add | Ext2Sub | Ext2Mul | Ext2Div => StackEffect::known(4, 2),
            Ext2Neg | Ext2Inv => StackEffect::known(2, 2),

            // TODO: Review remaining instruction effects.

            // Cryptographic operations
            Hash => StackEffect::known(4, 4),
            HMerge => StackEffect::known(8, 4),
            HPerm => StackEffect::known(12, 12),
            MTreeGet => StackEffect::known(2, 4).with_required_depth(6),
            MTreeSet => StackEffect::known(10, 8),
            MTreeMerge => StackEffect::known(8, 4),
            MTreeVerify => StackEffect::known(0, 0).with_required_depth(10),
            MTreeVerifyWithError(_) => StackEffect::known(0, 0).with_required_depth(10),

            // Polynomial/circuit operations
            EvalCircuit => StackEffect::known(0, 0).with_required_depth(3),
            HornerBase => StackEffect::known(16, 16),
            HornerExt => StackEffect::known(16, 16),
            LogPrecompile => StackEffect::known(12, 12).with_required_depth(12),

            // FRI folding
            FriExt2Fold4 => StackEffect::known(0, 0).with_required_depth(17),

            // Memory loads/stores
            MemLoad => StackEffect::known(1, 1).with_required_depth(1),
            MemLoadImm(_) => StackEffect::known(0, 1),
            MemLoadWBe => StackEffect::known(5, 4).with_required_depth(5),
            MemLoadWBeImm(_) => StackEffect::known(4, 4).with_required_depth(4),
            MemLoadWLe => StackEffect::known(5, 4).with_required_depth(5),
            MemLoadWLeImm(_) => StackEffect::known(4, 4).with_required_depth(4),

            LocLoad(_) => StackEffect::known(0, 1),
            LocLoadWBe(_) => StackEffect::known(4, 4).with_required_depth(4),
            LocLoadWLe(_) => StackEffect::known(4, 4).with_required_depth(4),

            MemStore => StackEffect::known(2, 0).with_required_depth(2),
            MemStoreImm(_) => StackEffect::known(1, 0).with_required_depth(1),
            MemStoreWBe => StackEffect::known(1, 0).with_required_depth(5),
            MemStoreWBeImm(_) => StackEffect::known(0, 0).with_required_depth(4),
            MemStoreWLe => StackEffect::known(1, 0).with_required_depth(5),
            MemStoreWLeImm(_) => StackEffect::known(0, 0).with_required_depth(4),

            LocStore(_) => StackEffect::known(1, 0).with_required_depth(1),
            LocStoreWBe(_) => StackEffect::known(0, 0).with_required_depth(4),
            LocStoreWLe(_) => StackEffect::known(0, 0).with_required_depth(4),

            MemStream => StackEffect::known(13, 13).with_required_depth(13),

            Push(Immediate::Value(spanned)) => match spanned.inner() {
                PushValue::Word(_) => StackEffect::known(0, 4),
                PushValue::Int(_) => StackEffect::known(0, 1),
            },
            Push(Immediate::Constant(_)) | Locaddr(_) | Sdepth => StackEffect::known(0, 1),
            PushSlice(_, range) => StackEffect::known(0, range.len()),
            PushFeltList(values) => StackEffect::known(0, values.len()),

            AdvLoadW => StackEffect::known(4, 4).with_required_depth(4),
            AdvPipe => StackEffect::known(13, 13).with_required_depth(13),
            AdvPush(Immediate::Value(values)) => StackEffect::known(0, *values.inner() as usize),

            SysEvent(_) => StackEffect::known(0, 0),

            // Stack effects from calls are handled manually during analysis.
            Exec(_) | Call(_) | SysCall(_) | DynExec | DynCall => StackEffect::Unknown,

            Debug(_) => StackEffect::known(0, 0),

            Emit => StackEffect::known(0, 0).with_required_depth(1),
            EmitImm(_) => StackEffect::known(0, 0),
            Trace(_) => StackEffect::known(0, 0),
            _ => StackEffect::Unknown,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use miden_assembly_syntax::ast::Instruction;

    #[test]
    fn exp_u32_uses_binary_stack_effect() {
        assert_eq!(
            StackEffect::from(&Instruction::ExpBitLength(32)),
            StackEffect::known(2, 1)
        );
    }

    #[test]
    fn ext2add_uses_pair_stack_effect() {
        assert_eq!(
            StackEffect::from(&Instruction::Ext2Add),
            StackEffect::known(4, 2)
        );
    }

    #[test]
    fn u32assertw_keeps_stack() {
        assert_eq!(
            StackEffect::from(&Instruction::U32AssertW),
            StackEffect::known(0, 0).with_required_depth(4)
        );
    }

    #[test]
    fn u32widening_add_pushes_sum_and_carry() {
        assert_eq!(
            StackEffect::from(&Instruction::U32WideningAdd),
            StackEffect::known(2, 2)
        );
    }

    #[test]
    fn u32widening_add3_pushes_sum_and_carry() {
        assert_eq!(
            StackEffect::from(&Instruction::U32WideningAdd3),
            StackEffect::known(3, 2)
        );
    }

    #[test]
    fn horner_eval_clobbers_the_full_window() {
        assert_eq!(
            StackEffect::from(&Instruction::HornerBase),
            StackEffect::known(16, 16)
        );
        assert_eq!(
            StackEffect::from(&Instruction::HornerExt),
            StackEffect::known(16, 16)
        );
    }

    #[test]
    fn then_push_then_drop_is_neutral() {
        // push: (0, 1, 0) then drop: (1, 0, 1) = (0, 0, 0)
        let push = StackEffect::known(0, 1);
        let drop = StackEffect::known(1, 0);
        let combined = push.then(drop);
        assert_eq!(combined, StackEffect::known(0, 0));
    }

    #[test]
    fn then_drop_then_push_needs_input() {
        // drop: (1, 0, 1) then push: (0, 1, 0) = (1, 1, 1)
        // Drop needs 1 input, push produces 1 output
        let drop = StackEffect::known(1, 0);
        let push = StackEffect::known(0, 1);
        let combined = drop.then(push);
        assert_eq!(combined, StackEffect::known(1, 1));
    }

    #[test]
    fn then_two_drops_needs_two_inputs() {
        // drop: (1, 0, 1) then drop: (1, 0, 1) = (2, 0, 2)
        let drop = StackEffect::known(1, 0);
        let combined = drop.then(drop);
        assert_eq!(combined, StackEffect::known(2, 0));
    }

    #[test]
    fn then_two_pushes_produces_two() {
        // push: (0, 1, 0) then push: (0, 1, 0) = (0, 2, 0)
        let push = StackEffect::known(0, 1);
        let combined = push.then(push);
        assert_eq!(combined, StackEffect::known(0, 2));
    }

    #[test]
    fn then_add_after_two_pushes() {
        // push.push: (0, 2, 0) then add: (2, 1, 2) = (0, 1, 0)
        let two_pushes = StackEffect::known(0, 2);
        let add = StackEffect::known(2, 1);
        let combined = two_pushes.then(add);
        assert_eq!(combined, StackEffect::known(0, 1));
    }

    #[test]
    fn then_add_needs_one_more_input() {
        // push: (0, 1, 0) then add: (2, 1, 2) = (1, 1, 1)
        // Push provides 1, add needs 2, so need 1 from original stack
        let push = StackEffect::known(0, 1);
        let add = StackEffect::known(2, 1);
        let combined = push.then(add);
        assert_eq!(combined, StackEffect::known(1, 1));
    }

    #[test]
    fn then_swap_then_unary_pops_two() {
        // swap: (2, 2, 2) then add.1: (1, 1, 1) = (2, 2, 2)
        // swap provides 2 values, add.1 consumes 1, leaves 1, pushes 1
        let swap = StackEffect::known(2, 2);
        let add1 = StackEffect::known(1, 1);
        let combined = swap.then(add1);
        assert_eq!(combined, StackEffect::known(2, 2));
    }

    #[test]
    fn then_preserves_required_depth_from_first() {
        // dup.5: (0, 1, 6) then drop: (1, 0, 1) = (0, 0, 6)
        // Even though net is 0, we still need depth 6 for the dup
        let dup5 = StackEffect::known(0, 1).with_required_depth(6);
        let drop = StackEffect::known(1, 0);
        let combined = dup5.then(drop);
        assert_eq!(
            combined,
            StackEffect::Known {
                pops: 0,
                pushes: 0,
                required_depth: 6
            }
        );
    }

    #[test]
    fn then_required_depth_accounts_for_stack_shrinkage() {
        // drop: (1, 0, 1) then dup.0: (0, 1, 1)
        // After drop, stack is 1 shorter, so dup.0 needs original depth 2
        let drop = StackEffect::known(1, 0);
        let dup0 = StackEffect::known(0, 1).with_required_depth(1);
        let combined = drop.then(dup0);
        assert_eq!(
            combined,
            StackEffect::Known {
                pops: 1,
                pushes: 1,
                required_depth: 2
            }
        );
    }

    #[test]
    fn then_unknown_propagates() {
        let push = StackEffect::known(0, 1);
        let unknown = StackEffect::Unknown;
        assert_eq!(push.then(unknown), StackEffect::Unknown);
        assert_eq!(unknown.then(push), StackEffect::Unknown);
    }
}
