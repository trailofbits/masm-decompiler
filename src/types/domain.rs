//! Core type-analysis domain.

use std::fmt;

use crate::ir::{IndexExpr, ValueId, Var, VarBase};

/// Internal dataflow fact for the scalar type chain `Bool < Address < U32 < Felt`.
///
/// This type is used within the type analysis pass for lattice-based inference.
/// It is not exposed outside `src/types`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum TypeFact {
    /// Generic field element (top of lattice).
    Felt,
    /// 32-bit unsigned integer.
    U32,
    /// Element address (refinement of U32).
    Address,
    /// Boolean value (bottom of lattice).
    Bool,
}

impl TypeFact {
    /// Numeric rank in the chain `Bool(0) < Address(1) < U32(2) < Felt(3)`.
    const fn rank(self) -> u8 {
        match self {
            Self::Bool => 0,
            Self::Address => 1,
            Self::U32 => 2,
            Self::Felt => 3,
        }
    }

    /// Least upper bound (join) in the chain lattice.
    ///
    /// Used at control-flow merge points (if-phi, loop-phi).
    pub(super) fn join(self, other: Self) -> Self {
        if self.rank() >= other.rank() {
            self
        } else {
            other
        }
    }

    /// Greatest lower bound (meet/glb) in the chain lattice.
    ///
    /// Used when accumulating evidence about the same SSA value or storage cell.
    pub(super) fn glb(self, other: Self) -> Self {
        if self.rank() <= other.rank() {
            self
        } else {
            other
        }
    }

    /// Check whether `self` (actual inferred fact) satisfies `req` (expected).
    ///
    /// Returns `true` when `self` is at least as specific as `req`
    /// (i.e. `self <= req` in the lattice order).
    pub(super) fn satisfies(self, req: Self) -> bool {
        self.rank() <= req.rank()
    }

    /// Convert to the public `InferredType` surface type.
    pub(super) fn to_inferred_type(self) -> InferredType {
        match self {
            Self::Felt => InferredType::Felt,
            Self::U32 => InferredType::U32,
            Self::Address => InferredType::Address,
            Self::Bool => InferredType::Bool,
        }
    }

    /// Convert to the public `TypeRequirement` surface type.
    pub(super) fn to_requirement(self) -> TypeRequirement {
        match self {
            Self::Felt => TypeRequirement::Felt,
            Self::U32 => TypeRequirement::U32,
            Self::Address => TypeRequirement::Address,
            Self::Bool => TypeRequirement::Bool,
        }
    }

    /// Convert from a public `InferredType`.
    pub(super) fn from_inferred_type(ty: InferredType) -> Self {
        match ty {
            InferredType::Felt => Self::Felt,
            InferredType::U32 => Self::U32,
            InferredType::Address => Self::Address,
            InferredType::Bool => Self::Bool,
        }
    }

    /// Convert from a public `TypeRequirement`.
    pub(super) fn from_requirement(req: TypeRequirement) -> Self {
        match req {
            TypeRequirement::Felt => Self::Felt,
            TypeRequirement::U32 => Self::U32,
            TypeRequirement::Address => Self::Address,
            TypeRequirement::Bool => Self::Bool,
        }
    }
}

/// Conservative type inferred for a stack value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferredType {
    /// Generic field element.
    Felt,
    /// Boolean value (`0` or `1`).
    Bool,
    /// 32-bit unsigned integer.
    U32,
    /// Element address.
    Address,
}

impl fmt::Display for InferredType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Felt => write!(f, "Felt"),
            Self::Bool => write!(f, "Bool"),
            Self::U32 => write!(f, "U32"),
            Self::Address => write!(f, "Address"),
        }
    }
}

/// Required type at a use site.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TypeRequirement {
    /// Any value promotable to felt is accepted.
    Felt,
    /// Boolean is required.
    Bool,
    /// U32 is required.
    U32,
    /// Address is required.
    Address,
}

impl fmt::Display for TypeRequirement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Felt => write!(f, "Felt"),
            Self::Bool => write!(f, "Bool"),
            Self::U32 => write!(f, "U32"),
            Self::Address => write!(f, "Address"),
        }
    }
}

/// Base identity used in type maps.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VarBaseKey {
    /// Concrete SSA value.
    Value(ValueId),
    /// Repeat-loop input identity.
    LoopInput(usize),
}

/// Hashable identity key for a variable version.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct VarKey {
    /// Base identity.
    pub base: VarBaseKey,
    /// SSA subscript.
    pub subscript: IndexExpr,
}

impl VarKey {
    /// Build a key from a variable.
    pub fn from_var(var: &Var) -> Self {
        let base = match var.base {
            VarBase::Value(id) => VarBaseKey::Value(id),
            VarBase::LoopInput { loop_depth } => VarBaseKey::LoopInput(loop_depth),
        };
        Self {
            base,
            subscript: var.subscript.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // -- TypeFact lattice -------------------------------------------------

    #[test]
    fn type_fact_join_is_lub() {
        assert_eq!(TypeFact::Bool.join(TypeFact::Bool), TypeFact::Bool);
        assert_eq!(TypeFact::U32.join(TypeFact::U32), TypeFact::U32);
        assert_eq!(TypeFact::Felt.join(TypeFact::Felt), TypeFact::Felt);
        assert_eq!(TypeFact::Bool.join(TypeFact::Address), TypeFact::Address);
        assert_eq!(TypeFact::Address.join(TypeFact::Bool), TypeFact::Address);
        assert_eq!(TypeFact::Bool.join(TypeFact::U32), TypeFact::U32);
        assert_eq!(TypeFact::U32.join(TypeFact::Bool), TypeFact::U32);
        assert_eq!(TypeFact::Address.join(TypeFact::U32), TypeFact::U32);
        assert_eq!(TypeFact::U32.join(TypeFact::Address), TypeFact::U32);
        assert_eq!(TypeFact::Bool.join(TypeFact::Felt), TypeFact::Felt);
        assert_eq!(TypeFact::U32.join(TypeFact::Felt), TypeFact::Felt);
        assert_eq!(TypeFact::Address.join(TypeFact::Felt), TypeFact::Felt);
    }

    #[test]
    fn type_fact_glb_is_greatest_lower_bound() {
        assert_eq!(TypeFact::Bool.glb(TypeFact::Bool), TypeFact::Bool);
        assert_eq!(TypeFact::U32.glb(TypeFact::U32), TypeFact::U32);
        assert_eq!(TypeFact::Address.glb(TypeFact::Bool), TypeFact::Bool);
        assert_eq!(TypeFact::Bool.glb(TypeFact::Address), TypeFact::Bool);
        assert_eq!(TypeFact::U32.glb(TypeFact::Address), TypeFact::Address);
        assert_eq!(TypeFact::Address.glb(TypeFact::U32), TypeFact::Address);
        assert_eq!(TypeFact::Felt.glb(TypeFact::Bool), TypeFact::Bool);
        assert_eq!(TypeFact::Felt.glb(TypeFact::U32), TypeFact::U32);
        assert_eq!(TypeFact::Felt.glb(TypeFact::Address), TypeFact::Address);
    }

    #[test]
    fn type_fact_satisfies_is_subtype_check() {
        // Bool satisfies everything
        assert!(TypeFact::Bool.satisfies(TypeFact::Bool));
        assert!(TypeFact::Bool.satisfies(TypeFact::Address));
        assert!(TypeFact::Bool.satisfies(TypeFact::U32));
        assert!(TypeFact::Bool.satisfies(TypeFact::Felt));
        // Address satisfies Address, U32, Felt but not Bool
        assert!(TypeFact::Address.satisfies(TypeFact::Address));
        assert!(TypeFact::Address.satisfies(TypeFact::U32));
        assert!(TypeFact::Address.satisfies(TypeFact::Felt));
        assert!(!TypeFact::Address.satisfies(TypeFact::Bool));
        // U32 satisfies U32, Felt but not Address, Bool
        assert!(TypeFact::U32.satisfies(TypeFact::U32));
        assert!(TypeFact::U32.satisfies(TypeFact::Felt));
        assert!(!TypeFact::U32.satisfies(TypeFact::Address));
        assert!(!TypeFact::U32.satisfies(TypeFact::Bool));
        // Felt only satisfies Felt
        assert!(TypeFact::Felt.satisfies(TypeFact::Felt));
        assert!(!TypeFact::Felt.satisfies(TypeFact::U32));
        assert!(!TypeFact::Felt.satisfies(TypeFact::Bool));
        assert!(!TypeFact::Felt.satisfies(TypeFact::Address));
    }

    mod proptests {
        use super::*;
        use proptest::prelude::*;

        fn arb_type_fact() -> impl Strategy<Value = TypeFact> {
            prop_oneof![
                Just(TypeFact::Bool),
                Just(TypeFact::Address),
                Just(TypeFact::U32),
                Just(TypeFact::Felt),
            ]
        }

        proptest! {
            #[test]
            fn join_commutative(a in arb_type_fact(), b in arb_type_fact()) {
                prop_assert_eq!(a.join(b), b.join(a));
            }

            #[test]
            fn join_associative(a in arb_type_fact(), b in arb_type_fact(), c in arb_type_fact()) {
                prop_assert_eq!(a.join(b).join(c), a.join(b.join(c)));
            }

            #[test]
            fn join_idempotent(a in arb_type_fact()) {
                prop_assert_eq!(a.join(a), a);
            }

            #[test]
            fn glb_commutative(a in arb_type_fact(), b in arb_type_fact()) {
                prop_assert_eq!(a.glb(b), b.glb(a));
            }

            #[test]
            fn glb_associative(a in arb_type_fact(), b in arb_type_fact(), c in arb_type_fact()) {
                prop_assert_eq!(a.glb(b).glb(c), a.glb(b.glb(c)));
            }

            #[test]
            fn glb_idempotent(a in arb_type_fact()) {
                prop_assert_eq!(a.glb(a), a);
            }

            #[test]
            fn absorption_join_glb(a in arb_type_fact(), b in arb_type_fact()) {
                prop_assert_eq!(a.join(a.glb(b)), a);
            }

            #[test]
            fn absorption_glb_join(a in arb_type_fact(), b in arb_type_fact()) {
                prop_assert_eq!(a.glb(a.join(b)), a);
            }

            #[test]
            fn satisfies_is_reflexive(a in arb_type_fact()) {
                prop_assert!(a.satisfies(a));
            }

            #[test]
            fn satisfies_consistent_with_glb(a in arb_type_fact(), b in arb_type_fact()) {
                if a.glb(b) == a {
                    prop_assert!(a.satisfies(b));
                }
            }
        }
    }
}
