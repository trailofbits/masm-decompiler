//! Core type-analysis domain.

use std::fmt;

use crate::ir::{IndexExpr, ValueId, Var, VarBase};

/// Conservative type inferred for a stack value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum InferredType {
    /// Type could not be determined.
    Unknown,
    /// Generic field element.
    Felt,
    /// Boolean value (`0` or `1`).
    Bool,
    /// 32-bit unsigned integer.
    U32,
    /// Element address.
    Address,
}

impl InferredType {
    /// Combine two values from different control-flow paths.
    ///
    /// `Unknown` means at least one path is opaque, so the result is unknown.
    /// Distinct known subtypes join to their least upper bound in the lattice
    /// `Bool <: U32 <: Felt`, with `Address` as a sibling of `U32`.
    pub fn combine_paths(self, other: Self) -> Self {
        match (self, other) {
            (a, b) if a == b => a,
            (Self::Unknown, _) | (_, Self::Unknown) => Self::Unknown,
            // Bool <: U32
            (Self::Bool, Self::U32) | (Self::U32, Self::Bool) => Self::U32,
            _ => Self::Felt,
        }
    }

    /// Refine a stored type with newly inferred information.
    ///
    /// Existing `Unknown` values are replaced by `new_type`. Existing known
    /// values are widened to their least upper bound in the lattice
    /// `Bool <: U32 <: Felt` if they disagree, with `Address` as a sibling
    /// of `U32`.
    pub fn refine(self, new_type: Self) -> Self {
        match (self, new_type) {
            (Self::Unknown, t) => t,
            (t, Self::Unknown) => t,
            (a, b) if a == b => a,
            // Bool <: U32
            (Self::Bool, Self::U32) | (Self::U32, Self::Bool) => Self::U32,
            _ => Self::Felt,
        }
    }
}

impl fmt::Display for InferredType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unknown => write!(f, "Unknown"),
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
    /// No requirement is known.
    Unknown,
    /// Any value promotable to felt is accepted.
    Felt,
    /// Boolean is required.
    Bool,
    /// U32 is required.
    U32,
    /// Address is required.
    Address,
}

impl TypeRequirement {
    /// Meet two requirements.
    ///
    /// `Unknown` acts as "no constraint". `Felt` is a supertype of
    /// `Bool`/`U32`/`Address`, so meeting with `Felt` keeps the other
    /// requirement. Conflicts collapse to `Unknown` to avoid unsound claims.
    pub fn meet(self, other: Self) -> Self {
        match (self, other) {
            (Self::Unknown, req) | (req, Self::Unknown) => req,
            (Self::Felt, req) | (req, Self::Felt) => req,
            (a, b) if a == b => a,
            _ => Self::Unknown,
        }
    }

    /// Convert an inferred type to the corresponding exact requirement.
    pub fn from_inferred(ty: InferredType) -> Self {
        match ty {
            InferredType::Unknown => Self::Unknown,
            InferredType::Felt => Self::Felt,
            InferredType::Bool => Self::Bool,
            InferredType::U32 => Self::U32,
            InferredType::Address => Self::Address,
        }
    }
}

impl fmt::Display for TypeRequirement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Unknown => write!(f, "Unknown"),
            Self::Felt => write!(f, "Felt"),
            Self::Bool => write!(f, "Bool"),
            Self::U32 => write!(f, "U32"),
            Self::Address => write!(f, "Address"),
        }
    }
}

/// Compatibility result for `actual <: expected` checks.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Compatibility {
    /// The value is known compatible with the requirement.
    Compatible,
    /// The value is known incompatible with the requirement.
    Incompatible,
    /// Compatibility cannot be decided from current information.
    Indeterminate,
}

/// Check whether an inferred value type satisfies a requirement.
pub fn check_compatibility(actual: InferredType, expected: TypeRequirement) -> Compatibility {
    match expected {
        TypeRequirement::Unknown => Compatibility::Indeterminate,
        TypeRequirement::Felt => match actual {
            InferredType::Unknown => Compatibility::Indeterminate,
            InferredType::Felt | InferredType::Bool | InferredType::U32 | InferredType::Address => {
                Compatibility::Compatible
            }
        },
        TypeRequirement::Bool => match actual {
            InferredType::Unknown => Compatibility::Indeterminate,
            InferredType::Bool => Compatibility::Compatible,
            _ => Compatibility::Incompatible,
        },
        TypeRequirement::U32 => match actual {
            InferredType::Unknown => Compatibility::Indeterminate,
            InferredType::U32 | InferredType::Bool => Compatibility::Compatible,
            _ => Compatibility::Incompatible,
        },
        TypeRequirement::Address => match actual {
            InferredType::Unknown => Compatibility::Indeterminate,
            InferredType::Address => Compatibility::Compatible,
            _ => Compatibility::Incompatible,
        },
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

    // -- check_compatibility --------------------------------------------------

    #[test]
    fn felt_accepts_promotable_types() {
        assert_eq!(
            check_compatibility(InferredType::Bool, TypeRequirement::Felt),
            Compatibility::Compatible
        );
        assert_eq!(
            check_compatibility(InferredType::U32, TypeRequirement::Felt),
            Compatibility::Compatible
        );
        assert_eq!(
            check_compatibility(InferredType::Address, TypeRequirement::Felt),
            Compatibility::Compatible
        );
    }

    #[test]
    fn bool_is_compatible_with_u32() {
        assert_eq!(
            check_compatibility(InferredType::Bool, TypeRequirement::U32),
            Compatibility::Compatible
        );
    }

    #[test]
    fn mismatched_exact_types_are_incompatible() {
        assert_eq!(
            check_compatibility(InferredType::Felt, TypeRequirement::Bool),
            Compatibility::Incompatible
        );
        assert_eq!(
            check_compatibility(InferredType::Felt, TypeRequirement::U32),
            Compatibility::Incompatible
        );
        assert_eq!(
            check_compatibility(InferredType::U32, TypeRequirement::Bool),
            Compatibility::Incompatible
        );
        assert_eq!(
            check_compatibility(InferredType::Bool, TypeRequirement::Address),
            Compatibility::Incompatible
        );
        assert_eq!(
            check_compatibility(InferredType::Address, TypeRequirement::Bool),
            Compatibility::Incompatible
        );
    }

    #[test]
    fn unknown_actual_is_indeterminate() {
        assert_eq!(
            check_compatibility(InferredType::Unknown, TypeRequirement::Bool),
            Compatibility::Indeterminate
        );
        assert_eq!(
            check_compatibility(InferredType::Unknown, TypeRequirement::Felt),
            Compatibility::Indeterminate
        );
    }

    // -- combine_paths --------------------------------------------------------

    #[test]
    fn combine_paths_same_type() {
        assert_eq!(
            InferredType::Bool.combine_paths(InferredType::Bool),
            InferredType::Bool
        );
        assert_eq!(
            InferredType::U32.combine_paths(InferredType::U32),
            InferredType::U32
        );
        assert_eq!(
            InferredType::Felt.combine_paths(InferredType::Felt),
            InferredType::Felt
        );
    }

    #[test]
    fn combine_paths_bool_u32_yields_u32() {
        assert_eq!(
            InferredType::Bool.combine_paths(InferredType::U32),
            InferredType::U32
        );
        assert_eq!(
            InferredType::U32.combine_paths(InferredType::Bool),
            InferredType::U32
        );
    }

    #[test]
    fn combine_paths_with_felt_yields_felt() {
        assert_eq!(
            InferredType::Bool.combine_paths(InferredType::Felt),
            InferredType::Felt
        );
        assert_eq!(
            InferredType::U32.combine_paths(InferredType::Felt),
            InferredType::Felt
        );
        assert_eq!(
            InferredType::Address.combine_paths(InferredType::Felt),
            InferredType::Felt
        );
    }

    #[test]
    fn combine_paths_address_siblings_yield_felt() {
        assert_eq!(
            InferredType::Bool.combine_paths(InferredType::Address),
            InferredType::Felt
        );
        assert_eq!(
            InferredType::U32.combine_paths(InferredType::Address),
            InferredType::Felt
        );
    }

    #[test]
    fn combine_paths_unknown_yields_unknown() {
        assert_eq!(
            InferredType::Bool.combine_paths(InferredType::Unknown),
            InferredType::Unknown
        );
        assert_eq!(
            InferredType::Unknown.combine_paths(InferredType::U32),
            InferredType::Unknown
        );
    }

    // -- refine ---------------------------------------------------------------

    #[test]
    fn refine_unknown_takes_new() {
        assert_eq!(
            InferredType::Unknown.refine(InferredType::Bool),
            InferredType::Bool
        );
        assert_eq!(
            InferredType::Unknown.refine(InferredType::U32),
            InferredType::U32
        );
    }

    #[test]
    fn refine_bool_u32_yields_u32() {
        assert_eq!(
            InferredType::Bool.refine(InferredType::U32),
            InferredType::U32
        );
        assert_eq!(
            InferredType::U32.refine(InferredType::Bool),
            InferredType::U32
        );
    }

    #[test]
    fn refine_with_felt_yields_felt() {
        assert_eq!(
            InferredType::Bool.refine(InferredType::Felt),
            InferredType::Felt
        );
        assert_eq!(
            InferredType::U32.refine(InferredType::Felt),
            InferredType::Felt
        );
    }

    #[test]
    fn refine_address_siblings_yield_felt() {
        assert_eq!(
            InferredType::Bool.refine(InferredType::Address),
            InferredType::Felt
        );
        assert_eq!(
            InferredType::U32.refine(InferredType::Address),
            InferredType::Felt
        );
    }
}
