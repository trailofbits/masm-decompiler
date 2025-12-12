//! Stack-signature inference.

mod domain;
mod effects;
mod solver;

pub use domain::{ProcSignature, Range, SignatureMap, SlotShape};
pub use effects::{InstructionEffect, stack_effect};
pub use solver::infer_signatures;
