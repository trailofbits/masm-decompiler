//! Stack-signature inference.

mod domain;
mod effects;
mod solver;

pub use domain::{ProcSignature, Range, SignatureMap, SlotShape};
pub use solver::infer_signatures;
pub use effects::{stack_effect, InstructionEffect};
