//! Stack-signature inference.

mod domain;
mod effects;
mod solver;

pub use domain::{ProcSignature, SignatureMap};
pub use effects::InstructionEffect;
pub use solver::infer_signatures;
