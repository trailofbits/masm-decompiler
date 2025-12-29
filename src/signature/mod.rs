//! Stack-signature inference.

mod analysis;
mod domain;
mod effects;

pub use analysis::infer_signatures;
pub use domain::{ProcSignature, SignatureMap};
pub use effects::InstructionEffect;
