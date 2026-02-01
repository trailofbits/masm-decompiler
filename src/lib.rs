pub mod analysis;
pub mod callgraph;
pub mod cfg;
pub mod decompile;
pub mod fmt;
pub mod frontend;
pub mod signature;
pub mod ssa;
pub mod structuring;

// Re-export key types for convenient access
pub use decompile::{DecompilationConfig, DecompilationError, DecompilationResult, Decompiler};
pub use frontend::Program;
