pub mod callgraph;
pub mod decompile;
pub mod fmt;
pub mod frontend;
pub mod ir;
pub mod lifting;
pub mod signature;

// Re-export key types for convenient access
pub use decompile::{DecompilationConfig, DecompilationError, DecompilationResult, Decompiler};
pub use frontend::Program;
