pub mod callgraph;
pub mod decompile;
pub mod fmt;
pub mod frontend;
pub mod ir;
pub mod lift;
pub mod signature;
pub mod simplify;
pub mod symbol;
pub mod types;

// Re-export key types for convenient access
pub use decompile::{DecompilationConfig, DecompilationError, DecompilationResult, Decompiler};
pub use frontend::Program;
pub use symbol::path::SymbolPath;
