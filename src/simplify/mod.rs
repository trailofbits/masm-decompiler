//! IR simplification passes (dead code elimination, expression propagation, etc.).

pub mod eliminate;
pub mod propagate;
pub mod simplify;
pub mod used_vars;

pub use eliminate::eliminate_dead_code;
pub use propagate::propagate_expressions;
pub use simplify::simplify_statements;
