//! IR simplification passes (dead code elimination, expression propagation, etc.).

pub mod eliminate;
pub mod propagate_copies;
pub mod propagate_exprs;
pub mod shorten_call_targets;
pub mod simplify;
pub mod used_vars;

pub use eliminate::eliminate_dead_code;
pub use propagate_copies::propagate_copies;
pub use propagate_exprs::propagate_expressions;
pub use shorten_call_targets::shorten_call_targets;
pub use simplify::simplify_statements;
