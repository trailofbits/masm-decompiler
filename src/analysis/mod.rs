//! Analysis passes (expression propagation, DCE, etc.).

mod dead_code_elimination;
mod expression_propagation;
mod loop_indices;
mod used_vars;

pub use dead_code_elimination::eliminate_dead_code;
pub use expression_propagation::propagate_expressions;
pub use loop_indices::compute_loop_indices;
pub use used_vars::{DefUseMap, DefinesVars, UsesVars, build_def_use_map};
