//! SSA IR skeleton.
//!
//! This keeps the crate layout aligned with `rewasm` while inference/SSA lowering is implemented.

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Var {
    pub index: u32,
    pub subscript: u32,
}

impl Var {
    pub const fn new(index: u32, subscript: u32) -> Self {
        Self { index, subscript }
    }

    pub const fn no_sub(index: u32) -> Self {
        Self { index, subscript: 0 }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    True,
    Var(Var),
    UnknownExec,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Stmt {
    Expr(Expr),
    Nop,
}
