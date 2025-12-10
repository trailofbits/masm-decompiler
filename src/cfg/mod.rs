//! Control-flow graph structures.
//!
//! These mirror the `rewasm` layout but are trimmed down until stack/SSA plumbing lands.

use crate::ssa::Stmt;

pub type NodeId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstrPos {
    pub node: NodeId,
    pub instr: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EdgeType {
    Unconditional,
    Conditional(bool),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct EdgeCond {
    pub expr_index: u32,
    pub edge_type: EdgeType,
}

impl EdgeCond {
    pub const fn unconditional() -> Self {
        Self {
            expr_index: 0,
            edge_type: EdgeType::Unconditional,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Edge {
    pub cond: EdgeCond,
    pub node: NodeId,
    pub back_edge: bool,
}

#[derive(Debug, Default)]
pub struct BasicBlock {
    pub code: Vec<Stmt>,
    pub next: Vec<Edge>,
    pub prev: Vec<Edge>,
}

/// Skeleton CFG used until the builder/structuring passes are in place.
#[derive(Debug, Default)]
pub struct Cfg {
    pub nodes: Vec<BasicBlock>,
}
