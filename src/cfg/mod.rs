//! Control-flow graph structures.
//!
//! These mirror the `rewasm` layout but are trimmed down until stack/SSA plumbing lands.

use crate::ssa::Stmt;
use std::collections::HashSet;

mod builder;
pub use builder::{build_cfg_for_proc, CfgBuildError};

pub type NodeId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

impl Cfg {
    pub fn stmt(&self, pos: InstrPos) -> &Stmt {
        &self.nodes[pos.node].code[pos.instr]
    }

    pub fn stmt_mut(&mut self, pos: InstrPos) -> &mut Stmt {
        &mut self.nodes[pos.node].code[pos.instr]
    }

    pub fn succs(&self, node: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes[node].next.iter().map(|e| e.node)
    }

    /// Iterator over forward successors (excluding back edges).
    pub fn forward_succs(&self, node: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes[node].next.iter().filter_map(|e| if e.back_edge { None } else { Some(e.node) })
    }

    pub fn preds(&self, node: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes[node].prev.iter().map(|e| e.node)
    }

    /// Return successors that leave the given region of nodes.
    pub fn region_successors(&self, region_nodes: &HashSet<NodeId>) -> HashSet<NodeId> {
        let mut result = HashSet::new();
        for &n in region_nodes {
            for s in self.nodes[n].next.iter().map(|e| e.node) {
                if !region_nodes.contains(&s) {
                    result.insert(s);
                }
            }
        }
        result
    }

    /// Find all nodes between `head` and the `targets`, following only forward edges.
    pub fn graph_slice(&self, head: NodeId, targets: HashSet<NodeId>) -> HashSet<NodeId> {
        GraphSliceBuilder::dfs(self, head, targets)
    }
}

struct GraphSliceBuilder {
    targets: HashSet<NodeId>,
    visited: HashSet<NodeId>,
}

impl GraphSliceBuilder {
    fn dfs(cfg: &Cfg, head: NodeId, targets: HashSet<NodeId>) -> HashSet<NodeId> {
        let mut performer = GraphSliceBuilder { targets, visited: HashSet::new() };
        performer.visit(cfg, head);
        performer.targets
    }

    fn visit(&mut self, cfg: &Cfg, n: usize) -> bool {
        let mut inserted = self.targets.contains(&n);
        for u in cfg.forward_succs(n) {
            if !self.visited.insert(u) {
                if !inserted && self.targets.contains(&u) {
                    self.targets.insert(n);
                    inserted = true;
                }
                continue;
            }
            if self.visit(cfg, u) && !inserted {
                self.targets.insert(n);
                inserted = true;
            }
        }
        inserted
    }
}
