//! Control-flow graph structures.
//!
//! These mirror the `rewasm` layout but are trimmed down until stack/SSA plumbing lands.

use crate::ssa::{Stmt, VarArena};
use std::collections::{HashMap, HashSet};

mod builder;
pub use builder::{CfgError, build_cfg_for_proc};

pub type NodeId = usize;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StmtPos {
    pub node: NodeId,
    pub instr: usize,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Edge {
    /// An unconditional edge from the source to `node`.
    Unconditional {
        /// Target node ID.
        node: NodeId,
        /// True when this edge points back to a loop header.
        back_edge: bool,
    },
    /// A conditional edge from the source to `node`.
    Conditional {
        /// Target node ID.
        node: NodeId,
        /// True when this edge points back to a loop header.
        back_edge: bool,
        /// True if this edge is taken when the condition evaluates to true.
        true_branch: bool,
    },
}

impl Edge {
    pub fn node(&self) -> NodeId {
        match self {
            Edge::Unconditional { node, .. } => *node,
            Edge::Conditional { node, .. } => *node,
        }
    }

    pub fn back_edge(&self) -> bool {
        match self {
            Edge::Unconditional { back_edge, .. } => *back_edge,
            Edge::Conditional { back_edge, .. } => *back_edge,
        }
    }

    pub fn true_branch(&self) -> Option<bool> {
        if let Edge::Conditional { true_branch, .. } = self {
            Some(*true_branch)
        } else {
            None
        }
    }
}

#[derive(Debug, Default)]
pub struct BasicBlock {
    pub code: Vec<Stmt>,
    pub next: Vec<Edge>,
    pub prev: Vec<Edge>,
}

/// Context information for a repeat loop, used for subscript computation.
#[derive(Debug, Clone)]
pub struct LoopContext {
    /// Index of the loop counter variable.
    pub loop_var_index: usize,
    /// Stack depth at loop entry (before any iterations).
    pub entry_depth: usize,
    /// Net stack effect per iteration (positive = producing, negative = consuming).
    pub effect_per_iter: isize,
    /// Total number of iterations.
    pub iter_count: usize,
}

#[derive(Debug, Default)]
pub struct Cfg {
    pub nodes: Vec<BasicBlock>,
    pub arena: VarArena,
    /// Maps variable index to its birth depth (stack depth when created).
    pub var_depths: HashMap<usize, usize>,
    /// Loop contexts for subscript computation, keyed by loop header node ID.
    pub loop_contexts: HashMap<NodeId, LoopContext>,
}

impl Cfg {
    pub fn stmt(&self, pos: StmtPos) -> &Stmt {
        &self.nodes[pos.node].code[pos.instr]
    }

    pub fn stmt_mut(&mut self, pos: StmtPos) -> &mut Stmt {
        &mut self.nodes[pos.node].code[pos.instr]
    }

    /// Iterator over the nodes successors.
    pub fn successors(&self, node: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes[node].next.iter().map(|e| e.node())
    }

    /// Iterator over the nodes forward successors (excluding back edges).
    pub fn forward_successors(&self, node: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes[node]
            .next
            .iter()
            .filter_map(|e| if e.back_edge() { None } else { Some(e.node()) })
    }

    /// Iterator over the nodes predecessors.
    pub fn predecessors(&self, node: NodeId) -> impl Iterator<Item = NodeId> + '_ {
        self.nodes[node].prev.iter().map(|e| e.node())
    }

    /// Return successors that leave the given region of nodes.
    pub fn region_successors(&self, region_nodes: &HashSet<NodeId>) -> HashSet<NodeId> {
        let mut result = HashSet::new();
        for &n in region_nodes {
            for s in self.successors(n) {
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
        let mut builder = GraphSliceBuilder {
            targets,
            visited: HashSet::new(),
        };
        builder.visit(cfg, head);
        builder.targets
    }

    fn visit(&mut self, cfg: &Cfg, n: usize) -> bool {
        let mut inserted = self.targets.contains(&n);
        for s in cfg.forward_successors(n) {
            if !self.visited.insert(s) {
                if !inserted && self.targets.contains(&s) {
                    self.targets.insert(n);
                    inserted = true;
                }
                continue;
            }
            if self.visit(cfg, s) && !inserted {
                self.targets.insert(n);
                inserted = true;
            }
        }
        inserted
    }
}
