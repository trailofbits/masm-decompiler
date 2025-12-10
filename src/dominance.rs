use std::collections::HashSet;

use crate::cfg::{Cfg, NodeId};

/// Immediate-dominator tree.
pub struct DomTree {
    pub idom: Vec<usize>,
    pub succs: Vec<Vec<usize>>,
}

impl DomTree {
    /// Find all nodes dominated by `n` (including `n`).
    pub fn dominated_by(&self, n: usize) -> HashSet<usize> {
        let mut result = HashSet::new();
        let mut todo = vec![n];
        while let Some(u) = todo.pop() {
            if result.insert(u) {
                for &s in &self.succs[u] {
                    todo.push(s);
                }
            }
        }
        result
    }

    pub fn dominates_strictly(&self, n: usize, mut w: usize) -> bool {
        if n == 0 {
            return w != 0;
        }
        while w != 0 {
            w = self.idom[w];
            if n == w {
                return true;
            }
        }
        false
    }

    pub fn remove(&mut self, head: usize, nodes: &HashSet<usize>) {
        self.succs[head] = self.find_nodes_to_keep(head, nodes);
        for &succ in &self.succs[head] {
            self.idom[succ] = head;
        }
    }

    fn find_nodes_to_keep(&self, head: usize, nodes: &HashSet<usize>) -> Vec<usize> {
        if !nodes.contains(&head) {
            return vec![head];
        }
        let mut keep = Vec::new();
        for &succ in &self.succs[head] {
            keep.extend(self.find_nodes_to_keep(succ, nodes));
        }
        keep
    }

    pub fn build(cfg: &Cfg) -> Self {
        DomTreeBuilder::new(cfg).build()
    }
}

struct DomTreeBuilder<'a> {
    cfg: &'a Cfg,
    rev_edges: Vec<Vec<usize>>,
    bucket: Vec<Vec<usize>>,
    index: Vec<usize>,
    rev_index: Vec<usize>,
    parent: Vec<usize>,
    idom: Vec<usize>,
    sdom: Vec<usize>,
    dsu: Vec<usize>,
    label: Vec<usize>,
    next_index: usize,
}

impl<'a> DomTreeBuilder<'a> {
    fn new(cfg: &'a Cfg) -> Self {
        let n = cfg.nodes.len().max(1);
        Self {
            cfg,
            rev_edges: vec![Vec::new(); n],
            bucket: vec![Vec::new(); n],
            index: vec![0; n],
            rev_index: vec![0; n],
            parent: vec![0; n],
            idom: vec![0; n],
            sdom: vec![0; n],
            dsu: vec![0; n],
            label: vec![0; n],
            next_index: 0,
        }
    }

    fn initial_dfs(&mut self, u: usize) {
        let idx = self.next_index;
        self.next_index += 1;
        self.index[u] = idx;
        self.rev_index[idx] = u;
        self.idom[idx] = idx;
        self.sdom[idx] = idx;
        self.dsu[idx] = idx;
        self.label[idx] = idx;

        for w in self.cfg.succs(u) {
            let w = w as usize;
            if self.index[w] == 0 && w != 0 {
                self.initial_dfs(w);
                self.parent[self.index[w]] = idx;
            }
            self.rev_edges[self.index[w]].push(idx);
        }
    }

    fn find(&mut self, u: usize) -> usize {
        self.find_internal(u, 0).unwrap_or(u)
    }

    fn find_internal(&mut self, u: usize, depth: usize) -> Option<usize> {
        if u >= self.dsu.len() {
            return None;
        }
        if u == self.dsu[u] {
            return if depth == 0 { Some(u) } else { None };
        }

        let parent = self.dsu[u];
        let v = self.find_internal(parent, depth + 1)?;
        if self.sdom[self.label[parent]] < self.sdom[self.label[u]] {
            self.label[u] = self.label[parent];
        }
        self.dsu[u] = v;
        Some(if depth == 0 { self.label[u] } else { v })
    }

    fn build(mut self) -> DomTree {
        if self.cfg.nodes.is_empty() {
            return DomTree { idom: Vec::new(), succs: Vec::new() };
        }

        self.initial_dfs(0);

        for i in (0..self.cfg.nodes.len()).rev() {
            let preds: Vec<_> = self.rev_edges[i].clone();
            for pred in preds {
                let v = self.find(pred);
                let x = self.sdom[v];
                if x < self.sdom[i] {
                    self.sdom[i] = x;
                }
            }

            if i > 0 {
                self.bucket[self.sdom[i]].push(i);
            }

            let bucket = self.bucket[i].clone();
            for w in bucket {
                let v = self.find(w);
                if self.sdom[v] == self.sdom[w] {
                    self.idom[w] = self.sdom[w];
                } else {
                    self.idom[w] = v;
                }
            }

            if i > 0 {
                self.dsu[i] = self.parent[i];
            }
        }

        let mut dom_tree = vec![Vec::new(); self.cfg.nodes.len()];
        for i in 1..self.cfg.nodes.len() {
            if self.idom[i] != self.sdom[i] {
                self.idom[i] = self.idom[self.idom[i]];
            }
            dom_tree[self.rev_index[self.idom[i]]].push(self.rev_index[i]);
        }

        let mut idom = vec![0; self.idom.len()];
        for (i, dom) in self.idom.iter().enumerate() {
            idom[self.rev_index[i]] = self.rev_index[*dom];
        }
        if !idom.is_empty() {
            idom[0] = std::usize::MAX;
        }

        DomTree { idom, succs: dom_tree }
    }
}

struct DomFrontierBuilder<'a> {
    cfg: &'a Cfg,
    dom_tree: &'a DomTree,
    df: Vec<Vec<NodeId>>,
}

impl<'a> DomFrontierBuilder<'a> {
    fn new(cfg: &'a Cfg, dom_tree: &'a DomTree) -> Self {
        let n = cfg.nodes.len();
        Self { cfg, dom_tree, df: vec![Vec::new(); n] }
    }

    fn compute_df(&mut self, n: NodeId) {
        for succ in self.cfg.succs(n) {
            if self.dom_tree.idom[succ] != n {
                self.df[n].push(succ);
            }
        }

        for &dom_succ in &self.dom_tree.succs[n] {
            self.compute_df(dom_succ);
            let succ_df = self.df[dom_succ].clone();
            for w in succ_df {
                if !self.dom_tree.dominates_strictly(n, w) {
                    self.df[n].push(w);
                }
            }
        }
    }

    fn build(mut self) -> Vec<Vec<NodeId>> {
        if self.cfg.nodes.is_empty() {
            return Vec::new();
        }
        self.compute_df(0);
        self.df
    }
}

pub fn compute_dom_frontier(cfg: &Cfg, dom_tree: &DomTree) -> Vec<Vec<NodeId>> {
    DomFrontierBuilder::new(cfg, dom_tree).build()
}
