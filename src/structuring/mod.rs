//! Structuring passes: convert a CFG with low-level branches into structured Stmt forms.
//! Currently a conservative pass that stitches regions together and preserves branch markers;
//! it intentionally over-approximates compared to rewasm's full condition/loop refinement.

use std::collections::{HashMap, HashSet};

use crate::{
    cfg::{Cfg, Edge, EdgeCond, EdgeType, NodeId},
    dominance::{compute_dom_frontier, DomTree},
    ssa::{BinOp, Constant, Expr, Stmt, UnOp, Var},
};

mod rename_vars;
mod sidefx;
mod cond;
mod simplify;

/// Structure a CFG into a single sequence of statements.
pub fn structure(cfg: Cfg) -> Vec<Stmt> {
    if cfg.nodes.is_empty() {
        return Vec::new();
    }

    let mut cfg = cfg;
    let carriers = lower_loop_phis_with_cfg(&mut cfg);
    let expr_map = extract_branch_exprs(&mut cfg);
    let post_order = InitDfs::dfs(&cfg);
    let next_var = next_var_index(&cfg);
    let dom_tree = DomTree::build(&cfg);
    let dom_frontier = compute_dom_frontier(&cfg, &dom_tree);
    let mut structurer =
        Structurer { cfg, post_order, dom_tree, dom_frontier, expr_map, next_var, carriers };
    structurer.run()
}

struct Structurer {
    cfg: Cfg,
    post_order: Vec<usize>,
    dom_tree: DomTree,
    dom_frontier: Vec<Vec<usize>>,
    expr_map: HashMap<u32, Expr>,
    next_var: u32,
    carriers: HashSet<(Var, Var)>,
}

impl Structurer {
    fn fresh_var(&mut self) -> Var {
        let v = Var::no_sub(self.next_var);
        self.next_var += 1;
        v
    }

    fn run(&mut self) -> Vec<Stmt> {
        for i in 0..self.post_order.len() {
            let head = self.post_order[i];

            if self.cfg.nodes[head].prev.iter().any(|e| e.back_edge) {
                self.structure_loop(head, i);
            }

            let nodes = self.dom_tree.dominated_by(head);
            if nodes.len() == 1 {
                continue;
            }

            let region_succs = self.cfg.region_successors(&nodes);
            if region_succs.len() < 2 {
                self.structure_acyclic(head, i, &nodes);
                self.rewire_after_collapse(head, &nodes, region_succs);
            }
        }

        let mut out = if self.cfg.nodes.len() > 1 {
            let mut out = Vec::new();
            for bb in self.cfg.nodes.drain(..) {
                out.extend(bb.code);
            }
            out
        } else {
            self.cfg.nodes.remove(0).code
        };
        normalize_branches(&mut out);
        sidefx::prune_nops(&mut out);
        cond::refine(&mut out);
        hoist_shared_conditions(&mut out, &mut self.next_var);
        sidefx::prune_side_effects(&mut out);
        simplify::apply(&mut out);
        rename_vars::apply(&mut out, &self.carriers);
        out
    }

    fn structure_acyclic(&mut self, head: usize, i: usize, nodes: &HashSet<usize>) {
        let mut reaching_conds: HashMap<usize, Expr> = HashMap::new();
        reaching_conds.insert(head, Expr::True);
        let mut nodes_done = 1usize;

        for &n in self.post_order[..i].iter().rev() {
            if !nodes.contains(&n) {
                continue;
            }

            let mut cond: Option<Expr> = None;
            for edge in &self.cfg.nodes[n].prev {
                if !nodes.contains(&edge.node) {
                    continue;
                }
                let pred_cond = reaching_conds.get(&edge.node).cloned().unwrap_or(Expr::True);
                let edge_expr = edge_cond_expr(&edge.cond, &self.expr_map);
                let incoming =
                    Expr::BinOp(BinOp::And, Box::new(pred_cond), Box::new(edge_expr.clone()));
                cond = Some(match cond {
                    None => incoming,
                    Some(prev) => Expr::BinOp(BinOp::Or, Box::new(prev), Box::new(incoming)),
                });
            }

            let cond = cond.unwrap_or(Expr::True);
            reaching_conds.insert(n, cond.clone());

            let code = std::mem::take(&mut self.cfg.nodes[n].code);
            if !code.is_empty() {
                if matches!(cond, Expr::True) {
                    self.cfg.nodes[head].code.extend(code);
                } else {
                    self.cfg.nodes[head].code.push(Stmt::If {
                        cond: cond.clone(),
                        then_body: code,
                        else_body: Vec::new(),
                    });
                }
            }

            nodes_done += 1;
            if nodes_done == nodes.len() {
                break;
            }
        }

        cond::refine(&mut self.cfg.nodes[head].code);
    }

    fn structure_loop(&mut self, head: usize, i: usize) {
        let (nodes, succs) = self.find_loop_region(head);
        let mut exit_map: HashMap<usize, u32> = HashMap::new();
        for (idx, succ) in succs.iter().copied().enumerate() {
            exit_map.insert(succ, idx as u32);
        }
        let exit_var = if succs.len() > 1 { Some(self.fresh_var()) } else { None };
        self.insert_breaks(&nodes, exit_var.as_ref(), &exit_map, head);

        // Collapse dominated regions inside the loop where possible (acyclic subregions).
        if nodes.len() > 1 {
            for j in 0..i {
                let new_head = self.post_order[j];
                if !nodes.contains(&new_head) {
                    continue;
                }

                let mut new_nodes = self.dom_tree.dominated_by(new_head);
                new_nodes.retain(|n| nodes.contains(n));
                if new_nodes.len() == 1 {
                    continue;
                }

                let region_succs = self.cfg.region_successors(&new_nodes);
                if region_succs.len() < 2 {
                    self.structure_acyclic(new_head, j, &new_nodes);
                    self.rewire_after_collapse(new_head, &new_nodes, region_succs);
                }
            }

            let mut new_nodes = self.dom_tree.dominated_by(head);
            new_nodes.retain(|n| nodes.contains(n));
            if new_nodes.len() > 1 {
                let region_succs = self.cfg.region_successors(&new_nodes);
                if region_succs.len() < 2 {
                    self.structure_acyclic(head, i, &new_nodes);
                    self.rewire_after_collapse(head, &new_nodes, region_succs);
                }
            }
        }

        // Build loop body from head + dominated nodes within the loop.
        let mut body_nodes: Vec<_> = self.post_order[..=i]
            .iter()
            .copied()
            .filter(|n| nodes.contains(n) && *n != head)
            .collect();
        body_nodes.sort();

        let mut body_code = std::mem::take(&mut self.cfg.nodes[head].code);
        for n in body_nodes.into_iter().rev() {
            body_code.extend(std::mem::take(&mut self.cfg.nodes[n].code));
        }

        let cond = self.expr_map.get(&(head as u32)).cloned().unwrap_or(Expr::True);
        let mut new_code = Vec::new();
        if let Some(exit_var) = exit_var {
            let default_idx = self
                .cfg
                .nodes[head]
                .next
                .iter()
                .find(|e| !e.back_edge && !nodes.contains(&e.node))
                .and_then(|e| exit_map.get(&e.node).copied())
                .unwrap_or(0);
            new_code.push(Stmt::Assign {
                dst: exit_var,
                expr: Expr::Constant(Constant::Felt(default_idx as u64)),
            });
        }
        new_code.push(Stmt::While { cond, body: body_code });

        if let Some(exit_var) = exit_var {
            let mut dispatch = self.build_exit_dispatch(exit_var, &succs);
            new_code.append(&mut dispatch);
        }

        self.cfg.nodes[head].code = new_code;

        // Remove edges to successors outside the loop to avoid reprocessing.
        self.cfg.nodes[head].next.retain(|e| nodes.contains(&e.node) || succs.contains(&e.node));
    }

    fn build_exit_dispatch(&mut self, exit_var: Var, succs: &HashSet<usize>) -> Vec<Stmt> {
        let mut succs_sorted: Vec<_> = succs.iter().copied().collect();
        succs_sorted.sort();

        let mut branches: Vec<(u32, Vec<Stmt>)> = Vec::new();
        for (idx, succ) in succs_sorted.iter().copied().enumerate() {
            let region = self.dom_tree.dominated_by(succ);
            let mut code = Vec::new();
            for &n in self.post_order.iter().rev() {
                if !region.contains(&n) {
                    continue;
                }
                code.extend(std::mem::take(&mut self.cfg.nodes[n].code));
            }
            branches.push((idx as u32, code));
        }

        if branches.is_empty() {
            return Vec::new();
        }

        let cases: Vec<(Constant, Vec<Stmt>)> = branches
            .into_iter()
            .map(|(idx, code)| (Constant::Felt(idx as u64), code))
            .collect();

        vec![Stmt::Switch { expr: Expr::Var(exit_var), cases, default: Vec::new() }]
    }

    fn find_loop_region(&self, head: usize) -> (HashSet<usize>, HashSet<usize>) {
        let latch_nodes: HashSet<_> = self.cfg.nodes[head]
            .prev
            .iter()
            .filter(|e| e.back_edge)
            .map(|e| e.node)
            .collect();
        let mut loop_nodes = self.cfg.graph_slice(head, latch_nodes);
        loop_nodes.insert(head);

        let mut loop_succs: HashSet<usize> = self.cfg.region_successors(&loop_nodes);
        if let Some(df) = self.dom_frontier.get(head) {
            loop_succs.extend(df.iter().copied());
        }

        while loop_succs.len() > 1 {
            let mut added_any = false;
            let mut new_succs = HashSet::new();
            for succ in loop_succs.clone() {
                if self.cfg.nodes[succ].prev.iter().all(|e| loop_nodes.contains(&e.node)) {
                    loop_nodes.insert(succ);
                    added_any = true;
                    for s in self.cfg.nodes[succ].next.iter().map(|e| e.node) {
                        if !loop_nodes.contains(&s) {
                            new_succs.insert(s);
                        }
                    }
                }
            }
            if !added_any {
                break;
            }
            loop_succs = new_succs;
            if let Some(df) = self.dom_frontier.get(head) {
                loop_succs.extend(df.iter().copied());
            }
        }

        loop_succs.retain(|s| !loop_nodes.contains(s));
        (loop_nodes, loop_succs)
    }

    fn insert_breaks(
        &mut self,
        nodes: &HashSet<usize>,
        exit_var: Option<&Var>,
        exit_map: &HashMap<usize, u32>,
        head: usize,
    ) {
        for &n in nodes {
            let mut code = std::mem::take(&mut self.cfg.nodes[n].code);
            let mut new_edges = Vec::new();
            for edge in self.cfg.nodes[n].next.clone() {
                if nodes.contains(&edge.node) && edge.node != head {
                    new_edges.push(edge);
                    continue;
                }
                let cond_expr = edge_cond_expr(&edge.cond, &self.expr_map);
                if edge.node == head {
                    // Continue to next iteration.
                    if matches!(edge.cond.edge_type, EdgeType::Unconditional) {
                        code.push(Stmt::Continue);
                    } else {
                        code.push(Stmt::If {
                            cond: cond_expr,
                            then_body: vec![Stmt::Continue],
                            else_body: Vec::new(),
                        });
                    }
                    continue;
                }
                let mut break_stmts = Vec::new();
                if let Some(var) = exit_var {
                    if let Some(idx) = exit_map.get(&edge.node) {
                        break_stmts.push(Stmt::Assign {
                            dst: *var,
                            expr: Expr::Constant(Constant::Felt(*idx as u64)),
                        });
                    }
                }
                break_stmts.push(Stmt::Break);
                if matches!(edge.cond.edge_type, EdgeType::Unconditional) {
                    code.extend(break_stmts);
                } else {
                    code.push(Stmt::If { cond: cond_expr, then_body: break_stmts, else_body: Vec::new() });
                }
            }
            self.cfg.nodes[n].next = new_edges;
            self.cfg.nodes[n].code = code;
        }
    }

    fn rewire_after_collapse(
        &mut self,
        head: usize,
        nodes: &HashSet<usize>,
        mut region_succs: HashSet<usize>,
    ) {
        self.dom_tree.remove(head, nodes);
        self.cfg.nodes[head].next.clear();

        if let Some(succ) = region_succs.drain().next() {
            let back_edge = self.cfg.nodes[succ]
                .prev
                .iter()
                .any(|edge| edge.back_edge && nodes.contains(&edge.node));

            self.cfg.nodes[succ].prev.retain(|e| !nodes.contains(&e.node));
            self.cfg.nodes[succ].prev.push(Edge {
                cond: EdgeCond::unconditional(),
                node: head,
                back_edge,
            });

            self.cfg.nodes[head].next.push(Edge {
                cond: EdgeCond::unconditional(),
                node: succ,
                back_edge,
            });
        }
    }
}

fn extract_branch_exprs(cfg: &mut Cfg) -> HashMap<u32, Expr> {
    let mut map = HashMap::new();
    for idx in 0..cfg.nodes.len() {
        if let Some(Stmt::Branch(expr)) = cfg.nodes[idx].code.last().cloned() {
            cfg.nodes[idx].code.pop();
            // Assign this expr to all outgoing conditional edges from this block.
            for edge in &cfg.nodes[idx].next {
                if matches!(edge.cond.edge_type, EdgeType::Conditional(_)) {
                    map.insert(edge.cond.expr_index, expr.clone());
                }
            }
        }
    }
    map
}

fn edge_cond_expr(cond: &EdgeCond, expr_map: &HashMap<u32, Expr>) -> Expr {
    match cond.edge_type {
        EdgeType::Unconditional => Expr::True,
        EdgeType::Conditional(expect_true) => {
            let base = expr_map.get(&cond.expr_index).cloned().unwrap_or(Expr::Unknown);
            if expect_true {
                base
            } else {
                Expr::Unary(UnOp::Not, Box::new(base))
            }
        }
    }
}

struct InitDfs {
    post_order: Vec<usize>,
    visited: HashSet<usize>,
}

impl InitDfs {
    fn dfs(cfg: &Cfg) -> Vec<usize> {
        if cfg.nodes.is_empty() {
            return Vec::new();
        }
        let mut performer =
            InitDfs { post_order: Vec::with_capacity(cfg.nodes.len()), visited: HashSet::new() };
        performer.visited.insert(0);
        performer.visit(cfg, 0);
        performer.post_order
    }

    fn visit(&mut self, cfg: &Cfg, n: usize) {
        for u in cfg.succs(n) {
            if self.visited.insert(u) {
                self.visit(cfg, u);
            }
        }
        self.post_order.push(n);
    }
}

fn next_var_index(cfg: &Cfg) -> u32 {
    let mut max = 0u32;
    for bb in &cfg.nodes {
        for stmt in &bb.code {
            scan_stmt(stmt, &mut max);
        }
    }
    max.saturating_add(1)
}

fn scan_stmt(stmt: &Stmt, max: &mut u32) {
        match stmt {
            Stmt::Assign { dst, expr } => {
                *max = (*max).max(dst.index);
                scan_expr(expr, max);
            }
        Stmt::Expr(expr) | Stmt::Branch(expr) => scan_expr(expr, max),
        Stmt::StackOp(op) => {
            for v in op.pops.iter().chain(op.pushes.iter()) {
                *max = (*max).max(v.index);
            }
        }
        Stmt::Phi { var, sources } => {
            *max = (*max).max(var.index);
            for s in sources {
                *max = (*max).max(s.index);
            }
        }
        Stmt::If { cond, then_body, else_body } => {
            scan_expr(cond, max);
            for s in then_body.iter().chain(else_body.iter()) {
                scan_stmt(s, max);
            }
        }
        Stmt::Switch { expr, cases, default } => {
            scan_expr(expr, max);
            for (_, body) in cases {
                for s in body {
                    scan_stmt(s, max);
                }
            }
            for s in default {
                scan_stmt(s, max);
            }
        }
        Stmt::While { cond, body } => {
            scan_expr(cond, max);
            for s in body {
                scan_stmt(s, max);
            }
        }
        Stmt::Instr(_) | Stmt::Unknown | Stmt::Nop | Stmt::Break | Stmt::Continue => {}
    }
}

fn scan_expr(expr: &Expr, max: &mut u32) {
    match expr {
        Expr::Var(v) => *max = (*max).max(v.index),
        Expr::BinOp(_, a, b) => {
            scan_expr(a, max);
            scan_expr(b, max);
        }
        Expr::Unary(_, a) => scan_expr(a, max),
        Expr::Constant(_) | Expr::True | Expr::Unknown => {}
    }
}

/// Hoist side-effect-free conditions used multiple times into temporaries.
fn hoist_shared_conditions(code: &mut Vec<Stmt>, next_var: &mut u32) {
    let mut counts: HashMap<String, (Expr, bool, u32)> = HashMap::new();
    collect_conds(code, &mut counts);

    // Map from base expr key to allocated var.
    let mut base_vars: HashMap<String, Var> = HashMap::new();
    let mut replacements: HashMap<String, Expr> = HashMap::new();
    let mut hoisted_assigns = Vec::new();

    for (key, (base, neg, count)) in counts {
        if count < 2 {
            continue;
        }
        if matches!(base, Expr::Var(_) | Expr::Constant(_) | Expr::True) {
            continue;
        }
        let base_key = format!("{:?}", base);
        let var = *base_vars.entry(base_key.clone()).or_insert_with(|| {
            let v = Var::no_sub(*next_var);
            *next_var += 1;
            hoisted_assigns.push(Stmt::Assign { dst: v, expr: base.clone() });
            v
        });
        let expr = if neg { Expr::Unary(UnOp::Not, Box::new(Expr::Var(var))) } else { Expr::Var(var) };
        replacements.insert(key, expr);
    }

    if hoisted_assigns.is_empty() {
        return;
    }

    apply_replacements(code, &replacements);
    hoisted_assigns.append(code);
    *code = hoisted_assigns;
}

fn collect_conds(code: &[Stmt], counts: &mut HashMap<String, (Expr, bool, u32)>) {
    for stmt in code {
        match stmt {
            Stmt::If { cond, then_body, else_body } => {
                bump_cond(cond, counts);
                collect_conds(then_body, counts);
                collect_conds(else_body, counts);
            }
            Stmt::Switch { expr, cases, default } => {
                bump_cond(expr, counts);
                for (_, body) in cases {
                    collect_conds(body, counts);
                }
                collect_conds(default, counts);
            }
            Stmt::While { cond, body } => {
                bump_cond(cond, counts);
                collect_conds(body, counts);
            }
            _ => {}
        }
    }
}

fn bump_cond(expr: &Expr, counts: &mut HashMap<String, (Expr, bool, u32)>) {
    if let Some((base, neg)) = base_cond(expr) {
        let key = format!("{:?}|{}", base, neg);
        let entry = counts.entry(key).or_insert_with(|| (base, neg, 0));
        entry.2 += 1;
    }
}

fn base_cond(expr: &Expr) -> Option<(Expr, bool)> {
    match expr {
        Expr::Unary(UnOp::Not, inner) => {
            let (base, neg) = base_cond(inner)?;
            Some((base, !neg))
        }
        Expr::Unknown => None,
        _ => Some((expr.clone(), false)),
    }
}

fn apply_replacements(code: &mut [Stmt], replacements: &HashMap<String, Expr>) {
    for stmt in code {
        match stmt {
            Stmt::If { cond, then_body, else_body } => {
                replace_cond_expr(cond, replacements);
                apply_replacements(then_body, replacements);
                apply_replacements(else_body, replacements);
            }
            Stmt::Switch { expr, cases, default } => {
                replace_cond_expr(expr, replacements);
                for (_, body) in cases {
                    apply_replacements(body, replacements);
                }
                apply_replacements(default, replacements);
            }
            Stmt::While { cond, body } => {
                replace_cond_expr(cond, replacements);
                apply_replacements(body, replacements);
            }
            _ => {}
        }
    }
}

fn replace_cond_expr(expr: &mut Expr, replacements: &HashMap<String, Expr>) {
    if let Some((base, neg)) = base_cond(expr) {
        let key = format!("{:?}|{}", base, neg);
        if let Some(rep) = replacements.get(&key) {
            *expr = rep.clone();
            return;
        }
    }
    match expr {
        Expr::Unary(_, inner) => replace_cond_expr(inner, replacements),
        Expr::BinOp(_, a, b) => {
            replace_cond_expr(a, replacements);
            replace_cond_expr(b, replacements);
        }
        _ => {}
    }
}

/// Lower loop-header phis while CFG information is still available by mapping sources to
/// preheader/back-edge predecessors and inserting explicit init/update assignments.
fn lower_loop_phis_with_cfg(cfg: &mut Cfg) -> HashSet<(Var, Var)> {
    let mut carrier_pairs = HashSet::new();
    // Collect definitions per block to help map vars to predecessor blocks.
    let mut block_defs: Vec<HashSet<Var>> = Vec::with_capacity(cfg.nodes.len());
    for bb in &cfg.nodes {
        block_defs.push(collect_defs_shallow(&bb.code));
    }

    // Accumulate updates to insert at the end of predecessor blocks.
    let mut pending_updates: HashMap<NodeId, Vec<Stmt>> = HashMap::new();

    for head in 0..cfg.nodes.len() {
        let preds = cfg.nodes[head].prev.clone();
        if preds.is_empty() {
            continue;
        }
        let has_backedge = preds.iter().any(|e| e.back_edge);
        if !has_backedge {
            continue;
        }

        let mut init_stmts: Vec<Stmt> = Vec::new();
        let mut new_code: Vec<Stmt> = Vec::new();

        for stmt in std::mem::take(&mut cfg.nodes[head].code) {
            if let Stmt::Phi { var, sources } = stmt {
                if sources.len() < 2 {
                    // Not a real merge; drop it.
                    continue;
                }
                // Try to map sources to preds.
                let mut init_src: Option<Var> = None;
                let mut update_src: Option<(Var, NodeId)> = None;

                for src in sources.iter().copied() {
                    // Heuristic: pick the first non-back-edge pred that defines the var as init.
                    for p in preds.iter() {
                        let p_node = p.node;
                        let is_back = p.back_edge;
                        if block_defs.get(p_node).map_or(false, |defs| defs.contains(&src)) {
                            if is_back {
                                if update_src.is_none() {
                                    update_src = Some((src, p_node));
                                }
                            } else if init_src.is_none() {
                                init_src = Some(src);
                            }
                        }
                    }
                    // If still missing init, fall back to any non-backedge pred even without def.
                    if init_src.is_none() {
                        if let Some(p) = preds.iter().find(|e| !e.back_edge) {
                            init_src = Some(src);
                            let _ = p;
                        }
                    }
                    // If still missing update, fall back to any back-edge pred.
                    if update_src.is_none() {
                        if let Some(p) = preds.iter().find(|e| e.back_edge) {
                            update_src = Some((src, p.node));
                        }
                    }
                }

                if let (Some(init), Some((upd, upd_pred))) = (init_src, update_src) {
                    init_stmts.push(Stmt::Assign { dst: var, expr: Expr::Var(init) });
                    carrier_pairs.insert((var, init));
                    pending_updates
                        .entry(upd_pred)
                        .or_default()
                        .push(Stmt::Assign { dst: var, expr: Expr::Var(upd) });
                    carrier_pairs.insert((var, upd));
                    continue;
                }

                // Ambiguous; keep phi.
                new_code.push(Stmt::Phi { var, sources });
            } else {
                new_code.push(stmt);
            }
        }

        // Prepend inits to the head block.
        if !init_stmts.is_empty() {
            let mut combined = init_stmts;
            combined.extend(new_code.into_iter());
            cfg.nodes[head].code = combined;
        } else {
            cfg.nodes[head].code = new_code;
        }
    }

    // Append updates to predecessor blocks.
    for (pred, mut stmts) in pending_updates {
        cfg.nodes[pred].code.append(&mut stmts);
    }

    carrier_pairs
}

fn collect_defs_shallow(body: &[Stmt]) -> HashSet<Var> {
    let mut defs = HashSet::new();
    for stmt in body {
        match stmt {
            Stmt::Assign { dst, .. } => {
                defs.insert(*dst);
            }
            Stmt::StackOp(op) => {
                defs.extend(op.pushes.iter().copied());
            }
            Stmt::Phi { var, .. } => {
                defs.insert(*var);
            }
            Stmt::If { then_body, else_body, .. } => {
                defs.extend(collect_defs_shallow(then_body));
                defs.extend(collect_defs_shallow(else_body));
            }
            Stmt::Switch { cases, default, .. } => {
                for (_, body) in cases {
                    defs.extend(collect_defs_shallow(body));
                }
                defs.extend(collect_defs_shallow(default));
            }
            // Do not descend into nested loops; treat them as opaque for the outer loop's defs.
            Stmt::While { .. } => {}
            _ => {}
        }
    }
    defs
}


fn normalize_branches(code: &mut Vec<Stmt>) {
    for stmt in code.iter_mut() {
        match stmt {
            Stmt::Branch(expr) => {
                *stmt = Stmt::If { cond: expr.clone(), then_body: Vec::new(), else_body: Vec::new() };
            }
            Stmt::If { then_body, else_body, .. } => {
                normalize_branches(then_body);
                normalize_branches(else_body);
            }
            Stmt::While { body, .. } => {
                normalize_branches(body);
            }
            _ => {}
        }
    }
}
