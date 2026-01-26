//! Structuring passes: convert a CFG with low-level branches into structured Stmt forms.
//! Currently a conservative pass that stitches regions together and preserves branch markers;
//! it intentionally over-approximates compared to rewasm's full condition/loop refinement.

use std::collections::{HashMap, HashSet};

use crate::{
    analysis::compute_loop_indices,
    cfg::{Cfg, Edge, NodeId},
    dominance::DomTree,
    ssa::{BinOp, Constant, Expr, IndexExpr, Stmt, Subscript, UnOp, Var},
};

mod cond;
mod rename_vars;
mod side_effects;
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
    let mut structurer = Structurer {
        cfg,
        post_order,
        dom_tree,
        expr_map,
        next_var,
        carriers,
    };
    structurer.run()
}

struct Structurer {
    cfg: Cfg,
    post_order: Vec<usize>,
    dom_tree: DomTree,
    expr_map: HashMap<usize, Expr>,
    next_var: usize,
    carriers: HashSet<(Var, Var)>,
}

impl Structurer {
    fn fresh_var(&mut self) -> Var {
        let v = Var::new(self.next_var);
        self.next_var += 1;
        v
    }

    fn run(&mut self) -> Vec<Stmt> {
        for i in 0..self.post_order.len() {
            let head = self.post_order[i];

            if self.cfg.nodes[head].prev.iter().any(|e| e.back_edge()) {
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
        side_effects::prune_nops(&mut out);
        cond::refine(&mut out);
        hoist_shared_conditions(&mut out, &mut self.next_var);
        side_effects::prune_side_effects(&mut out);
        simplify::apply(&mut out);
        rewrite_repeat_loops(&mut out);
        rename_vars::apply(&mut out, &self.carriers);
        simplify::apply(&mut out);
        apply_loop_subscripts(&mut out);
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
                if !nodes.contains(&edge.node()) {
                    continue;
                }
                let pred_cond = reaching_conds
                    .get(&edge.node())
                    .cloned()
                    .unwrap_or(Expr::True);
                let edge_expr = edge_cond_expr(edge, edge.node(), &self.expr_map);
                let incoming =
                    Expr::Binary(BinOp::And, Box::new(pred_cond), Box::new(edge_expr.clone()));
                cond = Some(match cond {
                    None => incoming,
                    Some(prev) => Expr::Binary(BinOp::Or, Box::new(prev), Box::new(incoming)),
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
        if std::env::var("DEBUG_LOOP").is_ok() {
            eprintln!(
                "structure_loop start head {} initial edges {:?}",
                head, self.cfg.nodes[head].next
            );
        }
        let mut exit_map: HashMap<usize, usize> = HashMap::new();
        for (idx, succ) in succs.iter().copied().enumerate() {
            exit_map.insert(succ, idx);
        }
        let exit_var = if succs.len() > 1 {
            Some(self.fresh_var())
        } else {
            None
        };
        self.insert_breaks(&nodes, exit_var.as_ref(), &exit_map, head);

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

        if std::env::var("DEBUG_LOOP").is_ok() {
            eprintln!(
                "loop head {} nodes {:?} edges {:?}",
                head, nodes, self.cfg.nodes[head].next
            );
        }
        let cond = self.cfg.nodes[head]
            .next
            .iter()
            .find_map(|edge| match edge {
                Edge::Conditional {
                    true_branch: true, ..
                } => Some(edge_cond_expr(edge, head, &self.expr_map)),
                _ => None,
            })
            .unwrap_or(Expr::True);
        if std::env::var("DEBUG_LOOP").is_ok() {
            eprintln!(
                "structure_loop head {} cond {:?} expr_map {:?}",
                head, cond, self.expr_map
            );
        }
        let mut new_code = Vec::new();
        if let Some(exit_var) = exit_var.as_ref() {
            let default_idx = self.cfg.nodes[head]
                .next
                .iter()
                .find(|e| !e.back_edge() && !nodes.contains(&e.node()))
                .and_then(|e| exit_map.get(&e.node()).copied())
                .unwrap_or(0);
            new_code.push(Stmt::Assign {
                dest: exit_var.clone(),
                expr: Expr::Constant(Constant::Felt(default_idx as u64)),
            });
        }
        new_code.push(Stmt::While {
            cond,
            body: body_code,
        });

        if let Some(exit_var) = exit_var {
            let mut dispatch = self.build_exit_dispatch(exit_var, &succs);
            new_code.append(&mut dispatch);
        }

        self.cfg.nodes[head].code = new_code;

        // Remove edges to successors outside the loop to avoid reprocessing.
        self.cfg.nodes[head]
            .next
            .retain(|e| nodes.contains(&e.node()) || succs.contains(&e.node()));
    }

    fn build_exit_dispatch(&mut self, exit_var: Var, succs: &HashSet<usize>) -> Vec<Stmt> {
        let mut succs_sorted: Vec<_> = succs.iter().copied().collect();
        succs_sorted.sort();

        let mut branches: Vec<(usize, Vec<Stmt>)> = Vec::new();
        for (idx, succ) in succs_sorted.iter().copied().enumerate() {
            let region = self.dom_tree.dominated_by(succ);
            let mut code = Vec::new();
            for &n in self.post_order.iter().rev() {
                if !region.contains(&n) {
                    continue;
                }
                code.extend(std::mem::take(&mut self.cfg.nodes[n].code));
            }
            branches.push((idx, code));
        }

        if branches.is_empty() {
            return Vec::new();
        }

        let mut chain: Vec<Stmt> = Vec::new();
        for (idx, code) in branches.into_iter().rev() {
            let cond = Expr::Binary(
                BinOp::Eq,
                Box::new(Expr::Var(exit_var.clone())),
                Box::new(Expr::Constant(Constant::Felt(idx as u64))),
            );
            chain = vec![Stmt::If {
                cond,
                then_body: code,
                else_body: chain,
            }];
        }
        chain
    }

    fn find_loop_region(&self, head: usize) -> (HashSet<usize>, HashSet<usize>) {
        let latch_nodes: HashSet<_> = self.cfg.nodes[head]
            .prev
            .iter()
            .filter(|e| e.back_edge())
            .map(|e| e.node())
            .collect();

        let mut loop_nodes: HashSet<usize> = HashSet::new();
        loop_nodes.insert(head);
        let mut stack: Vec<usize> = latch_nodes.iter().copied().collect();
        while let Some(n) = stack.pop() {
            if loop_nodes.insert(n) {
                for pred in self.cfg.predecessors(n) {
                    if pred == head || self.dom_tree.dominates_strictly(head, pred) {
                        stack.push(pred);
                    }
                }
            }
        }

        let loop_succs: HashSet<usize> = self.cfg.region_successors(&loop_nodes);
        if std::env::var("DEBUG_LOOP").is_ok() {
            eprintln!(
                "graph_slice head {} loop_nodes {:?} loop_succs {:?}",
                head, loop_nodes, loop_succs
            );
        }
        (loop_nodes, loop_succs)
    }

    fn insert_breaks(
        &mut self,
        nodes: &HashSet<usize>,
        exit_var: Option<&Var>,
        exit_map: &HashMap<usize, usize>,
        head: usize,
    ) {
        for &n in nodes {
            let mut code = std::mem::take(&mut self.cfg.nodes[n].code);
            let mut new_edges = Vec::new();
            for edge in self.cfg.nodes[n].next.clone() {
                if nodes.contains(&edge.node()) && edge.node() != head {
                    new_edges.push(edge);
                    continue;
                }
                let cond_expr = edge_cond_expr(&edge, n, &self.expr_map);
                if edge.node() == head {
                    // Continue to next iteration.
                    if matches!(edge, Edge::Unconditional { .. }) {
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
                    if let Some(idx) = exit_map.get(&edge.node()) {
                        break_stmts.push(Stmt::Assign {
                            dest: var.clone(),
                            expr: Expr::Constant(Constant::Felt(*idx as u64)),
                        });
                    }
                }
                break_stmts.push(Stmt::Break);
                if matches!(edge, Edge::Unconditional { .. }) {
                    code.extend(break_stmts);
                } else {
                    code.push(Stmt::If {
                        cond: cond_expr,
                        then_body: break_stmts,
                        else_body: Vec::new(),
                    });
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
                .any(|edge| edge.back_edge() && nodes.contains(&edge.node()));

            self.cfg.nodes[succ]
                .prev
                .retain(|e| !nodes.contains(&e.node()));
            self.cfg.nodes[succ].prev.push(Edge::Unconditional {
                node: head,
                back_edge,
            });

            self.cfg.nodes[head].next.push(Edge::Unconditional {
                node: succ,
                back_edge,
            });
        }
    }
}

fn extract_branch_exprs(cfg: &mut Cfg) -> HashMap<NodeId, Expr> {
    let mut map = HashMap::new();
    for idx in 0..cfg.nodes.len() {
        let mut branch_idx = None;
        for (stmt_idx, stmt) in cfg.nodes[idx].code.iter().enumerate().rev() {
            if let Stmt::Branch(expr) = stmt {
                map.insert(idx, expr.clone());
                branch_idx = Some(stmt_idx);
                break;
            }
        }
        if let Some(stmt_idx) = branch_idx {
            cfg.nodes[idx].code.remove(stmt_idx);
        }
    }
    map
}

fn edge_cond_expr(edge: &Edge, source: NodeId, expr_map: &HashMap<NodeId, Expr>) -> Expr {
    match edge {
        Edge::Unconditional { .. } => Expr::True,
        Edge::Conditional {
            true_branch: expect_true,
            ..
        } => {
            let base = expr_map.get(&source).cloned().unwrap_or(Expr::Unknown);
            if *expect_true {
                base
            } else {
                Expr::Unary(UnOp::Not, Box::new(base))
            }
        }
    }
}

fn rewrite_repeat_loops(code: &mut Vec<Stmt>) {
    let mut i = 0;
    while i < code.len() {
        match &mut code[i] {
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                rewrite_repeat_loops(then_body);
                rewrite_repeat_loops(else_body);
            }
            Stmt::While { body, .. } => {
                rewrite_repeat_loops(body);
            }
            Stmt::Repeat { body, .. } => {
                rewrite_repeat_loops(body);
            }
            _ => {}
        }
        let repeat = if i > 0 {
            if let Stmt::While { cond, body } = &code[i] {
                fold_repeat_from_pattern(&code[i - 1], cond, body)
            } else {
                None
            }
        } else {
            None
        };
        if let Some(repeat) = repeat {
            code[i] = repeat;
            code.remove(i - 1);
            i = i.saturating_sub(1);
        } else {
            i += 1;
        }
    }
}

fn fold_repeat_from_pattern(init: &Stmt, cond: &Expr, body: &[Stmt]) -> Option<Stmt> {
    let init_var = match init {
        Stmt::Assign {
            dest,
            expr: Expr::Constant(Constant::Felt(0)),
        } => dest.clone(),
        _ => return None,
    };
    let (cond_var, count) = match cond {
        Expr::Binary(BinOp::Lt, lhs, rhs) => match (&**lhs, &**rhs) {
            (Expr::Var(v), Expr::Constant(Constant::Felt(n))) => {
                let count = usize::try_from(*n).ok()?;
                (v.clone(), count)
            }
            _ => return None,
        },
        _ => return None,
    };

    let mut phi_idx: Option<usize> = None;
    let mut step_var: Option<Var> = None;
    for (idx, stmt) in body.iter().enumerate() {
        if let Stmt::Phi { var, sources } = stmt {
            if var != &cond_var || sources.len() != 2 {
                continue;
            }
            if sources.iter().any(|s| *s == init_var) {
                let step = sources.iter().find(|s| **s != init_var).cloned();
                if let Some(step) = step {
                    phi_idx = Some(idx);
                    step_var = Some(step);
                    break;
                }
            }
        }
    }
    let phi_idx = phi_idx?;
    let step_var = step_var?;

    let mut step_idx: Option<usize> = None;
    for (idx, stmt) in body.iter().enumerate() {
        if let Stmt::Assign { dest, expr } = stmt {
            if *dest == step_var && is_increment_expr(expr, &cond_var) {
                step_idx = Some(idx);
                break;
            }
        }
    }
    let step_idx = step_idx?;

    let mut new_body = Vec::with_capacity(body.len().saturating_sub(2));
    for (idx, stmt) in body.iter().enumerate() {
        if idx == phi_idx || idx == step_idx {
            continue;
        }
        new_body.push(stmt.clone());
    }

    Some(Stmt::Repeat {
        loop_var: cond_var,
        loop_count: count,
        body: new_body,
    })
}

fn is_increment_expr(expr: &Expr, base: &Var) -> bool {
    match expr {
        Expr::Binary(BinOp::Add, lhs, rhs) => {
            (is_var(lhs, base) && is_one(rhs)) || (is_var(rhs, base) && is_one(lhs))
        }
        _ => false,
    }
}

fn is_var(expr: &Expr, var: &Var) -> bool {
    matches!(expr, Expr::Var(v) if v == var)
}

fn is_one(expr: &Expr) -> bool {
    matches!(expr, Expr::Constant(Constant::Felt(1)))
}

fn apply_loop_subscripts(code: &mut [Stmt]) {
    let idx_map = compute_loop_indices(code);
    if idx_map.is_empty() {
        return;
    }
    let mut by_index = HashMap::new();
    for (var, expr) in idx_map {
        by_index.insert(var.index, expr);
    }
    apply_subscripts_block(code, &by_index);
}

fn apply_subscripts_block(code: &mut [Stmt], subscripts: &HashMap<usize, IndexExpr>) {
    for stmt in code {
        apply_subscripts_stmt(stmt, subscripts);
    }
}

fn apply_subscripts_stmt(stmt: &mut Stmt, subscripts: &HashMap<usize, IndexExpr>) {
    match stmt {
        Stmt::Assign { dest, expr } => {
            apply_subscripts_expr(expr, subscripts);
            apply_subscripts_var(dest, subscripts);
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            apply_subscripts_expr(cond, subscripts);
            apply_subscripts_block(then_body, subscripts);
            apply_subscripts_block(else_body, subscripts);
        }
        Stmt::Repeat { loop_var, body, .. } => {
            apply_subscripts_var(loop_var, subscripts);
            apply_subscripts_block(body, subscripts);
        }
        Stmt::While { cond, body } => {
            apply_subscripts_expr(cond, subscripts);
            apply_subscripts_block(body, subscripts);
        }
        Stmt::Return(vals) => {
            for v in vals.iter_mut() {
                apply_subscripts_var(v, subscripts);
            }
        }
        Stmt::Phi { var, sources } => {
            apply_subscripts_var(var, subscripts);
            for src in sources.iter_mut() {
                apply_subscripts_var(src, subscripts);
            }
        }
        Stmt::Branch(expr) => apply_subscripts_expr(expr, subscripts),
        Stmt::MemLoad(mem) => {
            for v in mem.address.iter_mut().chain(mem.outputs.iter_mut()) {
                apply_subscripts_var(v, subscripts);
            }
        }
        Stmt::MemStore(mem) => {
            for v in mem.address.iter_mut().chain(mem.values.iter_mut()) {
                apply_subscripts_var(v, subscripts);
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in call.args.iter_mut().chain(call.results.iter_mut()) {
                apply_subscripts_var(v, subscripts);
            }
        }
        Stmt::DynCall { args, results } => {
            for v in args.iter_mut().chain(results.iter_mut()) {
                apply_subscripts_var(v, subscripts);
            }
        }
        Stmt::Intrinsic(intr) => {
            for v in intr.args.iter_mut().chain(intr.results.iter_mut()) {
                apply_subscripts_var(v, subscripts);
            }
        }
        Stmt::AdvLoad(load) => {
            for v in load.outputs.iter_mut() {
                apply_subscripts_var(v, subscripts);
            }
        }
        Stmt::AdvStore(store) => {
            for v in store.values.iter_mut() {
                apply_subscripts_var(v, subscripts);
            }
        }
        Stmt::LocalLoad(load) => {
            for v in load.outputs.iter_mut() {
                apply_subscripts_var(v, subscripts);
            }
        }
        Stmt::LocalStore(store) => {
            for v in store.values.iter_mut() {
                apply_subscripts_var(v, subscripts);
            }
        }
        Stmt::Inst(_) | Stmt::Nop | Stmt::Break | Stmt::Continue => {}
    }
}

fn apply_subscripts_expr(expr: &mut Expr, subscripts: &HashMap<usize, IndexExpr>) {
    match expr {
        Expr::Var(v) => apply_subscripts_var(v, subscripts),
        Expr::Binary(_, a, b) => {
            apply_subscripts_expr(a, subscripts);
            apply_subscripts_expr(b, subscripts);
        }
        Expr::Unary(_, a) => apply_subscripts_expr(a, subscripts),
        Expr::Constant(_) | Expr::True | Expr::Unknown => {}
    }
}

fn apply_subscripts_var(var: &mut Var, subscripts: &HashMap<usize, IndexExpr>) {
    if !matches!(var.subscript, Subscript::None) {
        return;
    }
    if let Some(expr) = subscripts.get(&var.index) {
        *var = var.with_subscript(Subscript::Expr(expr.clone()));
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
        let mut performer = InitDfs {
            post_order: Vec::with_capacity(cfg.nodes.len()),
            visited: HashSet::new(),
        };
        performer.visited.insert(0);
        performer.visit(cfg, 0);
        performer.post_order
    }

    fn visit(&mut self, cfg: &Cfg, n: usize) {
        for u in cfg.successors(n) {
            if self.visited.insert(u) {
                self.visit(cfg, u);
            }
        }
        self.post_order.push(n);
    }
}

fn next_var_index(cfg: &Cfg) -> usize {
    let mut max = 0usize;
    for bb in &cfg.nodes {
        for stmt in &bb.code {
            scan_stmt(stmt, &mut max);
        }
    }
    max.saturating_add(1)
}

fn scan_stmt(stmt: &Stmt, max: &mut usize) {
    match stmt {
        Stmt::Assign { dest: dst, expr } => {
            *max = (*max).max(dst.index);
            scan_expr(expr, max);
        }
        Stmt::Branch(expr) => scan_expr(expr, max),
        Stmt::AdvLoad(load) => {
            for v in load.outputs.iter() {
                *max = (*max).max(v.index);
            }
        }
        Stmt::AdvStore(store) => {
            for v in store.values.iter() {
                *max = (*max).max(v.index);
            }
        }
        Stmt::LocalLoad(load) => {
            for v in load.outputs.iter() {
                *max = (*max).max(v.index);
            }
        }
        Stmt::LocalStore(store) => {
            for v in store.values.iter() {
                *max = (*max).max(v.index);
            }
        }
        Stmt::MemLoad(mem) => {
            for v in mem.address.iter().chain(mem.outputs.iter()) {
                *max = (*max).max(v.index);
            }
        }
        Stmt::MemStore(mem) => {
            for v in mem.address.iter().chain(mem.values.iter()) {
                *max = (*max).max(v.index);
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in call.args.iter().chain(call.results.iter()) {
                *max = (*max).max(v.index);
            }
        }
        Stmt::DynCall { args, results } => {
            for v in args.iter().chain(results.iter()) {
                *max = (*max).max(v.index);
            }
        }
        Stmt::Intrinsic(intr) => {
            for v in intr.args.iter().chain(intr.results.iter()) {
                *max = (*max).max(v.index);
            }
        }
        Stmt::Phi { var, sources } => {
            *max = (*max).max(var.index);
            for s in sources {
                *max = (*max).max(s.index);
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            scan_expr(cond, max);
            for s in then_body.iter().chain(else_body.iter()) {
                scan_stmt(s, max);
            }
        }
        Stmt::Repeat { body, .. } => {
            for s in body.iter() {
                scan_stmt(s, max);
            }
        }
        Stmt::While { cond, body } => {
            scan_expr(cond, max);
            for s in body {
                scan_stmt(s, max);
            }
        }
        Stmt::Return(vals) => {
            for v in vals {
                *max = (*max).max(v.index);
            }
        }
        Stmt::Inst(_) | Stmt::Nop | Stmt::Break | Stmt::Continue => {}
    }
}

fn scan_expr(expr: &Expr, max: &mut usize) {
    match expr {
        Expr::Var(v) => *max = (*max).max(v.index),
        Expr::Binary(_, a, b) => {
            scan_expr(a, max);
            scan_expr(b, max);
        }
        Expr::Unary(_, a) => scan_expr(a, max),
        Expr::Constant(_) | Expr::True | Expr::Unknown => {}
    }
}

/// Hoist side-effect-free conditions used multiple times into temporaries.
fn hoist_shared_conditions(code: &mut Vec<Stmt>, next_var: &mut usize) {
    let mut counts: HashMap<String, (Expr, bool, usize)> = HashMap::new();
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
        let var = base_vars
            .entry(base_key.clone())
            .or_insert_with(|| {
            let v = Var::new(*next_var);
            *next_var += 1;
            hoisted_assigns.push(Stmt::Assign {
                dest: v.clone(),
                expr: base.clone(),
            });
            v
        })
            .clone();
        let expr = if neg {
            Expr::Unary(UnOp::Not, Box::new(Expr::Var(var.clone())))
        } else {
            Expr::Var(var.clone())
        };
        replacements.insert(key, expr);
    }

    if hoisted_assigns.is_empty() {
        return;
    }

    apply_replacements(code, &replacements);
    hoisted_assigns.append(code);
    *code = hoisted_assigns;
}

fn collect_conds(code: &[Stmt], counts: &mut HashMap<String, (Expr, bool, usize)>) {
    for stmt in code {
        match stmt {
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                bump_cond(cond, counts);
                collect_conds(then_body, counts);
                collect_conds(else_body, counts);
            }
            Stmt::While { cond, body } => {
                bump_cond(cond, counts);
                collect_conds(body, counts);
            }
            _ => {}
        }
    }
}

fn bump_cond(expr: &Expr, counts: &mut HashMap<String, (Expr, bool, usize)>) {
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
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                replace_cond_expr(cond, replacements);
                apply_replacements(then_body, replacements);
                apply_replacements(else_body, replacements);
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
        Expr::Binary(_, a, b) => {
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
        let has_backedge = preds.iter().any(|e| e.back_edge());
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

                for src in sources.iter() {
                    let src_var = src.clone();
                    // Heuristic: pick the first non-back-edge pred that defines the var as init.
                    for p in preds.iter() {
                        let p_node = p.node();
                        let is_back = p.back_edge();
                        if block_defs
                            .get(p_node)
                            .map_or(false, |defs| defs.contains(src))
                        {
                            if is_back {
                                if update_src.is_none() {
                                    update_src = Some((src_var.clone(), p_node));
                                }
                            } else if init_src.is_none() {
                                init_src = Some(src_var.clone());
                            }
                        }
                    }
                    // If still missing init, fall back to any non-backedge pred even without def.
                    if init_src.is_none() {
                        if let Some(p) = preds.iter().find(|e| !e.back_edge()) {
                            init_src = Some(src_var.clone());
                            let _ = p;
                        }
                    }
                    // If still missing update, fall back to any back-edge pred.
                    if update_src.is_none() {
                        if let Some(p) = preds.iter().find(|e| e.back_edge()) {
                            update_src = Some((src_var.clone(), p.node()));
                        }
                    }
                }

                if let (Some(init), Some((upd, upd_pred))) = (init_src, update_src) {
                    init_stmts.push(Stmt::Assign {
                        dest: var.clone(),
                        expr: Expr::Var(init.clone()),
                    });
                    carrier_pairs.insert((var.clone(), init.clone()));
                    pending_updates
                        .entry(upd_pred)
                        .or_default()
                        .push(Stmt::Assign {
                            dest: var.clone(),
                            expr: Expr::Var(upd.clone()),
                        });
                    carrier_pairs.insert((var.clone(), upd));
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
            Stmt::Assign { dest: dst, .. } => {
                defs.insert(dst.clone());
            }
            Stmt::MemLoad(mem) => {
                defs.extend(mem.outputs.iter().cloned());
            }
            Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
                defs.extend(call.results.iter().cloned());
            }
            Stmt::DynCall { results, .. } => {
                defs.extend(results.iter().cloned());
            }
            Stmt::Intrinsic(intr) => {
                defs.extend(intr.results.iter().cloned());
            }
            Stmt::AdvLoad(load) => {
                defs.extend(load.outputs.iter().cloned());
            }
            Stmt::LocalLoad(load) => {
                defs.extend(load.outputs.iter().cloned());
            }
            Stmt::Phi { var, .. } => {
                defs.insert(var.clone());
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                defs.extend(collect_defs_shallow(then_body));
                defs.extend(collect_defs_shallow(else_body));
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
                *stmt = Stmt::If {
                    cond: expr.clone(),
                    then_body: Vec::new(),
                    else_body: Vec::new(),
                };
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
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
