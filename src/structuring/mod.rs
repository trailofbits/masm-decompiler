//! Structuring passes: convert a CFG with branch markers into structured statements.
//!
//! This module transforms a CFG containing `IfBranch`, `WhileBranch`, and `RepeatBranch`
//! markers into a flat sequence of `If`, `While`, and `Repeat` statements.

use std::collections::{HashMap, HashSet};

use miden_assembly_syntax::ast::{ProcedureName, Visibility};
use miden_assembly_syntax::debuginfo::SourceSpan;

use crate::{
    analysis::compute_loop_indices,
    cfg::{Cfg, NodeId},
    signature::ProcSignature,
    ssa::{Condition, Expr, IndexExpr, Stmt, Subscript, UnOp, Var},
};

/// A structured procedure body with no CFG edges.
///
/// All control flow is represented by structured statements
/// (`If`, `While`, `Repeat`) rather than conditional branches.
#[derive(Debug, Clone)]
pub struct StructuredBody {
    /// The statements in the procedure body.
    pub stmts: Vec<Stmt>,
}

impl StructuredBody {
    /// Create a new structured body from a sequence of statements.
    pub fn new(stmts: Vec<Stmt>) -> Self {
        Self { stmts }
    }

    /// Returns a reference to the statements.
    pub fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }

    /// Returns a mutable reference to the statements.
    pub fn stmts_mut(&mut self) -> &mut Vec<Stmt> {
        &mut self.stmts
    }
}

/// A decompiled procedure with structured control flow.
#[derive(Debug, Clone)]
pub struct StructuredProc {
    /// The procedure name.
    pub name: ProcedureName,
    /// Visibility (public/private).
    pub visibility: Visibility,
    /// Source span of the original procedure.
    pub span: SourceSpan,
    /// The inferred procedure signature.
    pub signature: ProcSignature,
    /// The decompiled procedure body.
    pub body: StructuredBody,
}

impl StructuredProc {
    /// Create a new structured procedure.
    pub fn new(
        name: ProcedureName,
        visibility: Visibility,
        span: SourceSpan,
        signature: ProcSignature,
        body: StructuredBody,
    ) -> Self {
        Self {
            name,
            visibility,
            span,
            signature,
            body,
        }
    }

    /// Returns the procedure name.
    pub fn name(&self) -> &ProcedureName {
        &self.name
    }

    /// Returns the visibility.
    pub fn visibility(&self) -> Visibility {
        self.visibility
    }

    /// Returns the source span.
    pub fn span(&self) -> SourceSpan {
        self.span
    }

    /// Returns the procedure signature.
    pub fn signature(&self) -> &ProcSignature {
        &self.signature
    }

    /// Returns a reference to the body.
    pub fn body(&self) -> &StructuredBody {
        &self.body
    }

    /// Returns a mutable reference to the body.
    pub fn body_mut(&mut self) -> &mut StructuredBody {
        &mut self.body
    }
}

mod cond;
mod flatten;
mod rename_vars;
mod side_effects;
mod simplify;

/// Structure a CFG into a structured body.
pub fn structure(cfg: Cfg) -> StructuredBody {
    if cfg.nodes.is_empty() {
        return StructuredBody::new(Vec::new());
    }

    let mut cfg = cfg;

    // Lower phi nodes while CFG edge info is available.
    let carriers = lower_loop_phis_with_cfg(&mut cfg);

    // Flatten control flow into structured statements.
    let mut code = flatten::flatten_control_flow(cfg);

    // Apply cleanup passes.
    side_effects::prune_nops(&mut code);
    cond::refine(&mut code);
    hoist_shared_conditions(&mut code);
    side_effects::prune_side_effects(&mut code);
    simplify::apply(&mut code);

    // Apply loop subscripts before renaming so indices match.
    // Then renaming will update both variable indices and IndexExpr::LoopVar indices.
    apply_loop_subscripts(&mut code);
    rename_vars::apply(&mut code, &carriers);
    simplify::apply(&mut code);

    StructuredBody::new(code)
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
        Stmt::IfBranch(Condition::Stack(expr))
        | Stmt::WhileBranch(Condition::Stack(expr)) => apply_subscripts_expr(expr, subscripts),
        Stmt::IfBranch(Condition::Count { .. })
        | Stmt::WhileBranch(Condition::Count { .. })
        | Stmt::RepeatBranch(_) => {}
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

/// Hoist side-effect-free conditions used multiple times into temporaries.
fn hoist_shared_conditions(code: &mut Vec<Stmt>) {
    let mut next_var = next_var_index(code);
    let mut counts: HashMap<String, (Expr, bool, usize)> = HashMap::new();
    collect_conds(code, &mut counts);

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
                let v = Var::new(next_var);
                next_var += 1;
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

fn next_var_index(code: &[Stmt]) -> usize {
    let mut max = 0usize;
    for stmt in code {
        scan_stmt(stmt, &mut max);
    }
    max.saturating_add(1)
}

fn scan_stmt(stmt: &Stmt, max: &mut usize) {
    match stmt {
        Stmt::Assign { dest: dst, expr } => {
            *max = (*max).max(dst.index);
            scan_expr(expr, max);
        }
        Stmt::IfBranch(Condition::Stack(expr))
        | Stmt::WhileBranch(Condition::Stack(expr)) => scan_expr(expr, max),
        Stmt::IfBranch(Condition::Count { .. })
        | Stmt::WhileBranch(Condition::Count { .. })
        | Stmt::RepeatBranch(_) => {}
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

/// Lower loop-header phis while CFG information is still available.
fn lower_loop_phis_with_cfg(cfg: &mut Cfg) -> HashSet<(Var, Var)> {
    let mut carrier_pairs = HashSet::new();

    // Collect definitions per block.
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
                    continue;
                }

                let mut init_src: Option<Var> = None;
                let mut update_src: Option<(Var, NodeId)> = None;

                for src in sources.iter() {
                    let src_var = src.clone();
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
                    if init_src.is_none() {
                        if let Some(_p) = preds.iter().find(|e| !e.back_edge()) {
                            init_src = Some(src_var.clone());
                        }
                    }
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

                new_code.push(Stmt::Phi { var, sources });
            } else {
                new_code.push(stmt);
            }
        }

        if !init_stmts.is_empty() {
            let mut combined = init_stmts;
            combined.extend(new_code.into_iter());
            cfg.nodes[head].code = combined;
        } else {
            cfg.nodes[head].code = new_code;
        }
    }

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
            Stmt::While { .. } => {}
            _ => {}
        }
    }
    defs
}
