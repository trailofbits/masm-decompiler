//! Structuring passes: convert a CFG with branch markers into structured statements.
//!
//! This module transforms a CFG containing `IfBranch`, `WhileBranch`, and `RepeatBranch`
//! markers into a flat sequence of `If`, `While`, and `Repeat` statements.

use std::collections::{HashMap, HashSet};

use miden_assembly_syntax::ast::{ProcedureName, Visibility};
use miden_assembly_syntax::debuginfo::SourceSpan;

use crate::analysis::DefinesVars;
use crate::{
    cfg::{Cfg, NodeId},
    signature::ProcSignature,
    ssa::{Expr, Stmt, Var},
};

mod flatten;
mod simplify;
mod subscripts;

/// A structured procedure body with no CFG edges.
///
/// All control flow is represented by structured statements
/// (`If`, `While`, `Repeat`) rather than conditional branches.
#[derive(Debug, Clone)]
pub struct DecompiledBody {
    /// The statements in the procedure body.
    pub stmts: Vec<Stmt>,
}

impl DecompiledBody {
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
    pub body: DecompiledBody,
}

impl StructuredProc {
    /// Create a new structured procedure.
    pub fn new(
        name: ProcedureName,
        visibility: Visibility,
        span: SourceSpan,
        signature: ProcSignature,
        body: DecompiledBody,
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
    pub fn body(&self) -> &DecompiledBody {
        &self.body
    }

    /// Returns a mutable reference to the body.
    pub fn body_mut(&mut self) -> &mut DecompiledBody {
        &mut self.body
    }
}

/// Structure a CFG into a structured body.
pub fn structure(cfg: Cfg, simplify: bool) -> DecompiledBody {
    if cfg.nodes.is_empty() {
        return DecompiledBody::new(Vec::new());
    }

    let mut cfg = cfg;

    // Extract var_depths and loop_contexts before flattening consumes the CFG.
    let var_depths = std::mem::take(&mut cfg.var_depths);
    let loop_contexts = std::mem::take(&mut cfg.loop_contexts);

    // Lower phi nodes while CFG edge info is available.
    lift_loop_phis_with_cfg(&mut cfg);

    // Flatten control flow into structured statements.
    let mut code = flatten::flatten_control_flow(cfg);

    // Apply subscripts used during formatting.
    subscripts::compute_subscripts(&mut code, &var_depths, &loop_contexts);

    // Apply cleanup passes.
    if simplify {
        simplify::apply_simplification(&mut code);
    }
    DecompiledBody::new(code)
}

/// Lift loop-header phis while CFG information is still available.
fn lift_loop_phis_with_cfg(cfg: &mut Cfg) -> HashSet<(Var, Var)> {
    let mut carrier_pairs = HashSet::new();

    // Cache definitions per block.
    let mut block_defs: Vec<HashSet<Var>> = Vec::with_capacity(cfg.nodes.len());
    for bb in &cfg.nodes {
        block_defs.push(bb.code.defines_vars());
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
