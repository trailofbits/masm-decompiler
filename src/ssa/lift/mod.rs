//! SSA lifting pipeline and CFG traversal utilities.

mod context;
mod inst;
mod phi;
mod repeat;

use miden_assembly_syntax::ast::{Instruction, InvocationTarget};

use crate::cfg::{Cfg, Edge, NodeId};
use crate::signature::SignatureMap;

use super::{Expr, Stmt, Var};
use context::{Frame, SsaContext, VarAlloc, alloc_scope, build_entry_frame, retain_live_exprs};
use inst::lift_inst_to_stmt;
use phi::{BlockPhiState, emit_phis, merge_into_block};
use repeat::extract_repeat_count;

/// Errors produced during CFG-to-SSA lifting.
#[derive(Debug)]
pub enum SsaError {
    /// Unbalanced if-statement encountered during lifting.
    UnbalancedIf,
    /// Non-neutral while-loop encountered during lifting.
    NonNeutralWhile,
    /// Unsupported instruction encountered during lifting.
    UnknownInstruction(Instruction),
    /// `exec` call to procedure with unknown stack effect.
    UnknownStackEffect(InvocationTarget),
    /// A CFG node contained an unknown statement.
    UnknownStatement,
    /// Worklist iteration limit was exceeded.
    IterationLimitExceeded(usize),
}

pub type SsaResult<T> = Result<T, SsaError>;

/// Lift a MASM CFG to SSA.
///
///
/// # Errors
///
/// The analysis returns an error if it encounters any of the following:
///
///   1. Unsupported instructions
///   2. Unbalanced if-statements
///   3. Non-neutral while-loops
///   4. `exec` calls to procedures with unknown stack effects
///   5. Unknown statements in the CFG
///   6. Worklist iteration limit exceeded
///
pub fn lift_cfg_to_ssa(
    mut cfg: Cfg,
    module_path: &str,
    proc_path: &str,
    sigs: &SignatureMap,
) -> SsaResult<Cfg> {
    let original_codes = collect_original_codes(&cfg);
    let repeat_counts = compute_repeat_counts(&original_codes);

    let mut ctx = SsaContext::new(std::mem::take(&mut cfg.arena));
    let (mut in_state, mut base_stack_len, mut phi_state, mut def_cache, mut queue) =
        init_lift_state(&cfg, proc_path, sigs, &mut ctx);

    // Worklist traversal including back-edges; should converge quickly for small graphs.
    let mut iters = 0;
    while let Some(node) = queue.pop() {
        iters += 1;
        if iters > 10_000 {
            return Err(SsaError::IterationLimitExceeded(10_000));
        }
        process_node(
            node,
            &mut cfg,
            &original_codes,
            &mut phi_state,
            module_path,
            sigs,
            &mut in_state,
            &mut base_stack_len,
            &repeat_counts,
            &mut def_cache,
            &mut ctx,
            &mut queue,
        )?;
    }
    cfg.arena = ctx.into_arena();
    Ok(cfg)
}

/// Snapshot the original block codes before rewriting.
fn collect_original_codes(cfg: &Cfg) -> Vec<Vec<Stmt>> {
    cfg.nodes.iter().map(|n| n.code.clone()).collect()
}

/// Pre-compute repeat loop counts per block, if detectable.
fn compute_repeat_counts(original_codes: &[Vec<Stmt>]) -> Vec<Option<usize>> {
    original_codes
        .iter()
        .map(|code| extract_repeat_count(code))
        .collect()
}

/// Initialize per-block state for SSA lifting.
fn init_lift_state(
    cfg: &Cfg,
    proc_path: &str,
    sigs: &SignatureMap,
    ctx: &mut SsaContext,
) -> (
    Vec<Option<Frame>>,
    Vec<Option<usize>>,
    Vec<BlockPhiState>,
    Vec<Vec<Vec<Var>>>,
    Vec<NodeId>,
) {
    let mut in_state: Vec<Option<Frame>> = vec![None; cfg.nodes.len()];
    let mut base_stack_len: Vec<Option<usize>> = vec![None; cfg.nodes.len()];
    let phi_state: Vec<BlockPhiState> = vec![BlockPhiState::default(); cfg.nodes.len()];
    let def_cache: Vec<Vec<Vec<Var>>> = vec![Vec::new(); cfg.nodes.len()];

    let entry_frame = build_entry_frame(proc_path, sigs, ctx);
    base_stack_len[0] = Some(entry_frame.stack.len());
    in_state[0] = Some(entry_frame);
    let queue = vec![0];

    (in_state, base_stack_len, phi_state, def_cache, queue)
}

/// Lift a single CFG node and propagate its state to successors.
fn process_node(
    node: NodeId,
    cfg: &mut Cfg,
    original_codes: &[Vec<Stmt>],
    phi_state: &mut [BlockPhiState],
    module_path: &str,
    sigs: &SignatureMap,
    in_state: &mut [Option<Frame>],
    base_stack_len: &mut [Option<usize>],
    repeat_counts: &[Option<usize>],
    def_cache: &mut Vec<Vec<Vec<Var>>>,
    ctx: &mut SsaContext,
    queue: &mut Vec<NodeId>,
) -> SsaResult<()> {
    let mut state = match &in_state[node] {
        Some(f) => f.clone(),
        None => return Ok(()),
    };
    let orig_code = &original_codes[node];
    let mut new_code = lift_block_code(
        node,
        orig_code,
        &phi_state[node],
        module_path,
        sigs,
        &mut state,
        ctx,
        def_cache,
    )?;
    let mut branch_alloc = alloc_scope(def_cache, node, orig_code.len());
    ensure_branch_stmt(
        &cfg.nodes[node].next,
        &mut new_code,
        &mut state,
        ctx,
        &mut branch_alloc,
    )?;
    cfg.nodes[node].code = new_code;
    retain_live_exprs(&mut state);

    // Propagate to successors
    for edge in cfg.nodes[node].next.clone() {
        let succ = edge.node();
        let updated = merge_into_block(
            succ,
            node,
            edge.back_edge(),
            &state,
            in_state,
            phi_state,
            repeat_counts,
            base_stack_len,
            ctx,
        )?;
        if updated {
            queue.push(succ);
        }
    }
    Ok(())
}

/// Lift all statements in a block, inserting any leading phis.
fn lift_block_code(
    node: NodeId,
    orig_code: &[Stmt],
    phis: &BlockPhiState,
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut SsaContext,
    def_cache: &mut Vec<Vec<Vec<Var>>>,
) -> SsaResult<Vec<Stmt>> {
    let mut new_code = Vec::new();
    emit_phis(phis, &mut new_code);
    for (stmt_idx, stmt) in orig_code.iter().enumerate() {
        let mut alloc = alloc_scope(def_cache, node, stmt_idx);
        match stmt {
            Stmt::Inst(inst) => {
                let lifted = lift_inst_to_stmt(inst, module_path, sigs, state, ctx, &mut alloc)?;
                new_code.extend(lifted);
            }
            _ => new_code.push(stmt.clone()),
        }
    }
    Ok(new_code)
}

/// Ensure a branch statement exists when the CFG has conditional edges.
fn ensure_branch_stmt(
    edges: &[Edge],
    code: &mut Vec<Stmt>,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<()> {
    let has_conditional = edges.iter().any(|e| matches!(e, Edge::Conditional { .. }));
    if !has_conditional {
        return Ok(());
    }
    let mut branch_idx = None;
    let mut branch_unknown = false;
    for (idx, stmt) in code.iter().enumerate().rev() {
        if let Stmt::Branch(expr) = stmt {
            branch_idx = Some(idx);
            branch_unknown = matches!(expr, Expr::Unknown);
            break;
        }
    }
    if branch_idx.is_none() || branch_unknown {
        let cond_var = state.pop_one(ctx, alloc, 1);
        let cond_expr = state
            .exprs
            .get(&cond_var)
            .cloned()
            .unwrap_or(Expr::Var(cond_var));
        if let Some(idx) = branch_idx {
            code[idx] = Stmt::Branch(cond_expr);
        } else {
            code.push(Stmt::Branch(cond_expr));
        }
    }
    Ok(())
}

/// Compute the maximum required input stack depth across blocks.
fn compute_inputs(in_state: &[Option<Frame>]) -> usize {
    in_state
        .iter()
        .filter_map(|f| f.as_ref().map(|f| f.stack.required_depth()))
        .max()
        .unwrap_or(0)
}

/// Compute a common output stack depth if all exits agree.
fn compute_outputs(cfg: &Cfg, in_state: &[Option<Frame>]) -> Option<usize> {
    let mut outputs: Option<usize> = None;
    for (idx, bb) in cfg.nodes.iter().enumerate() {
        let has_forward_succ = bb.next.iter().any(|e| !e.back_edge());
        if !has_forward_succ {
            if let Some(frame) = &in_state[idx] {
                match outputs {
                    None => outputs = Some(frame.stack.len()),
                    Some(prev) if prev == frame.stack.len() => {}
                    _ => {
                        outputs = None;
                        break;
                    }
                }
            }
        }
    }
    outputs
}
