//! SSA lifting pipeline and CFG traversal utilities.

mod context;
mod inst;
mod phi;
mod repeat;

use crate::cfg::{Cfg, Edge, NodeId};
use crate::signature::{ProcSignature, SignatureMap};

use super::{Condition, Expr, SsaError, SsaResult, SsaStack, Stmt, Var};
use context::{Frame, SsaContext, VarAlloc, alloc_scope, build_entry_frame, retain_live_exprs};
use inst::lift_inst_to_stmt;
use phi::{BlockPhiState, emit_phis, merge_into_block};
use repeat::{RepeatBodySummary, RepeatInfo, extract_repeat_info, summarize_repeat_body};

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
    let mut repeat_infos = compute_repeat_infos(&original_codes);
    let mut repeat_summaries: Vec<Option<RepeatBodySummary>> = vec![None; cfg.nodes.len()];

    let mut ctx = SsaContext::new(std::mem::take(&mut cfg.arena));

    // Allocate loop counter variables for all repeat headers.
    allocate_repeat_loop_vars(&mut repeat_infos, &mut ctx);

    // Look up the expected number of outputs from the procedure signature.
    // If the signature is unknown, we cannot determine the correct outputs.
    let output_count = match sigs.get(proc_path) {
        Some(ProcSignature::Known { outputs, .. }) => Some(*outputs),
        _ => None,
    };

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
            &mut repeat_infos,
            &mut repeat_summaries,
            &mut def_cache,
            &mut ctx,
            &mut queue,
            output_count,
        )?;
    }

    let (arena, var_depths) = ctx.into_parts();
    cfg.arena = arena;
    cfg.var_depths = var_depths;
    Ok(cfg)
}

/// Snapshot the original block codes before rewriting.
fn collect_original_codes(cfg: &Cfg) -> Vec<Vec<Stmt>> {
    cfg.nodes.iter().map(|n| n.code.clone()).collect()
}

/// Pre-compute repeat loop info per block, if detectable.
fn compute_repeat_infos(original_codes: &[Vec<Stmt>]) -> Vec<Option<RepeatInfo>> {
    original_codes
        .iter()
        .map(|code| extract_repeat_info(code))
        .collect()
}

/// Allocate loop counter variables for all repeat headers.
fn allocate_repeat_loop_vars(repeat_infos: &mut [Option<RepeatInfo>], ctx: &mut SsaContext) {
    for info in repeat_infos.iter_mut().flatten() {
        info.loop_var = Some(ctx.new_var());
    }
}

/// Update the RepeatBranch condition with the allocated loop_var.
fn update_repeat_branch_loop_var(
    node: NodeId,
    repeat_infos: &[Option<RepeatInfo>],
    code: &mut [Stmt],
) {
    let Some(info) = repeat_infos.get(node).and_then(|r| r.as_ref()) else {
        return;
    };
    for stmt in code.iter_mut() {
        if let Stmt::RepeatBranch(Condition::Count { loop_var, .. }) = stmt {
            *loop_var = info.loop_var.clone();
        }
    }
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
    repeat_infos: &mut [Option<RepeatInfo>],
    repeat_summaries: &mut [Option<RepeatBodySummary>],
    def_cache: &mut Vec<Vec<Vec<Var>>>,
    ctx: &mut SsaContext,
    queue: &mut Vec<NodeId>,
    output_count: Option<usize>,
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
        repeat_infos,
        module_path,
        sigs,
        &mut state,
        ctx,
        def_cache,
    )?;

    // Update RepeatBranch condition with allocated loop_var.
    update_repeat_branch_loop_var(node, repeat_infos, &mut new_code);

    let mut branch_alloc = alloc_scope(def_cache, node, orig_code.len());
    ensure_branch_cond(
        &cfg.nodes[node].next,
        &mut new_code,
        &mut state,
        ctx,
        &mut branch_alloc,
    )?;
    cfg.nodes[node].code = new_code;
    retain_live_exprs(&mut state);

    // Add return statement for exit nodes (no successors).
    if cfg.nodes[node].next.is_empty() {
        let has_return = cfg.nodes[node]
            .code
            .last()
            .map(|stmt| matches!(stmt, Stmt::Return(_)))
            .unwrap_or(false);
        if !has_return {
            if let Some(n) = output_count {
                let outputs = state
                    .stack
                    .outputs(n)
                    .expect("stack must have enough values for procedure outputs");
                cfg.nodes[node].code.push(Stmt::Return(outputs));
            }
        }
    }

    maybe_record_repeat_summary(
        node,
        cfg,
        repeat_infos,
        repeat_summaries,
        base_stack_len,
        queue,
    )?;

    // Propagate to successors
    for edge in cfg.nodes[node].next.clone() {
        let succ = edge.node();
        if let Some(info) = repeat_infos.get(node).and_then(|r| r.as_ref()) {
            if matches!(
                edge,
                Edge::Conditional {
                    true_branch: false,
                    ..
                }
            ) {
                let Some(summary) = repeat_summaries.get(node).and_then(|s| s.as_ref()) else {
                    continue;
                };
                let exit_frame = compute_repeat_exit_frame(&state, info, summary, ctx)?;
                let updated = merge_into_block(
                    succ,
                    node,
                    edge.back_edge(),
                    &exit_frame,
                    in_state,
                    phi_state,
                    repeat_infos,
                    base_stack_len,
                    ctx,
                )?;
                if updated {
                    queue.push(succ);
                }
                continue;
            }
        }
        let updated = merge_into_block(
            succ,
            node,
            edge.back_edge(),
            &state,
            in_state,
            phi_state,
            repeat_infos,
            base_stack_len,
            ctx,
        )?;
        if updated {
            queue.push(succ);
        }
    }
    Ok(())
}

fn maybe_record_repeat_summary(
    node: NodeId,
    cfg: &mut Cfg,
    repeat_infos: &[Option<RepeatInfo>],
    repeat_summaries: &mut [Option<RepeatBodySummary>],
    base_stack_len: &[Option<usize>],
    queue: &mut Vec<NodeId>,
) -> SsaResult<()> {
    use crate::cfg::LoopContext;

    for edge in cfg.nodes[node].next.iter() {
        if !edge.back_edge() {
            continue;
        }
        let header = edge.node();
        let Some(info) = repeat_infos.get(header).and_then(|r| r.as_ref()) else {
            continue;
        };
        if repeat_summaries
            .get(header)
            .and_then(|s| s.as_ref())
            .is_some()
        {
            continue;
        }
        let Some(loop_var) = &info.loop_var else {
            continue;
        };
        let summary = summarize_repeat_body(&cfg.nodes[node].code, loop_var)
            .ok_or(SsaError::NonNeutralWhile)?;

        // Record the loop context for subscript computation.
        let entry_depth = base_stack_len.get(header).and_then(|d| *d).unwrap_or(0);
        let effect_per_iter = summary.outputs.len() as isize - summary.pops as isize;
        cfg.loop_contexts.insert(
            header,
            LoopContext {
                loop_var_index: loop_var.index,
                entry_depth,
                effect_per_iter,
                iter_count: info.count,
            },
        );

        repeat_summaries[header] = Some(summary);
        queue.push(header);
    }
    Ok(())
}

fn compute_repeat_exit_frame(
    entry: &Frame,
    info: &RepeatInfo,
    summary: &RepeatBodySummary,
    ctx: &mut SsaContext,
) -> SsaResult<Frame> {
    use super::{IndexExpr, Subscript};

    let mut stack: Vec<Var> = entry.stack.iter().cloned().collect();
    let delta = summary.outputs.len().saturating_sub(summary.pops);
    let is_consuming = summary.pops > summary.outputs.len();

    for iter in 0..info.count {
        if summary.pops > stack.len() {
            return Err(SsaError::NonNeutralWhile);
        }
        let keep = stack.len().saturating_sub(summary.pops);
        stack.truncate(keep);

        // For producing loops (delta > 0), assign concrete subscripts to escaping outputs.
        // Variables that escape the loop should have subscripts based on their iteration.
        if delta > 0 {
            for (offset, var) in summary.outputs.iter().take(delta).enumerate() {
                let subscript_value = (iter * delta + offset) as i64;
                let subscript = Subscript::Expr(IndexExpr::Const(subscript_value));
                stack.push(var.with_subscript(subscript));
            }
            // Non-escaping outputs (consumed by next iteration) keep their original form.
            for var in summary.outputs.iter().skip(delta) {
                stack.push(var.clone());
            }
        } else {
            // For neutral/consuming loops, outputs are consumed internally.
            stack.extend(summary.outputs.iter().cloned());
        }
    }

    // For consuming loops, update var_depths to reflect final stack positions.
    // After all iterations, the final stack elements are at positions 0, 1, 2, ...
    // regardless of where they were originally born.
    if is_consuming {
        for (pos, var) in stack.iter().enumerate() {
            ctx.record_depth(var, pos);
        }
    }

    let mut exprs = entry.exprs.clone();
    let live: std::collections::HashSet<Var> = stack.iter().cloned().collect();
    exprs.retain(|k, _| live.contains(k));
    for var in &stack {
        exprs
            .entry(var.clone())
            .or_insert_with(|| Expr::Var(var.clone()));
    }
    let required_depth = entry.stack.required_depth().max(stack.len());
    let stack = std::collections::VecDeque::from(stack);
    Ok(Frame {
        stack: SsaStack::from_parts(stack, required_depth),
        exprs,
    })
}

/// Lift all statements in a block, inserting any leading phis.
fn lift_block_code(
    node: NodeId,
    orig_code: &[Stmt],
    phis: &BlockPhiState,
    _repeat_infos: &[Option<RepeatInfo>],
    module_path: &str,
    sigs: &SignatureMap,
    state: &mut Frame,
    ctx: &mut SsaContext,
    def_cache: &mut Vec<Vec<Vec<Var>>>,
) -> SsaResult<Vec<Stmt>> {
    let mut new_code = Vec::new();
    emit_phis(phis, &mut new_code);

    // Note: Repeat loop counters don't need phi/init/step statements.
    // The loop counter is implicit in the `for i in 0..N` syntax.

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

/// Fill in if- and while-statement branch conditions based on the actual stack
/// content.
fn ensure_branch_cond(
    edges: &[Edge],
    code: &mut Vec<Stmt>,
    state: &mut Frame,
    ctx: &mut SsaContext,
    alloc: &mut impl VarAlloc,
) -> SsaResult<()> {
    // Exit early if the block is empty or does not have multiple outgoing
    // edges.
    if code.len() == 0 || edges.len() <= 1 {
        return Ok(());
    }

    // Check if we need to update the branch condition based on the stack.
    let idx = code.len() - 1;
    match &code[idx] {
        Stmt::IfBranch(Condition::Stack(expr)) if matches!(expr, Expr::Unknown) => {
            let cond_var = state.pop_one(ctx, alloc, 1);
            let cond_expr = state
                .exprs
                .get(&cond_var)
                .cloned()
                .unwrap_or(Expr::Var(cond_var));
            code[idx] = Stmt::IfBranch(Condition::Stack(cond_expr));
        }
        Stmt::WhileBranch(Condition::Stack(expr)) if matches!(expr, Expr::Unknown) => {
            let cond_var = state.pop_one(ctx, alloc, 1);
            let cond_expr = state
                .exprs
                .get(&cond_var)
                .cloned()
                .unwrap_or(Expr::Var(cond_var));
            code[idx] = Stmt::WhileBranch(Condition::Stack(cond_expr));
        }
        _ => {}
    }
    Ok(())
}
