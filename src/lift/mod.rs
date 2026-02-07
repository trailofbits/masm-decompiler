//! Direct AST-to-IR lifting.
//!
//! This module transforms MASM AST directly into structured IR statements,
//! without an intermediate CFG representation. The approach mirrors signature
//! inference: recursive AST traversal with symbolic stack tracking.

mod inst;
mod stack;

use miden_assembly_syntax::ast::{Block, Instruction, Op, Procedure};
use std::collections::{HashMap, HashSet, VecDeque};

use crate::ir::{Expr, IfPhi, IndexExpr, LoopPhi, LoopVar, Stmt, Var, VarBase, ValueId};
use crate::signature::{ProcSignature, SignatureMap, StackEffect};

use stack::{SlotId, StackEntry};
pub use stack::SymbolicStack;

/// Errors that can occur during lifting.
#[derive(Debug)]
pub enum LiftingError {
    /// Unsupported instruction encountered.
    UnsupportedInstruction(Instruction),
    /// Call to procedure with unknown signature.
    UnknownCallTarget(String),
    /// Unbalanced if-statement (branches have different stack effects).
    UnbalancedIf,
    /// Non-neutral while loop.
    NonNeutralWhile,
    /// If-statement branches produced incompatible variable subscripts.
    IncompatibleIfMerge,
    /// Repeat loop pattern cannot be represented with linear subscripts.
    UnsupportedRepeatPattern(String),
}

impl std::fmt::Display for LiftingError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LiftingError::UnsupportedInstruction(inst) => {
                write!(f, "unsupported instruction `{inst}` found")
            }
            LiftingError::UnknownCallTarget(target) => {
                write!(f, "unknown call target `{target}` found")
            }
            LiftingError::UnbalancedIf => write!(f, "unbalanced if-statement"),
            LiftingError::NonNeutralWhile => write!(f, "non-neutral while loop"),
            LiftingError::IncompatibleIfMerge => {
                write!(f, "if-statement branches produced incompatible subscripts")
            }
            LiftingError::UnsupportedRepeatPattern(reason) => {
                write!(f, "unsupported repeat loop pattern: {reason}")
            }
        }
    }
}

impl std::error::Error for LiftingError {}

/// Result type for lifting operations.
pub type LiftingResult<T> = Result<T, LiftingError>;

/// Context for tracking loop nesting during lifting.
#[derive(Debug, Clone, Default)]
pub struct LoopContext {
    /// Stack of (loop_var, entry_depth) for each enclosing loop.
    loops: Vec<(LoopVar, usize)>,
}

impl LoopContext {
    /// Create a new empty loop context.
    pub fn new() -> Self {
        Self { loops: Vec::new() }
    }

    /// Enter a new loop with the given loop variable and entry stack depth.
    pub fn enter(&mut self, loop_var: LoopVar, entry_depth: usize) {
        self.loops.push((loop_var, entry_depth));
    }

    /// Exit the current loop.
    pub fn exit(&mut self) {
        self.loops.pop();
    }

    /// Get the current loop nesting depth (number of enclosing loops).
    pub fn depth(&self) -> usize {
        self.loops.len()
    }

    /// Get the innermost loop info, if any.
    pub fn innermost(&self) -> Option<&(LoopVar, usize)> {
        self.loops.last()
    }
}

/// Lift a procedure AST to structured IR statements.
///
/// This is the main entry point for the lifting pass. It initializes the
/// symbolic stack with input variables based on the procedure signature,
/// processes the procedure body, and appends a return statement.
pub fn lift_proc(
    proc: &Procedure,
    proc_path: &str,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<Vec<Stmt>> {
    let mut stack = SymbolicStack::new();
    let mut loop_ctx = LoopContext::new();

    // Initialize stack with input variables from signature.
    if let Some(ProcSignature::Known { inputs, .. }) = sigs.get(proc_path) {
        stack.ensure_depth(*inputs);
    }

    let mut stmts = lift_block(proc.body(), &mut stack, &mut loop_ctx, module_path, sigs)?;

    // Add return statement with outputs.
    if let Some(ProcSignature::Known { outputs, .. }) = sigs.get(proc_path) {
        let return_vars = stack.top_n(*outputs);
        stmts.push(Stmt::Return(return_vars));
    }

    Ok(stmts)
}

/// Lift a block of operations to statements.
fn lift_block(
    block: &Block,
    stack: &mut SymbolicStack,
    loop_ctx: &mut LoopContext,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<Vec<Stmt>> {
    let mut stmts = Vec::new();
    for op in block.iter() {
        let op_stmts = lift_op(op, stack, loop_ctx, module_path, sigs)?;
        stmts.extend(op_stmts);
    }
    Ok(stmts)
}

/// Lift a single operation to statements.
fn lift_op(
    op: &Op,
    stack: &mut SymbolicStack,
    loop_ctx: &mut LoopContext,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<Vec<Stmt>> {
    match op {
        Op::Inst(inst) => inst::lift_inst(inst.inner(), stack, loop_ctx, module_path, sigs),
        Op::If {
            then_blk, else_blk, ..
        } => lift_if(then_blk, else_blk, stack, loop_ctx, module_path, sigs),
        Op::Repeat { count, body, .. } => {
            lift_repeat(*count as usize, body, stack, loop_ctx, module_path, sigs)
        }
        Op::While { body, .. } => lift_while(body, stack, loop_ctx, module_path, sigs),
    }
}

/// Lift an if-else construct.
///
/// Both branches must have the same stack effect.
fn lift_if(
    then_block: &Block,
    else_block: &Block,
    stack: &mut SymbolicStack,
    loop_ctx: &mut LoopContext,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<Vec<Stmt>> {
    // Pop condition from stack.
    let cond_var = stack.pop();
    let cond = Expr::Var(cond_var);

    // Process both branches with cloned stacks.
    let mut then_stack = stack.clone();
    let mut else_stack = stack.clone();

    let then_body = lift_block(then_block, &mut then_stack, loop_ctx, module_path, sigs)?;
    let else_body = lift_block(else_block, &mut else_stack, loop_ctx, module_path, sigs)?;

    // Verify balanced stack effects.
    if then_stack.len() != else_stack.len() {
        return Err(LiftingError::UnbalancedIf);
    }

    // Merge branch stacks with Phi nodes where needed.
    let mut phis = Vec::new();
    let mut merged = Vec::with_capacity(then_stack.len());

    for (then_var, else_var) in then_stack.iter().zip(else_stack.iter()) {
        if then_var.subscript != else_var.subscript {
            return Err(LiftingError::IncompatibleIfMerge);
        }

        if then_var.base == else_var.base && then_var.subscript == else_var.subscript {
            merged.push(then_var.clone());
            continue;
        }

        let dest = stack.fresh_like(then_var);
        phis.push(IfPhi {
            dest: dest.clone(),
            then_var: then_var.clone(),
            else_var: else_var.clone(),
        });
        merged.push(dest);
    }

    stack.set_stack(merged);

    Ok(vec![Stmt::If {
        cond,
        then_body,
        else_body,
        phis,
    }])
}

/// Lift a repeat loop construct.
///
/// For repeat loops, we process the body once to get the template statements,
/// then compute appropriate subscripts for variables that escape the loop.
fn lift_repeat(
    count: usize,
    body: &Block,
    stack: &mut SymbolicStack,
    loop_ctx: &mut LoopContext,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<Vec<Stmt>> {
    let entry_depth = stack.len();
    let entry_entries = stack.to_entries();

    // Create loop variable using current nesting depth.
    // The depth uniquely identifies this loop within its scope and maps
    // directly to loop counter names (0 → i, 1 → j, etc.).
    let loop_var = LoopVar::new(loop_ctx.depth());

    // Enter loop context.
    loop_ctx.enter(loop_var, entry_depth);

    // Process body once to get template and determine stack effect.
    let body_stmts = lift_block(body, stack, loop_ctx, module_path, sigs)?;

    // Exit loop context.
    loop_ctx.exit();

    let exit_depth = stack.len();
    let exit_entries = stack.to_entries();
    let (mut repeat_phis, loop_carried_dests, loop_carried_ids) =
        collect_repeat_phis_by_slot(&entry_entries, &exit_entries, stack);

    // Compute net effect per iteration.
    let delta = exit_depth as isize - entry_depth as isize;
    let loop_depth = loop_var.loop_depth;
    let value_slots = stack.value_slots();
    let exit2_slots = if count > 1 {
        Some(simulate_repeat_slots(body, &exit_entries, module_path, sigs)?)
    } else {
        None
    };
    let slot_indices = compute_slot_indices(
        &entry_entries,
        &exit_entries,
        exit2_slots.as_deref(),
        count,
    )?;
    let produced_value_ids = collect_produced_value_ids(
        &entry_entries,
        &exit_entries,
        &body_stmts,
        &value_slots,
    );
    let produced_stride = if delta > 0 { delta as i64 } else { 0 };
    let mut body_stmts = transform_loop_subscripts(
        body_stmts,
        loop_depth,
        &slot_indices,
        &value_slots,
        &loop_carried_ids,
        &produced_value_ids,
        produced_stride,
    );
    repeat_phis = repeat_phis
        .into_iter()
        .map(|phi| {
            transform_loop_phi_subscripts(
                phi,
                loop_depth,
                &slot_indices,
                &value_slots,
                &loop_carried_ids,
                &produced_value_ids,
                produced_stride,
            )
        })
        .collect();
    let loop_input_ids = collect_loop_input_ids(&entry_entries, &exit_entries);
    if !loop_input_ids.is_empty() {
        body_stmts = transform_loop_input_bases(body_stmts, &loop_input_ids, loop_depth);
        repeat_phis = repeat_phis
            .into_iter()
            .map(|phi| LoopPhi {
                dest: transform_var_loop_input(phi.dest, &loop_input_ids, loop_depth),
                init: transform_var_loop_input(phi.init, &loop_input_ids, loop_depth),
                step: transform_var_loop_input(phi.step, &loop_input_ids, loop_depth),
            })
            .collect();
    }

    let produced_slots = collect_produced_slot_ids(&entry_entries, &exit_entries);
    update_stack_after_repeat(
        count,
        body,
        stack,
        &exit_entries,
        &loop_carried_dests,
        &produced_slots,
        module_path,
        sigs,
    )?;

    Ok(vec![Stmt::Repeat {
        loop_var,
        loop_count: count,
        body: body_stmts,
        phis: repeat_phis,
    }])
}

/// Add two index expressions, simplifying trivial cases.
///
/// This is used to combine subscript contributions from nested loops.
fn add_index_exprs(a: IndexExpr, b: IndexExpr) -> IndexExpr {
    match (&a, &b) {
        // Identity: 0 + x = x, x + 0 = x
        (IndexExpr::Const(0), _) => b,
        (_, IndexExpr::Const(0)) => a,
        // Constant folding
        (IndexExpr::Const(x), IndexExpr::Const(y)) => IndexExpr::Const(x + y),
        // General case
        _ => IndexExpr::Add(Box::new(a), Box::new(b)),
    }
}

/// Build a loop-term expression `coeff * loop_var`.
fn loop_term(loop_var_id: usize, coeff: i64) -> IndexExpr {
    match coeff {
        0 => IndexExpr::Const(0),
        1 => IndexExpr::LoopVar(loop_var_id),
        _ => IndexExpr::Mul(
            Box::new(IndexExpr::Const(coeff)),
            Box::new(IndexExpr::LoopVar(loop_var_id)),
        ),
    }
}

/// Per-slot index parameters used for loop subscript rewriting.
#[derive(Debug, Clone, Copy)]
struct SlotIndex {
    /// Linear shift applied per iteration.
    delta: i64,
}

/// Transform loop subscripts using slot provenance.
fn transform_loop_subscripts(
    stmts: Vec<Stmt>,
    loop_var_id: usize,
    slot_indices: &HashMap<SlotId, SlotIndex>,
    value_slots: &HashMap<ValueId, SlotId>,
    loop_carried_value_ids: &HashSet<ValueId>,
    produced_value_ids: &HashSet<ValueId>,
    produced_stride: i64,
) -> Vec<Stmt> {
    stmts
        .into_iter()
        .map(|stmt| {
            transform_stmt_loop_subscripts(
                stmt,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            )
        })
        .collect()
}

/// Rewrite a single statement using slot-based subscript adjustments.
fn transform_stmt_loop_subscripts(
    stmt: Stmt,
    loop_var_id: usize,
    slot_indices: &HashMap<SlotId, SlotIndex>,
    value_slots: &HashMap<ValueId, SlotId>,
    loop_carried_value_ids: &HashSet<ValueId>,
    produced_value_ids: &HashSet<ValueId>,
    produced_stride: i64,
) -> Stmt {
    match stmt {
        Stmt::Assign { dest, expr } => Stmt::Assign {
            dest: transform_var_loop_subscripts(
                dest,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            ),
            expr: transform_expr_loop_subscripts(
                expr,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            ),
        },
        Stmt::Repeat {
            loop_var,
            loop_count,
            body,
            phis,
        } => Stmt::Repeat {
            loop_var,
            loop_count,
            body: transform_loop_subscripts(
                body,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            ),
            phis: phis
                .into_iter()
                .map(|phi| {
                    transform_loop_phi_subscripts(
                        phi,
                        loop_var_id,
                        slot_indices,
                        value_slots,
                        loop_carried_value_ids,
                        produced_value_ids,
                        produced_stride,
                    )
                })
                .collect(),
        },
        Stmt::If {
            cond,
            then_body,
            else_body,
            phis,
        } => Stmt::If {
            cond: transform_expr_loop_subscripts(
                cond,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            ),
            then_body: transform_loop_subscripts(
                then_body,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            ),
            else_body: transform_loop_subscripts(
                else_body,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            ),
            phis: phis
                .into_iter()
                .map(|phi| IfPhi {
                    dest: transform_var_loop_subscripts(
                        phi.dest,
                        loop_var_id,
                        slot_indices,
                        value_slots,
                        loop_carried_value_ids,
                        produced_value_ids,
                        produced_stride,
                    ),
                    then_var: transform_var_loop_subscripts(
                        phi.then_var,
                        loop_var_id,
                        slot_indices,
                        value_slots,
                        loop_carried_value_ids,
                        produced_value_ids,
                        produced_stride,
                    ),
                    else_var: transform_var_loop_subscripts(
                        phi.else_var,
                        loop_var_id,
                        slot_indices,
                        value_slots,
                        loop_carried_value_ids,
                        produced_value_ids,
                        produced_stride,
                    ),
                })
                .collect(),
        },
        Stmt::While { cond, body, phis } => Stmt::While {
            cond: transform_expr_loop_subscripts(
                cond,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            ),
            body: transform_loop_subscripts(
                body,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            ),
            phis: phis
                .into_iter()
                .map(|phi| {
                    transform_loop_phi_subscripts(
                        phi,
                        loop_var_id,
                        slot_indices,
                        value_slots,
                        loop_carried_value_ids,
                        produced_value_ids,
                        produced_stride,
                    )
                })
                .collect(),
        },
        Stmt::Return(vars) => Stmt::Return(
            vars.into_iter()
                .map(|v| {
                    transform_var_loop_subscripts(
                        v,
                        loop_var_id,
                        slot_indices,
                        value_slots,
                        loop_carried_value_ids,
                        produced_value_ids,
                        produced_stride,
                    )
                })
                .collect(),
        ),
        other => other,
    }
}

/// Rewrite a loop phi node using slot-based subscript adjustments.
fn transform_loop_phi_subscripts(
    phi: LoopPhi,
    loop_var_id: usize,
    slot_indices: &HashMap<SlotId, SlotIndex>,
    value_slots: &HashMap<ValueId, SlotId>,
    loop_carried_value_ids: &HashSet<ValueId>,
    produced_value_ids: &HashSet<ValueId>,
    produced_stride: i64,
) -> LoopPhi {
    LoopPhi {
        dest: transform_var_loop_subscripts(
            phi.dest,
            loop_var_id,
            slot_indices,
            value_slots,
            loop_carried_value_ids,
            produced_value_ids,
            produced_stride,
        ),
        init: transform_var_loop_subscripts(
            phi.init,
            loop_var_id,
            slot_indices,
            value_slots,
            loop_carried_value_ids,
            produced_value_ids,
            produced_stride,
        ),
        step: transform_var_loop_subscripts(
            phi.step,
            loop_var_id,
            slot_indices,
            value_slots,
            loop_carried_value_ids,
            produced_value_ids,
            produced_stride,
        ),
    }
}

/// Rewrite a variable subscript using the slot index mapping.
fn transform_var_loop_subscripts(
    var: Var,
    loop_var_id: usize,
    slot_indices: &HashMap<SlotId, SlotIndex>,
    value_slots: &HashMap<ValueId, SlotId>,
    loop_carried_value_ids: &HashSet<ValueId>,
    produced_value_ids: &HashSet<ValueId>,
    produced_stride: i64,
) -> Var {
    let value_id = match var.base.value_id() {
        Some(id) => id,
        None => return var,
    };
    if loop_carried_value_ids.contains(&value_id) {
        return var;
    }
    let slot_id = value_slots.get(&value_id).copied();
    let slot_delta = slot_id
        .and_then(|slot_id| slot_indices.get(&slot_id))
        .map(|index| index.delta)
        .unwrap_or(0);
    let loop_delta = if produced_value_ids.contains(&value_id) {
        produced_stride
    } else {
        slot_delta
    };
    if loop_delta == 0 {
        return var;
    }

    let loop_adjustment = loop_term(loop_var_id, loop_delta);
    let new_subscript = add_index_exprs(var.subscript.clone(), loop_adjustment);
    var.with_subscript(new_subscript)
}

/// Rewrite expression variables using the slot index mapping.
fn transform_expr_loop_subscripts(
    expr: Expr,
    loop_var_id: usize,
    slot_indices: &HashMap<SlotId, SlotIndex>,
    value_slots: &HashMap<ValueId, SlotId>,
    loop_carried_value_ids: &HashSet<ValueId>,
    produced_value_ids: &HashSet<ValueId>,
    produced_stride: i64,
) -> Expr {
    match expr {
        Expr::Var(v) => Expr::Var(transform_var_loop_subscripts(
            v,
            loop_var_id,
            slot_indices,
            value_slots,
            loop_carried_value_ids,
            produced_value_ids,
            produced_stride,
        )),
        Expr::Binary(op, lhs, rhs) => Expr::Binary(
            op,
            Box::new(transform_expr_loop_subscripts(
                *lhs,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            )),
            Box::new(transform_expr_loop_subscripts(
                *rhs,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            )),
        ),
        Expr::Unary(op, inner) => Expr::Unary(
            op,
            Box::new(transform_expr_loop_subscripts(
                *inner,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            )),
        ),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => Expr::Ternary {
            cond: Box::new(transform_expr_loop_subscripts(
                *cond,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            )),
            then_expr: Box::new(transform_expr_loop_subscripts(
                *then_expr,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            )),
            else_expr: Box::new(transform_expr_loop_subscripts(
                *else_expr,
                loop_var_id,
                slot_indices,
                value_slots,
                loop_carried_value_ids,
                produced_value_ids,
                produced_stride,
            )),
        },
        other => other,
    }
}

/// Adjust the constant term of an index expression while preserving loop terms.
#[allow(dead_code)]
fn adjust_subscript_base(expr: IndexExpr, new_base: i64) -> IndexExpr {
    let current = constant_term(&expr);
    let delta = new_base - current;
    add_index_exprs(expr, IndexExpr::Const(delta))
}

/// Extract the constant term from a linear index expression.
#[allow(dead_code)]
fn constant_term(expr: &IndexExpr) -> i64 {
    match expr {
        IndexExpr::Const(value) => *value,
        IndexExpr::LoopVar(_) => 0,
        IndexExpr::Add(lhs, rhs) => constant_term(lhs) + constant_term(rhs),
        IndexExpr::Mul(lhs, rhs) => match (&**lhs, &**rhs) {
            (IndexExpr::Const(a), IndexExpr::Const(b)) => a * b,
            _ => 0,
        },
    }
}

/// Identify entry values that must be treated as loop inputs.
fn collect_loop_input_ids(
    entry_entries: &[StackEntry],
    exit_entries: &[StackEntry],
) -> HashSet<ValueId> {
    let exit_slots: HashSet<SlotId> = exit_entries.iter().map(|entry| entry.slot_id).collect();
    entry_entries
        .iter()
        .filter(|entry| !exit_slots.contains(&entry.slot_id))
        .filter_map(|entry| entry.var.base.value_id())
        .collect()
}

/// Build repeat-loop phis by matching entry and exit slot identities.
fn collect_repeat_phis_by_slot(
    entry_entries: &[StackEntry],
    exit_entries: &[StackEntry],
    stack: &mut SymbolicStack,
) -> (Vec<LoopPhi>, HashMap<SlotId, Var>, HashSet<ValueId>) {
    let mut entry_map = HashMap::new();
    for entry in entry_entries {
        entry_map.insert(entry.slot_id, entry.var.clone());
    }
    let mut phis = Vec::new();
    let mut loop_carried_dests = HashMap::new();
    let mut loop_carried_ids = HashSet::new();
    for exit in exit_entries {
        if let Some(init) = entry_map.get(&exit.slot_id) {
            if init.base != exit.var.base {
                let dest = stack.fresh_like(init);
                stack.register_value_slot_for_var(&dest, exit.slot_id);
                phis.push(LoopPhi {
                    dest: dest.clone(),
                    init: init.clone(),
                    step: exit.var.clone(),
                });
                loop_carried_dests.insert(exit.slot_id, dest);
                if let Some(id) = init.base.value_id() {
                    loop_carried_ids.insert(id);
                }
                if let Some(id) = exit.var.base.value_id() {
                    loop_carried_ids.insert(id);
                }
            }
        }
    }
    for dest in loop_carried_dests.values() {
        if let Some(id) = dest.base.value_id() {
            loop_carried_ids.insert(id);
        }
    }
    (phis, loop_carried_dests, loop_carried_ids)
}

/// Identify values defined in the loop body that correspond to produced slots.
fn collect_produced_value_ids(
    entry_entries: &[StackEntry],
    exit_entries: &[StackEntry],
    body_stmts: &[Stmt],
    value_slots: &HashMap<ValueId, SlotId>,
) -> HashSet<ValueId> {
    let entry_slots: HashSet<SlotId> = entry_entries.iter().map(|entry| entry.slot_id).collect();
    let exit_slots: HashSet<SlotId> = exit_entries.iter().map(|entry| entry.slot_id).collect();
    let produced_slots: HashSet<SlotId> = exit_slots
        .difference(&entry_slots)
        .copied()
        .collect();

    let defined_ids = collect_defined_value_ids(body_stmts);
    defined_ids
        .into_iter()
        .filter(|id| {
            value_slots
                .get(id)
                .map(|slot_id| produced_slots.contains(slot_id))
                .unwrap_or(false)
        })
        .collect()
}

/// Identify slots that are newly produced by a repeat-loop iteration.
fn collect_produced_slot_ids(
    entry_entries: &[StackEntry],
    exit_entries: &[StackEntry],
) -> HashSet<SlotId> {
    let entry_slots: HashSet<SlotId> = entry_entries.iter().map(|entry| entry.slot_id).collect();
    let exit_slots: HashSet<SlotId> = exit_entries.iter().map(|entry| entry.slot_id).collect();
    exit_slots.difference(&entry_slots).copied().collect()
}

/// Collect value identifiers defined within a statement list.
fn collect_defined_value_ids(stmts: &[Stmt]) -> HashSet<ValueId> {
    let mut defined = HashSet::new();
    for stmt in stmts {
        collect_defined_value_ids_stmt(stmt, &mut defined);
    }
    defined
}

/// Collect value identifiers defined in a single statement.
fn collect_defined_value_ids_stmt(stmt: &Stmt, defined: &mut HashSet<ValueId>) {
    match stmt {
        Stmt::Assign { dest, .. } => record_defined_id(dest, defined),
        Stmt::MemLoad(load) => {
            for v in &load.outputs {
                record_defined_id(v, defined);
            }
        }
        Stmt::AdvLoad(load) => {
            for v in &load.outputs {
                record_defined_id(v, defined);
            }
        }
        Stmt::LocalLoad(load) => {
            for v in &load.outputs {
                record_defined_id(v, defined);
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in &call.results {
                record_defined_id(v, defined);
            }
        }
        Stmt::DynCall { results, .. } => {
            for v in results {
                record_defined_id(v, defined);
            }
        }
        Stmt::Intrinsic(intrinsic) => {
            for v in &intrinsic.results {
                record_defined_id(v, defined);
            }
        }
        Stmt::Repeat { body, phis, .. } => {
            for phi in phis {
                record_defined_id(&phi.dest, defined);
            }
            for stmt in body {
                collect_defined_value_ids_stmt(stmt, defined);
            }
        }
        Stmt::If {
            then_body,
            else_body,
            phis,
            ..
        } => {
            for phi in phis {
                record_defined_id(&phi.dest, defined);
            }
            for stmt in then_body {
                collect_defined_value_ids_stmt(stmt, defined);
            }
            for stmt in else_body {
                collect_defined_value_ids_stmt(stmt, defined);
            }
        }
        Stmt::While { body, phis, .. } => {
            for phi in phis {
                record_defined_id(&phi.dest, defined);
            }
            for stmt in body {
                collect_defined_value_ids_stmt(stmt, defined);
            }
        }
        Stmt::MemStore(_)
        | Stmt::AdvStore(_)
        | Stmt::LocalStore(_)
        | Stmt::LocalStoreW(_)
        | Stmt::Return(_) => {}
    }
}

/// Record a value identifier from a variable definition.
fn record_defined_id(var: &Var, defined: &mut HashSet<ValueId>) {
    if let Some(id) = var.base.value_id() {
        defined.insert(id);
    }
}

/// Compute slot indices for loop subscripts, validating linear movement.
fn compute_slot_indices(
    entry_entries: &[StackEntry],
    exit_entries: &[StackEntry],
    exit2_slots: Option<&[SlotId]>,
    loop_count: usize,
) -> LiftingResult<HashMap<SlotId, SlotIndex>> {
    let entry_pos = slot_positions(entry_entries);
    let exit_pos = slot_positions(exit_entries);
    let exit2_pos = exit2_slots.map(slot_positions_from_ids);

    let entry_slots: HashSet<SlotId> = entry_entries.iter().map(|entry| entry.slot_id).collect();
    let exit_slots: HashSet<SlotId> = exit_entries.iter().map(|entry| entry.slot_id).collect();
    let consumed_stride = entry_slots
        .iter()
        .filter(|slot| !exit_slots.contains(slot))
        .count() as i64;

    let mut slot_indices = HashMap::new();
    for entry in entry_entries {
        if let Some(exit_idx) = exit_pos.get(&entry.slot_id) {
            let delta = if let Some(exit2_pos) = &exit2_pos {
                if let Some(next) = exit2_pos.get(&entry.slot_id) {
                    let base = *entry_pos.get(&entry.slot_id).expect("entry slot");
                    let delta1 = *exit_idx - base;
                    let delta2 = *next - *exit_idx;
                    if loop_count > 1 && delta1 != delta2 {
                        return Err(LiftingError::UnsupportedRepeatPattern(
                            "repeat loop permutes stack positions across iterations".to_string(),
                        ));
                    }
                    delta1
                } else {
                    -consumed_stride
                }
            } else {
                -consumed_stride
            };
            slot_indices.insert(entry.slot_id, SlotIndex { delta });
        } else {
            slot_indices.insert(entry.slot_id, SlotIndex { delta: -consumed_stride });
        }
    }

    for exit in exit_entries {
        if entry_slots.contains(&exit.slot_id) {
            continue;
        }
        let delta = if let Some(exit2_pos) = &exit2_pos {
            if let Some(next) = exit2_pos.get(&exit.slot_id) {
                let base = *exit_pos.get(&exit.slot_id).expect("exit slot");
                *next - base
            } else if loop_count > 1 {
                return Err(LiftingError::UnsupportedRepeatPattern(
                    "repeat loop does not reach a steady stack layout".to_string(),
                ));
            } else {
                0
            }
        } else {
            0
        };
        slot_indices.insert(exit.slot_id, SlotIndex { delta });
    }

    Ok(slot_indices)
}

/// Map slot identifiers to their stack positions.
fn slot_positions(entries: &[StackEntry]) -> HashMap<SlotId, i64> {
    entries
        .iter()
        .enumerate()
        .map(|(idx, entry)| (entry.slot_id, idx as i64))
        .collect()
}

/// Map slot identifiers to positions from an ordered list.
fn slot_positions_from_ids(ids: &[SlotId]) -> HashMap<SlotId, i64> {
    ids.iter()
        .enumerate()
        .map(|(idx, slot_id)| (*slot_id, idx as i64))
        .collect()
}

/// Simulate the stack slot layout after one repeat-loop iteration.
fn simulate_repeat_slots(
    body: &Block,
    entry_entries: &[StackEntry],
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<Vec<SlotId>> {
    let entry_slots = entry_entries
        .iter()
        .map(|entry| entry.slot_id)
        .collect::<Vec<_>>();
    simulate_repeat_slots_from_ids(body, &entry_slots, module_path, sigs)
}

/// Simulate the stack slot layout after one iteration using slot identifiers.
fn simulate_repeat_slots_from_ids(
    body: &Block,
    entry_slots: &[SlotId],
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<Vec<SlotId>> {
    let mut stack = SlotStack::new(entry_slots);
    simulate_block_slots(body, &mut stack, module_path, sigs)?;
    Ok(stack.into_slots())
}

/// Update the stack after a repeat loop using slot-based simulation.
fn update_stack_after_repeat(
    count: usize,
    body: &Block,
    stack: &mut SymbolicStack,
    exit_entries: &[StackEntry],
    loop_carried_dests: &HashMap<SlotId, Var>,
    produced_slots: &HashSet<SlotId>,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<()> {
    if count <= 1 {
        return Ok(());
    }

    let mut fresh_slots = HashSet::new();
    let mut slot_vars: HashMap<SlotId, Var> = exit_entries
        .iter()
        .map(|entry| {
            let var = if produced_slots.contains(&entry.slot_id) {
                let fresh = stack.fresh_var(0);
                fresh_slots.insert(entry.slot_id);
                fresh
            } else {
                loop_carried_dests
                    .get(&entry.slot_id)
                    .cloned()
                    .unwrap_or_else(|| entry.var.clone())
            };
            (entry.slot_id, var)
        })
        .collect();

    let loop_carried_slots: HashSet<SlotId> = loop_carried_dests.keys().copied().collect();
    let mut tagged_stack = TaggedSlotStack::new(
        &exit_entries
            .iter()
            .map(|entry| entry.slot_id)
            .collect::<Vec<_>>(),
        &loop_carried_slots,
    );
    let mut known_slots: HashSet<SlotId> = slot_vars.keys().copied().collect();

    for _ in 1..count {
        simulate_block_tags(body, &mut tagged_stack, module_path, sigs)?;
        for slot_id in tagged_stack.slots() {
            if !known_slots.contains(slot_id) {
                let var = stack.fresh_var(0);
                slot_vars.insert(*slot_id, var);
                known_slots.insert(*slot_id);
                fresh_slots.insert(*slot_id);
            }
        }
    }

    let mut final_entries = VecDeque::with_capacity(tagged_stack.slots().len());
    for (idx, slot_id) in tagged_stack.slots().iter().enumerate() {
        let tag_set = tagged_stack.tags_for(slot_id);
        if tag_set.len() > 1 {
            return Err(LiftingError::UnsupportedRepeatPattern(
                "repeat loop merges multiple loop-carried values".to_string(),
            ));
        }
        let var = if let Some(tag) = tag_set.iter().next() {
            loop_carried_dests.get(tag).cloned().ok_or_else(|| {
                LiftingError::UnsupportedRepeatPattern(
                    "repeat loop produced unknown loop-carried value".to_string(),
                )
            })?
        } else {
            slot_vars
                .get(slot_id)
                .cloned()
                .expect("slot variable must exist")
        };
        if fresh_slots.contains(slot_id) {
            let adjusted_var = Var {
                base: var.base.clone(),
                stack_depth: idx,
                subscript: IndexExpr::Const(idx as i64),
            };
            final_entries.push_back(StackEntry::new(adjusted_var, *slot_id));
        } else {
            final_entries.push_back(StackEntry::new(var, *slot_id));
        }
    }

    stack.set_entries(final_entries);
    Ok(())
}
/// Simulate a block of operations on the slot stack.
fn simulate_block_slots(
    block: &Block,
    stack: &mut SlotStack,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<()> {
    for op in block.iter() {
        simulate_op_slots(op, stack, module_path, sigs)?;
    }
    Ok(())
}

/// Simulate a single operation on the slot stack.
fn simulate_op_slots(
    op: &Op,
    stack: &mut SlotStack,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<()> {
    match op {
        Op::Inst(inst) => simulate_inst_slots(inst.inner(), stack, module_path, sigs),
        Op::If {
            then_blk, else_blk, ..
        } => {
            let mut then_stack = stack.clone();
            let mut else_stack = stack.clone();
            simulate_block_slots(then_blk, &mut then_stack, module_path, sigs)?;
            simulate_block_slots(else_blk, &mut else_stack, module_path, sigs)?;
            if then_stack.slots != else_stack.slots {
                return Err(LiftingError::UnbalancedIf);
            }
            stack.slots = then_stack.slots;
            Ok(())
        }
        Op::Repeat { count, body, .. } => {
            for _ in 0..*count {
                simulate_block_slots(body, stack, module_path, sigs)?;
            }
            Ok(())
        }
        Op::While { .. } => Err(LiftingError::UnsupportedRepeatPattern(
            "repeat loop contains a while loop".to_string(),
        )),
    }
}

/// Simulate a single instruction's stack effect for slot tracking.
fn simulate_inst_slots(
    inst: &Instruction,
    stack: &mut SlotStack,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<()> {
    match inst {
        Instruction::Swap1 => stack.swap(1),
        Instruction::Swap2 => stack.swap(2),
        Instruction::Swap3 => stack.swap(3),
        Instruction::Swap4 => stack.swap(4),
        Instruction::Swap5 => stack.swap(5),
        Instruction::Swap6 => stack.swap(6),
        Instruction::Swap7 => stack.swap(7),
        Instruction::Swap8 => stack.swap(8),
        Instruction::Swap9 => stack.swap(9),
        Instruction::Swap10 => stack.swap(10),
        Instruction::Swap11 => stack.swap(11),
        Instruction::Swap12 => stack.swap(12),
        Instruction::Swap13 => stack.swap(13),
        Instruction::Swap14 => stack.swap(14),
        Instruction::Swap15 => stack.swap(15),
        Instruction::SwapW1 => stack.swapw(1),
        Instruction::SwapW2 => stack.swapw(2),
        Instruction::SwapW3 => stack.swapw(3),
        Instruction::MovUp2 => stack.movup(2),
        Instruction::MovUp3 => stack.movup(3),
        Instruction::MovUp4 => stack.movup(4),
        Instruction::MovUp5 => stack.movup(5),
        Instruction::MovUp6 => stack.movup(6),
        Instruction::MovUp7 => stack.movup(7),
        Instruction::MovUp8 => stack.movup(8),
        Instruction::MovUp9 => stack.movup(9),
        Instruction::MovUp10 => stack.movup(10),
        Instruction::MovUp11 => stack.movup(11),
        Instruction::MovUp12 => stack.movup(12),
        Instruction::MovUp13 => stack.movup(13),
        Instruction::MovUp14 => stack.movup(14),
        Instruction::MovUp15 => stack.movup(15),
        Instruction::MovDn2 => stack.movdn(2),
        Instruction::MovDn3 => stack.movdn(3),
        Instruction::MovDn4 => stack.movdn(4),
        Instruction::MovDn5 => stack.movdn(5),
        Instruction::MovDn6 => stack.movdn(6),
        Instruction::MovDn7 => stack.movdn(7),
        Instruction::MovDn8 => stack.movdn(8),
        Instruction::MovDn9 => stack.movdn(9),
        Instruction::MovDn10 => stack.movdn(10),
        Instruction::MovDn11 => stack.movdn(11),
        Instruction::MovDn12 => stack.movdn(12),
        Instruction::MovDn13 => stack.movdn(13),
        Instruction::MovDn14 => stack.movdn(14),
        Instruction::MovDn15 => stack.movdn(15),
        Instruction::Reversew => stack.reversew(),
        _ => {
            let effect = inst::effect_for_inst(inst, module_path, sigs)?;
            let (pops, pushes, required_depth) = match effect {
                StackEffect::Known {
                    pops,
                    pushes,
                    required_depth,
                } => (pops, pushes, required_depth),
                StackEffect::Unknown => (0, 0, 0),
            };
            stack.apply_effect(pops, pushes, required_depth);
        }
    }
    Ok(())
}

/// Lightweight slot-only stack used for repeat-loop simulation.
#[derive(Debug, Clone)]
struct SlotStack {
    slots: Vec<SlotId>,
    next_slot: u64,
}

impl SlotStack {
    /// Create a slot stack initialized with the given entries.
    fn new(entry_slots: &[SlotId]) -> Self {
        let next_slot = entry_slots
            .iter()
            .map(|slot| slot.as_u64())
            .max()
            .map(|value| value + 1)
            .unwrap_or(0);
        Self {
            slots: entry_slots.to_vec(),
            next_slot,
        }
    }

    /// Ensure the stack has at least the required depth by pushing new slots.
    fn ensure_depth(&mut self, required_depth: usize) {
        while self.slots.len() < required_depth {
            let slot = self.alloc_slot();
            self.slots.push(slot);
        }
    }

    /// Allocate a fresh slot identifier.
    fn alloc_slot(&mut self) -> SlotId {
        let id = self.next_slot;
        self.next_slot += 1;
        SlotId::new(id)
    }

    /// Pop a slot identifier from the top of the stack.
    fn pop(&mut self) -> SlotId {
        self.slots.pop().expect("slot stack underflow")
    }

    /// Swap the top slot with the slot at the given depth.
    fn swap(&mut self, depth: usize) {
        let len = self.slots.len();
        if depth > 0 && depth < len {
            let top_idx = len - 1;
            let other_idx = len - 1 - depth;
            self.slots.swap(top_idx, other_idx);
        }
    }

    /// Swap the top word with the word below it.
    fn swapw(&mut self, word_index: usize) {
        if word_index == 0 {
            return;
        }
        let len = self.slots.len();
        let offset = word_index.saturating_mul(4);
        if offset + 4 > len {
            return;
        }
        for i in 0..4 {
            let top_idx = len - 1 - i;
            let other_idx = len - 1 - offset - i;
            self.slots.swap(top_idx, other_idx);
        }
    }

    /// Reverse the order of the top word.
    fn reversew(&mut self) {
        let len = self.slots.len();
        if len < 4 {
            return;
        }
        self.slots.swap(len - 4, len - 1);
        self.slots.swap(len - 3, len - 2);
    }

    /// Move the slot at the given depth to the top.
    fn movup(&mut self, depth: usize) {
        let len = self.slots.len();
        if depth > 0 && depth < len {
            let idx = len - 1 - depth;
            let slot = self.slots.remove(idx);
            self.slots.push(slot);
        }
    }

    /// Move the top slot down to the given depth.
    fn movdn(&mut self, depth: usize) {
        let len = self.slots.len();
        if depth > 0 && depth < len {
            let slot = self.slots.pop().expect("slot stack underflow");
            let idx = len - 1 - depth;
            self.slots.insert(idx, slot);
        }
    }

    /// Apply a stack effect to the slot stack, reusing slots where possible.
    fn apply_effect(&mut self, pops: usize, pushes: usize, required_depth: usize) {
        self.ensure_depth(required_depth);
        let mut popped = Vec::with_capacity(pops);
        for _ in 0..pops {
            popped.push(self.pop());
        }
        let mut reuse = popped.into_iter().rev().collect::<Vec<_>>();
        let reuse_count = reuse.len().min(pushes);
        for slot in reuse.drain(0..reuse_count) {
            self.slots.push(slot);
        }
        for _ in reuse_count..pushes {
            let slot = self.alloc_slot();
            self.slots.push(slot);
        }
    }

    /// Return the stack contents from bottom to top.
    fn into_slots(self) -> Vec<SlotId> {
        self.slots
    }
}

/// Slot stack with loop-carried tag tracking for repeat loops.
#[derive(Debug, Clone)]
struct TaggedSlotStack {
    slots: Vec<SlotId>,
    next_slot: u64,
    tags: HashMap<SlotId, HashSet<SlotId>>,
}

impl TaggedSlotStack {
    /// Create a tagged slot stack initialized with the given slots.
    fn new(entry_slots: &[SlotId], loop_carried: &HashSet<SlotId>) -> Self {
        let next_slot = entry_slots
            .iter()
            .map(|slot| slot.as_u64())
            .max()
            .map(|value| value + 1)
            .unwrap_or(0);
        let mut tags = HashMap::new();
        for slot in entry_slots {
            let mut set = HashSet::new();
            if loop_carried.contains(slot) {
                set.insert(*slot);
            }
            tags.insert(*slot, set);
        }
        Self {
            slots: entry_slots.to_vec(),
            next_slot,
            tags,
        }
    }

    /// Return the current slot order.
    fn slots(&self) -> &[SlotId] {
        &self.slots
    }

    /// Return tags for a slot identifier.
    fn tags_for(&self, slot_id: &SlotId) -> HashSet<SlotId> {
        self.tags.get(slot_id).cloned().unwrap_or_default()
    }

    /// Ensure the stack has at least the required depth by pushing new slots.
    fn ensure_depth(&mut self, required_depth: usize) {
        while self.slots.len() < required_depth {
            let slot = self.alloc_slot();
            self.tags.entry(slot).or_default();
            self.slots.push(slot);
        }
    }

    /// Allocate a fresh slot identifier.
    fn alloc_slot(&mut self) -> SlotId {
        let id = self.next_slot;
        self.next_slot += 1;
        SlotId::new(id)
    }

    /// Pop a slot identifier from the top of the stack.
    fn pop(&mut self) -> SlotId {
        self.slots.pop().expect("slot stack underflow")
    }

    /// Swap the top slot with the slot at the given depth.
    fn swap(&mut self, depth: usize) {
        let len = self.slots.len();
        if depth > 0 && depth < len {
            let top_idx = len - 1;
            let other_idx = len - 1 - depth;
            self.slots.swap(top_idx, other_idx);
        }
    }

    /// Swap the top word with the word below it.
    fn swapw(&mut self, word_index: usize) {
        if word_index == 0 {
            return;
        }
        let len = self.slots.len();
        let offset = word_index.saturating_mul(4);
        if offset + 4 > len {
            return;
        }
        for i in 0..4 {
            let top_idx = len - 1 - i;
            let other_idx = len - 1 - offset - i;
            self.slots.swap(top_idx, other_idx);
        }
    }

    /// Reverse the order of the top word.
    fn reversew(&mut self) {
        let len = self.slots.len();
        if len < 4 {
            return;
        }
        self.slots.swap(len - 4, len - 1);
        self.slots.swap(len - 3, len - 2);
    }

    /// Move the slot at the given depth to the top.
    fn movup(&mut self, depth: usize) {
        let len = self.slots.len();
        if depth > 0 && depth < len {
            let idx = len - 1 - depth;
            let slot = self.slots.remove(idx);
            self.slots.push(slot);
        }
    }

    /// Move the top slot down to the given depth.
    fn movdn(&mut self, depth: usize) {
        let len = self.slots.len();
        if depth > 0 && depth < len {
            let slot = self.slots.pop().expect("slot stack underflow");
            let idx = len - 1 - depth;
            self.slots.insert(idx, slot);
        }
    }

    /// Apply a stack effect to the tagged slot stack.
    fn apply_effect(&mut self, pops: usize, pushes: usize, required_depth: usize) {
        self.ensure_depth(required_depth);
        let mut popped = Vec::with_capacity(pops);
        let mut popped_tags = Vec::with_capacity(pops);
        for _ in 0..pops {
            let slot = self.pop();
            let tags = self.tags.remove(&slot).unwrap_or_default();
            popped.push(slot);
            popped_tags.push(tags);
        }
        let mut merged_tags = HashSet::new();
        for tags in popped_tags {
            merged_tags.extend(tags);
        }
        let mut reuse = popped.into_iter().rev().collect::<Vec<_>>();
        let reuse_count = reuse.len().min(pushes);
        for slot in reuse.drain(0..reuse_count) {
            self.tags.insert(slot, merged_tags.clone());
            self.slots.push(slot);
        }
        for _ in reuse_count..pushes {
            let slot = self.alloc_slot();
            self.tags.entry(slot).or_default();
            self.slots.push(slot);
        }
    }
}

/// Simulate a block of operations on the tagged slot stack.
fn simulate_block_tags(
    block: &Block,
    stack: &mut TaggedSlotStack,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<()> {
    for op in block.iter() {
        simulate_op_tags(op, stack, module_path, sigs)?;
    }
    Ok(())
}

/// Simulate a single operation on the tagged slot stack.
fn simulate_op_tags(
    op: &Op,
    stack: &mut TaggedSlotStack,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<()> {
    match op {
        Op::Inst(inst) => simulate_inst_tags(inst.inner(), stack, module_path, sigs),
        Op::If {
            then_blk, else_blk, ..
        } => {
            let mut then_stack = stack.clone();
            let mut else_stack = stack.clone();
            simulate_block_tags(then_blk, &mut then_stack, module_path, sigs)?;
            simulate_block_tags(else_blk, &mut else_stack, module_path, sigs)?;
            if then_stack.slots != else_stack.slots || then_stack.tags != else_stack.tags {
                return Err(LiftingError::UnsupportedRepeatPattern(
                    "repeat loop contains if with incompatible branches".to_string(),
                ));
            }
            *stack = then_stack;
            Ok(())
        }
        Op::Repeat { count, body, .. } => {
            for _ in 0..*count {
                simulate_block_tags(body, stack, module_path, sigs)?;
            }
            Ok(())
        }
        Op::While { .. } => Err(LiftingError::UnsupportedRepeatPattern(
            "repeat loop contains a while loop".to_string(),
        )),
    }
}

/// Simulate a single instruction's stack effect for tagged slot tracking.
fn simulate_inst_tags(
    inst: &Instruction,
    stack: &mut TaggedSlotStack,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<()> {
    match inst {
        Instruction::Swap1 => stack.swap(1),
        Instruction::Swap2 => stack.swap(2),
        Instruction::Swap3 => stack.swap(3),
        Instruction::Swap4 => stack.swap(4),
        Instruction::Swap5 => stack.swap(5),
        Instruction::Swap6 => stack.swap(6),
        Instruction::Swap7 => stack.swap(7),
        Instruction::Swap8 => stack.swap(8),
        Instruction::Swap9 => stack.swap(9),
        Instruction::Swap10 => stack.swap(10),
        Instruction::Swap11 => stack.swap(11),
        Instruction::Swap12 => stack.swap(12),
        Instruction::Swap13 => stack.swap(13),
        Instruction::Swap14 => stack.swap(14),
        Instruction::Swap15 => stack.swap(15),
        Instruction::SwapW1 => stack.swapw(1),
        Instruction::SwapW2 => stack.swapw(2),
        Instruction::SwapW3 => stack.swapw(3),
        Instruction::MovUp2 => stack.movup(2),
        Instruction::MovUp3 => stack.movup(3),
        Instruction::MovUp4 => stack.movup(4),
        Instruction::MovUp5 => stack.movup(5),
        Instruction::MovUp6 => stack.movup(6),
        Instruction::MovUp7 => stack.movup(7),
        Instruction::MovUp8 => stack.movup(8),
        Instruction::MovUp9 => stack.movup(9),
        Instruction::MovUp10 => stack.movup(10),
        Instruction::MovUp11 => stack.movup(11),
        Instruction::MovUp12 => stack.movup(12),
        Instruction::MovUp13 => stack.movup(13),
        Instruction::MovUp14 => stack.movup(14),
        Instruction::MovUp15 => stack.movup(15),
        Instruction::MovDn2 => stack.movdn(2),
        Instruction::MovDn3 => stack.movdn(3),
        Instruction::MovDn4 => stack.movdn(4),
        Instruction::MovDn5 => stack.movdn(5),
        Instruction::MovDn6 => stack.movdn(6),
        Instruction::MovDn7 => stack.movdn(7),
        Instruction::MovDn8 => stack.movdn(8),
        Instruction::MovDn9 => stack.movdn(9),
        Instruction::MovDn10 => stack.movdn(10),
        Instruction::MovDn11 => stack.movdn(11),
        Instruction::MovDn12 => stack.movdn(12),
        Instruction::MovDn13 => stack.movdn(13),
        Instruction::MovDn14 => stack.movdn(14),
        Instruction::MovDn15 => stack.movdn(15),
        Instruction::Reversew => stack.reversew(),
        _ => {
            let effect = inst::effect_for_inst(inst, module_path, sigs)?;
            let (pops, pushes, required_depth) = match effect {
                StackEffect::Known {
                    pops,
                    pushes,
                    required_depth,
                } => (pops, pushes, required_depth),
                StackEffect::Unknown => (0, 0, 0),
            };
            stack.apply_effect(pops, pushes, required_depth);
        }
    }
    Ok(())
}

/// Rewrite entry-stack references inside consuming loops to use loop-input bases.
fn transform_loop_input_bases(
    stmts: Vec<Stmt>,
    entry_value_ids: &HashSet<ValueId>,
    loop_depth: usize,
) -> Vec<Stmt> {
    stmts
        .into_iter()
        .map(|stmt| transform_stmt_loop_input(stmt, entry_value_ids, loop_depth))
        .collect()
}

/// Rewrite variables inside a statement to use loop-input bases when needed.
fn transform_stmt_loop_input(
    stmt: Stmt,
    entry_value_ids: &HashSet<ValueId>,
    loop_depth: usize,
) -> Stmt {
    match stmt {
        Stmt::Assign { dest, expr } => {
            let dest = transform_var_loop_input(dest, entry_value_ids, loop_depth);
            let expr = transform_expr_loop_input(expr, entry_value_ids, loop_depth);
            Stmt::Assign { dest, expr }
        }
        Stmt::Repeat {
            loop_var,
            loop_count,
            body,
            phis,
        } => Stmt::Repeat {
            loop_var,
            loop_count,
            body: transform_loop_input_bases(body, entry_value_ids, loop_depth),
            phis: phis
                .into_iter()
                .map(|phi| LoopPhi {
                    dest: transform_var_loop_input(phi.dest, entry_value_ids, loop_depth),
                    init: transform_var_loop_input(phi.init, entry_value_ids, loop_depth),
                    step: transform_var_loop_input(phi.step, entry_value_ids, loop_depth),
                })
                .collect(),
        },
        Stmt::If {
            cond,
            then_body,
            else_body,
            phis,
        } => Stmt::If {
            cond: transform_expr_loop_input(cond, entry_value_ids, loop_depth),
            then_body: transform_loop_input_bases(then_body, entry_value_ids, loop_depth),
            else_body: transform_loop_input_bases(else_body, entry_value_ids, loop_depth),
            phis: phis
                .into_iter()
                .map(|phi| IfPhi {
                    dest: transform_var_loop_input(phi.dest, entry_value_ids, loop_depth),
                    then_var: transform_var_loop_input(phi.then_var, entry_value_ids, loop_depth),
                    else_var: transform_var_loop_input(phi.else_var, entry_value_ids, loop_depth),
                })
                .collect(),
        },
        Stmt::While { cond, body, phis } => Stmt::While {
            cond: transform_expr_loop_input(cond, entry_value_ids, loop_depth),
            body: transform_loop_input_bases(body, entry_value_ids, loop_depth),
            phis: phis
                .into_iter()
                .map(|phi| LoopPhi {
                    dest: transform_var_loop_input(phi.dest, entry_value_ids, loop_depth),
                    init: transform_var_loop_input(phi.init, entry_value_ids, loop_depth),
                    step: transform_var_loop_input(phi.step, entry_value_ids, loop_depth),
                })
                .collect(),
        },
        Stmt::Return(vars) => Stmt::Return(
            vars.into_iter()
                .map(|v| transform_var_loop_input(v, entry_value_ids, loop_depth))
                .collect(),
        ),
        other => other,
    }
}

/// Rewrite a single variable to use a loop-input base when it refers to entry values.
fn transform_var_loop_input(
    var: Var,
    entry_value_ids: &HashSet<ValueId>,
    loop_depth: usize,
) -> Var {
    match var.base {
        VarBase::Value(id) if entry_value_ids.contains(&id) => {
            var.with_base(VarBase::LoopInput { loop_depth })
        }
        _ => var,
    }
}

/// Rewrite variables in an expression to use loop-input bases when needed.
fn transform_expr_loop_input(
    expr: Expr,
    entry_value_ids: &HashSet<ValueId>,
    loop_depth: usize,
) -> Expr {
    match expr {
        Expr::Var(v) => Expr::Var(transform_var_loop_input(v, entry_value_ids, loop_depth)),
        Expr::Binary(op, lhs, rhs) => Expr::Binary(
            op,
            Box::new(transform_expr_loop_input(*lhs, entry_value_ids, loop_depth)),
            Box::new(transform_expr_loop_input(*rhs, entry_value_ids, loop_depth)),
        ),
        Expr::Unary(op, inner) => Expr::Unary(
            op,
            Box::new(transform_expr_loop_input(*inner, entry_value_ids, loop_depth)),
        ),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => Expr::Ternary {
            cond: Box::new(transform_expr_loop_input(*cond, entry_value_ids, loop_depth)),
            then_expr: Box::new(transform_expr_loop_input(
                *then_expr,
                entry_value_ids,
                loop_depth,
            )),
            else_expr: Box::new(transform_expr_loop_input(
                *else_expr,
                entry_value_ids,
                loop_depth,
            )),
        },
        other => other,
    }
}

/// Lift a while loop construct.
///
/// We only support stack-neutral while loops.
fn lift_while(
    body: &Block,
    stack: &mut SymbolicStack,
    loop_ctx: &mut LoopContext,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftingResult<Vec<Stmt>> {
    // Pop initial condition.
    let cond_var = stack.pop();
    let cond = Expr::Var(cond_var);

    let entry_depth = stack.len();
    let entry_vars = stack.to_vec();

    // Create phi vars for the loop header and use them as the body stack.
    let mut phi_vars = Vec::with_capacity(entry_vars.len());
    for var in &entry_vars {
        phi_vars.push(stack.fresh_like(var));
    }

    let mut body_stack = stack.clone();
    body_stack.set_stack(phi_vars.clone());
    let body_stmts = lift_block(body, &mut body_stack, loop_ctx, module_path, sigs)?;

    // The body should end with pushing a condition value.
    if body_stack.is_empty() {
        return Err(LiftingError::NonNeutralWhile);
    }
    // Pop the continuation condition.
    body_stack.pop();

    // Verify that the loop body is stack-neutral.
    if body_stack.len() != entry_depth {
        return Err(LiftingError::NonNeutralWhile);
    }

    let step_vars = body_stack.to_vec();
    let mut phis = Vec::with_capacity(phi_vars.len());
    for ((dest, init), step) in phi_vars
        .iter()
        .cloned()
        .zip(entry_vars.into_iter())
        .zip(step_vars.into_iter())
    {
        phis.push(LoopPhi { dest, init, step });
    }

    // Update outer stack to the phi destinations.
    stack.set_stack(phi_vars);

    Ok(vec![Stmt::While {
        cond,
        body: body_stmts,
        phis,
    }])
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn make_var(id: u64, stack_depth: usize, sub: i64) -> Var {
        Var {
            base: VarBase::Value(ValueId::from(id)),
            stack_depth,
            subscript: IndexExpr::Const(sub),
        }
    }

    #[test]
    fn adjust_subscript_base_preserves_loop_terms() {
        fn contains_loop_var(expr: &IndexExpr) -> bool {
            match expr {
                IndexExpr::LoopVar(_) => true,
                IndexExpr::Const(_) => false,
                IndexExpr::Add(lhs, rhs) | IndexExpr::Mul(lhs, rhs) => {
                    contains_loop_var(lhs) || contains_loop_var(rhs)
                }
            }
        }

        let expr = IndexExpr::Add(
            Box::new(IndexExpr::Const(5)),
            Box::new(IndexExpr::LoopVar(0)),
        );
        let adjusted = adjust_subscript_base(expr, 2);
        assert_eq!(constant_term(&adjusted), 2);
        assert!(contains_loop_var(&adjusted));
    }

    #[test]
    fn compute_slot_indices_tracks_linear_shift() {
        let entry = vec![StackEntry::new(make_var(0, 0, 0), SlotId::new(0))];
        let exit = vec![
            StackEntry::new(make_var(1, 0, 0), SlotId::new(1)),
            StackEntry::new(make_var(0, 1, 1), SlotId::new(0)),
        ];
        let exit2_slots = vec![SlotId::new(1), SlotId::new(2), SlotId::new(0)];
        let indices = compute_slot_indices(&entry, &exit, Some(&exit2_slots), 2)
            .expect("slot index computation should succeed");
        let entry_index = indices.get(&SlotId::new(0)).expect("entry slot");
        assert_eq!(entry_index.delta, 1);
        let produced_index = indices.get(&SlotId::new(1)).expect("produced slot");
        assert_eq!(produced_index.delta, 0);
    }

    #[test]
    fn consuming_loop_rewrites_entry_values_to_loop_input() {
        let entry_id = ValueId::from(1);
        let entry_var = Var {
            base: VarBase::Value(entry_id),
            stack_depth: 0,
            subscript: IndexExpr::Const(0),
        };
        let stmt = Stmt::Assign {
            dest: entry_var.clone(),
            expr: Expr::Var(entry_var.clone()),
        };

        let mut entry_ids = HashSet::new();
        entry_ids.insert(entry_id);

        let transformed = transform_loop_input_bases(vec![stmt], &entry_ids, 0);
        match &transformed[0] {
            Stmt::Assign { dest, expr } => {
                assert!(matches!(dest.base, VarBase::LoopInput { loop_depth: 0 }));
                match expr {
                    Expr::Var(v) => {
                        assert!(matches!(v.base, VarBase::LoopInput { loop_depth: 0 }));
                    }
                    other => panic!("Expected var expr, got {other:?}"),
                }
            }
            other => panic!("Expected assign, got {other:?}"),
        }
    }
}
