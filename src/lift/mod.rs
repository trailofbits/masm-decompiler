//! Direct AST-to-IR lifting.
//!
//! This module transforms MASM AST directly into structured IR statements,
//! without an intermediate CFG representation. The approach mirrors signature
//! inference: recursive AST traversal with symbolic stack tracking.

mod inst;
mod stack;

use miden_assembly_syntax::ast::{Block, Instruction, Op, Procedure};
use std::collections::HashSet;

use crate::ir::{Expr, IfPhi, IndexExpr, LoopPhi, LoopVar, Stmt, Var, VarBase, ValueId};
use crate::signature::{ProcSignature, SignatureMap};

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
    let entry_vars = stack.to_vec();
    let entry_value_ids = collect_value_ids(&entry_vars);

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

    let exit_vars = stack.to_vec();
    let mut repeat_phis = collect_repeat_phis(&entry_vars, &exit_vars);
    let carried_entry_ids = collect_loop_carried_entry_ids(&entry_vars, &exit_vars);

    // Compute net effect per iteration.
    let delta = exit_depth as isize - entry_depth as isize;
    let stride = delta.abs() as usize;

    // Transform subscripts based on loop type.
    // Use loop_depth as the identifier for IndexExpr::LoopVar.
    let loop_depth = loop_var.loop_depth;
    let mut body_stmts = if delta > 0 {
        let defined_in_body_ids = collect_defined_value_ids(&body_stmts);
        let mut index_value_ids = defined_in_body_ids;
        index_value_ids.extend(carried_entry_ids.clone());
        repeat_phis = repeat_phis
            .into_iter()
            .map(|phi| LoopPhi {
                dest: transform_var_producing(phi.dest, loop_depth, stride, &index_value_ids),
                init: transform_var_producing(phi.init, loop_depth, stride, &index_value_ids),
                step: transform_var_producing(phi.step, loop_depth, stride, &index_value_ids),
            })
            .collect();
        // Producing loop: subscripts for indexed values = LoopVar * stride
        transform_producing_subscripts(body_stmts, loop_depth, stride, &index_value_ids)
    } else if delta < 0 {
        let defined_in_body_ids = collect_defined_value_ids(&body_stmts);
        let mut index_value_ids = defined_in_body_ids;
        index_value_ids.extend(entry_value_ids.iter().cloned());
        repeat_phis = repeat_phis
            .into_iter()
            .map(|phi| LoopPhi {
                dest: transform_var_consuming(phi.dest, loop_depth, stride, &index_value_ids),
                init: transform_var_consuming(phi.init, loop_depth, stride, &index_value_ids),
                step: transform_var_consuming(phi.step, loop_depth, stride, &index_value_ids),
            })
            .collect();
        // Consuming loop: subscripts = (stack_depth - LoopVar * stride)
        transform_consuming_subscripts(body_stmts, loop_depth, stride, &index_value_ids)
    } else {
        // Neutral loop: no indexing; use constant subscripts.
        body_stmts
    };

    if delta < 0 {
        let mut loop_input_ids = entry_value_ids.clone();
        for id in carried_entry_ids {
            loop_input_ids.remove(&id);
        }
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

    // Simulate remaining iterations for stack depth tracking.
    if delta > 0 {
        // Producing loop: each iteration adds `delta` values.
        // We already processed one iteration, simulate count-1 more.
        for _ in 1..count {
            for _ in 0..delta {
                stack.push_fresh();
            }
        }
    } else if delta < 0 {
        // Consuming loop: each iteration removes `-delta` values.
        let consume_per_iter = (-delta) as usize;
        for _ in 1..count {
            for _ in 0..consume_per_iter {
                if !stack.is_empty() {
                    stack.pop();
                }
            }
        }
    }
    // Neutral loop (delta == 0): stack unchanged after all iterations.

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

/// Transform subscripts for a producing loop.
///
/// In a producing loop, variables created at or after entry_depth have
/// iteration-dependent subscripts. The loop variable is added to any
/// existing subscript to account for nested loop effects.
fn transform_producing_subscripts(
    stmts: Vec<Stmt>,
    loop_var_id: usize,
    stride: usize,
    index_value_ids: &HashSet<ValueId>,
) -> Vec<Stmt> {
    stmts
        .into_iter()
        .map(|stmt| transform_stmt_producing(stmt, loop_var_id, stride, index_value_ids))
        .collect()
}

fn transform_stmt_producing(
    stmt: Stmt,
    loop_var_id: usize,
    stride: usize,
    index_value_ids: &HashSet<ValueId>,
) -> Stmt {
    match stmt {
        Stmt::Assign { dest, expr } => {
            let dest = transform_var_producing(dest, loop_var_id, stride, index_value_ids);
            let expr = transform_expr_producing(expr, loop_var_id, stride, index_value_ids);
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
            body: transform_producing_subscripts(body, loop_var_id, stride, index_value_ids),
            phis: phis
                .into_iter()
                .map(|phi| LoopPhi {
                    dest: transform_var_producing(phi.dest, loop_var_id, stride, index_value_ids),
                    init: transform_var_producing(phi.init, loop_var_id, stride, index_value_ids),
                    step: transform_var_producing(phi.step, loop_var_id, stride, index_value_ids),
                })
                .collect(),
        },
        Stmt::If {
            cond,
            then_body,
            else_body,
            phis,
        } => Stmt::If {
            cond: transform_expr_producing(cond, loop_var_id, stride, index_value_ids),
            then_body: transform_producing_subscripts(
                then_body,
                loop_var_id,
                stride,
                index_value_ids,
            ),
            else_body: transform_producing_subscripts(
                else_body,
                loop_var_id,
                stride,
                index_value_ids,
            ),
            phis: phis
                .into_iter()
                .map(|phi| IfPhi {
                    dest: transform_var_producing(phi.dest, loop_var_id, stride, index_value_ids),
                    then_var: transform_var_producing(
                        phi.then_var,
                        loop_var_id,
                        stride,
                        index_value_ids,
                    ),
                    else_var: transform_var_producing(
                        phi.else_var,
                        loop_var_id,
                        stride,
                        index_value_ids,
                    ),
                })
                .collect(),
        },
        Stmt::While { cond, body, phis } => Stmt::While {
            cond: transform_expr_producing(cond, loop_var_id, stride, index_value_ids),
            body: transform_producing_subscripts(body, loop_var_id, stride, index_value_ids),
            phis: phis
                .into_iter()
                .map(|phi| LoopPhi {
                    dest: transform_var_producing(phi.dest, loop_var_id, stride, index_value_ids),
                    init: transform_var_producing(phi.init, loop_var_id, stride, index_value_ids),
                    step: transform_var_producing(phi.step, loop_var_id, stride, index_value_ids),
                })
                .collect(),
        },
        Stmt::Return(vars) => Stmt::Return(
            vars.into_iter()
                .map(|v| transform_var_producing(v, loop_var_id, stride, index_value_ids))
                .collect(),
        ),
        // Other statement types pass through unchanged for now
        other => other,
    }
}

fn transform_var_producing(
    var: Var,
    loop_var_id: usize,
    stride: usize,
    index_value_ids: &HashSet<ValueId>,
) -> Var {
    if should_index_var(&var, index_value_ids) {
        let loop_var = loop_term(loop_var_id, stride as i64);
        // Add loop variable to the existing subscript
        let new_subscript = add_index_exprs(loop_var, var.subscript.clone());
        var.with_subscript(new_subscript)
    } else {
        var
    }
}

fn transform_expr_producing(
    expr: Expr,
    loop_var_id: usize,
    stride: usize,
    index_value_ids: &HashSet<ValueId>,
) -> Expr {
    match expr {
        Expr::Var(v) => Expr::Var(transform_var_producing(v, loop_var_id, stride, index_value_ids)),
        Expr::Binary(op, lhs, rhs) => Expr::Binary(
            op,
            Box::new(transform_expr_producing(*lhs, loop_var_id, stride, index_value_ids)),
            Box::new(transform_expr_producing(*rhs, loop_var_id, stride, index_value_ids)),
        ),
        Expr::Unary(op, inner) => Expr::Unary(
            op,
            Box::new(transform_expr_producing(*inner, loop_var_id, stride, index_value_ids)),
        ),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => Expr::Ternary {
            cond: Box::new(transform_expr_producing(
                *cond,
                loop_var_id,
                stride,
                index_value_ids,
            )),
            then_expr: Box::new(transform_expr_producing(
                *then_expr,
                loop_var_id,
                stride,
                index_value_ids,
            )),
            else_expr: Box::new(transform_expr_producing(
                *else_expr,
                loop_var_id,
                stride,
                index_value_ids,
            )),
        },
        other => other,
    }
}

/// Transform subscripts for a consuming loop.
///
/// In a consuming loop, all variables have iteration-dependent subscripts.
/// The loop variable is subtracted from any existing subscript to account
/// for the decreasing indices as values are consumed. For nested loops,
/// this composes with existing subscripts.
fn transform_consuming_subscripts(
    stmts: Vec<Stmt>,
    loop_var_id: usize,
    stride: usize,
    index_value_ids: &HashSet<ValueId>,
) -> Vec<Stmt> {
    stmts
        .into_iter()
        .map(|stmt| transform_stmt_consuming(stmt, loop_var_id, stride, index_value_ids))
        .collect()
}

fn transform_stmt_consuming(
    stmt: Stmt,
    loop_var_id: usize,
    stride: usize,
    index_value_ids: &HashSet<ValueId>,
) -> Stmt {
    match stmt {
        Stmt::Assign { dest, expr } => {
            let dest = transform_var_consuming(dest, loop_var_id, stride, index_value_ids);
            let expr = transform_expr_consuming(expr, loop_var_id, stride, index_value_ids);
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
            body: transform_consuming_subscripts(body, loop_var_id, stride, index_value_ids),
            phis: phis
                .into_iter()
                .map(|phi| LoopPhi {
                    dest: transform_var_consuming(phi.dest, loop_var_id, stride, index_value_ids),
                    init: transform_var_consuming(phi.init, loop_var_id, stride, index_value_ids),
                    step: transform_var_consuming(phi.step, loop_var_id, stride, index_value_ids),
                })
                .collect(),
        },
        Stmt::If {
            cond,
            then_body,
            else_body,
            phis,
        } => Stmt::If {
            cond: transform_expr_consuming(cond, loop_var_id, stride, index_value_ids),
            then_body: transform_consuming_subscripts(
                then_body,
                loop_var_id,
                stride,
                index_value_ids,
            ),
            else_body: transform_consuming_subscripts(
                else_body,
                loop_var_id,
                stride,
                index_value_ids,
            ),
            phis: phis
                .into_iter()
                .map(|phi| IfPhi {
                    dest: transform_var_consuming(phi.dest, loop_var_id, stride, index_value_ids),
                    then_var: transform_var_consuming(
                        phi.then_var,
                        loop_var_id,
                        stride,
                        index_value_ids,
                    ),
                    else_var: transform_var_consuming(
                        phi.else_var,
                        loop_var_id,
                        stride,
                        index_value_ids,
                    ),
                })
                .collect(),
        },
        Stmt::While { cond, body, phis } => Stmt::While {
            cond: transform_expr_consuming(cond, loop_var_id, stride, index_value_ids),
            body: transform_consuming_subscripts(body, loop_var_id, stride, index_value_ids),
            phis: phis
                .into_iter()
                .map(|phi| LoopPhi {
                    dest: transform_var_consuming(phi.dest, loop_var_id, stride, index_value_ids),
                    init: transform_var_consuming(phi.init, loop_var_id, stride, index_value_ids),
                    step: transform_var_consuming(phi.step, loop_var_id, stride, index_value_ids),
                })
                .collect(),
        },
        Stmt::Return(vars) => Stmt::Return(
            vars.into_iter()
                .map(|v| transform_var_consuming(v, loop_var_id, stride, index_value_ids))
                .collect(),
        ),
        // Other statement types pass through unchanged for now
        other => other,
    }
}

fn transform_var_consuming(
    var: Var,
    loop_var_id: usize,
    stride: usize,
    index_value_ids: &HashSet<ValueId>,
) -> Var {
    if should_index_var(&var, index_value_ids) {
        // For consuming loops, subtract loop_var * stride from the subscript.
        // This represents the decreasing indices as values are consumed.
        let neg_loop_var = loop_term(loop_var_id, -(stride as i64));

        // Subtract loop variable from the existing subscript
        let new_subscript = add_index_exprs(var.subscript.clone(), neg_loop_var);
        var.with_subscript(new_subscript)
    } else {
        var
    }
}

fn transform_expr_consuming(
    expr: Expr,
    loop_var_id: usize,
    stride: usize,
    index_value_ids: &HashSet<ValueId>,
) -> Expr {
    match expr {
        Expr::Var(v) => Expr::Var(transform_var_consuming(v, loop_var_id, stride, index_value_ids)),
        Expr::Binary(op, lhs, rhs) => Expr::Binary(
            op,
            Box::new(transform_expr_consuming(*lhs, loop_var_id, stride, index_value_ids)),
            Box::new(transform_expr_consuming(*rhs, loop_var_id, stride, index_value_ids)),
        ),
        Expr::Unary(op, inner) => Expr::Unary(
            op,
            Box::new(transform_expr_consuming(*inner, loop_var_id, stride, index_value_ids)),
        ),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => Expr::Ternary {
            cond: Box::new(transform_expr_consuming(
                *cond,
                loop_var_id,
                stride,
                index_value_ids,
            )),
            then_expr: Box::new(transform_expr_consuming(
                *then_expr,
                loop_var_id,
                stride,
                index_value_ids,
            )),
            else_expr: Box::new(transform_expr_consuming(
                *else_expr,
                loop_var_id,
                stride,
                index_value_ids,
            )),
        },
        other => other,
    }
}

fn should_index_var(var: &Var, index_value_ids: &HashSet<ValueId>) -> bool {
    match var.base {
        VarBase::LoopInput { .. } => true,
        VarBase::Value(id) => index_value_ids.contains(&id),
    }
}

/// Collect all value identifiers present in the given variables.
fn collect_value_ids(vars: &[Var]) -> HashSet<ValueId> {
    vars.iter()
        .filter_map(|v| v.base.value_id())
        .collect()
}

/// Collect all value identifiers defined in the given statements.
fn collect_defined_value_ids(stmts: &[Stmt]) -> HashSet<ValueId> {
    let mut ids = HashSet::new();
    for stmt in stmts {
        collect_defined_in_stmt(stmt, &mut ids);
    }
    ids
}

fn collect_defined_in_stmt(stmt: &Stmt, ids: &mut HashSet<ValueId>) {
    match stmt {
        Stmt::Assign { dest, .. } => collect_defined_in_var(dest, ids),
        Stmt::MemLoad(load) => {
            for v in &load.outputs {
                collect_defined_in_var(v, ids);
            }
        }
        Stmt::MemStore(_) => {}
        Stmt::AdvLoad(load) => {
            for v in &load.outputs {
                collect_defined_in_var(v, ids);
            }
        }
        Stmt::AdvStore(_) => {}
        Stmt::LocalLoad(load) => {
            for v in &load.outputs {
                collect_defined_in_var(v, ids);
            }
        }
        Stmt::LocalStore(_) | Stmt::LocalStoreW(_) => {}
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in &call.results {
                collect_defined_in_var(v, ids);
            }
        }
        Stmt::DynCall { results, .. } => {
            for v in results {
                collect_defined_in_var(v, ids);
            }
        }
        Stmt::Intrinsic(intrinsic) => {
            for v in &intrinsic.results {
                collect_defined_in_var(v, ids);
            }
        }
        Stmt::Repeat { body, phis, .. } => {
            for phi in phis {
                collect_defined_in_var(&phi.dest, ids);
            }
            for stmt in body {
                collect_defined_in_stmt(stmt, ids);
            }
        }
        Stmt::If {
            then_body,
            else_body,
            phis,
            ..
        } => {
            for phi in phis {
                collect_defined_in_var(&phi.dest, ids);
            }
            for stmt in then_body {
                collect_defined_in_stmt(stmt, ids);
            }
            for stmt in else_body {
                collect_defined_in_stmt(stmt, ids);
            }
        }
        Stmt::While { body, phis, .. } => {
            for phi in phis {
                collect_defined_in_var(&phi.dest, ids);
            }
            for stmt in body {
                collect_defined_in_stmt(stmt, ids);
            }
        }
        Stmt::Return(_) => {}
    }
}

fn collect_defined_in_var(var: &Var, ids: &mut HashSet<ValueId>) {
    if let VarBase::Value(id) = var.base {
        ids.insert(id);
    }
}

/// Identify entry values whose stack slots change across iterations.
fn collect_loop_carried_entry_ids(entry_vars: &[Var], exit_vars: &[Var]) -> HashSet<ValueId> {
    let mut ids = HashSet::new();
    let len = entry_vars.len().min(exit_vars.len());
    for idx in 0..len {
        if entry_vars[idx] != exit_vars[idx] {
            if let Some(id) = entry_vars[idx].base.value_id() {
                ids.insert(id);
            }
        }
    }
    ids
}

fn collect_repeat_phis(entry_vars: &[Var], exit_vars: &[Var]) -> Vec<LoopPhi> {
    let mut phis = Vec::new();
    let len = entry_vars.len().min(exit_vars.len());
    for idx in 0..len {
        if entry_vars[idx] != exit_vars[idx] {
            let init = entry_vars[idx].clone();
            let dest = exit_vars[idx].clone();
            phis.push(LoopPhi {
                dest: dest.clone(),
                init,
                step: dest,
            });
        }
    }
    phis
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
    fn producing_stride_applies_multiplier() {
        let var = make_var(0, 0, 5);
        let mut ids = HashSet::new();
        ids.insert(ValueId::from(0));
        let out = transform_var_producing(var, 0, 2, &ids);
        let expected = IndexExpr::Add(
            Box::new(IndexExpr::Mul(
                Box::new(IndexExpr::Const(2)),
                Box::new(IndexExpr::LoopVar(0)),
            )),
            Box::new(IndexExpr::Const(5)),
        );
        assert_eq!(out.subscript, expected);
    }

    #[test]
    fn consuming_stride_applies_multiplier() {
        let var = make_var(0, 0, 5);
        let mut ids = HashSet::new();
        ids.insert(ValueId::from(0));
        let out = transform_var_consuming(var, 0, 3, &ids);
        let expected = IndexExpr::Add(
            Box::new(IndexExpr::Const(5)),
            Box::new(IndexExpr::Mul(
                Box::new(IndexExpr::Const(-3)),
                Box::new(IndexExpr::LoopVar(0)),
            )),
        );
        assert_eq!(out.subscript, expected);
    }

    #[test]
    fn non_indexed_var_keeps_subscript() {
        let var = make_var(1, 0, 7);
        let ids = HashSet::new();
        let out = transform_var_producing(var, 0, 2, &ids);
        assert_eq!(out.subscript, IndexExpr::Const(7));
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
