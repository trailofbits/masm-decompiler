//! Direct AST-to-IR lifting.
//!
//! This module transforms MASM AST directly into structured IR statements,
//! without an intermediate CFG representation. The approach mirrors signature
//! inference: recursive AST traversal with symbolic stack tracking.

mod inst;
mod stack;

use log::debug;
use miden_assembly_syntax::ast::{Block, Instruction, Op, Procedure};

use crate::ir::{Expr, IndexExpr, LoopVar, Stmt, Subscript, Var};
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

    debug!("lifting procedure `{}`", proc_path);
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

    // Use then-branch stack as the result.
    // (Both branches have the same depth, variables may differ but
    // we use then-branch as the canonical choice.)
    *stack = then_stack;

    Ok(vec![Stmt::If {
        cond,
        then_body,
        else_body,
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

    // Compute net effect per iteration.
    let delta = exit_depth as isize - entry_depth as isize;

    // Transform subscripts based on loop type.
    // Use loop_depth as the identifier for IndexExpr::LoopVar.
    let loop_depth = loop_var.loop_depth;
    let body_stmts = if delta > 0 {
        // Producing loop: subscripts for new values = LoopVar
        transform_producing_subscripts(body_stmts, entry_depth, loop_depth)
    } else if delta < 0 {
        // Consuming loop: subscripts = (stack_depth - LoopVar)
        transform_consuming_subscripts(body_stmts, entry_depth, loop_depth)
    } else {
        // Neutral loop: no transformation needed, subscripts are constant
        body_stmts
    };

    // Simulate remaining iterations for stack depth tracking.
    if delta > 0 {
        // Producing loop: each iteration adds `delta` values.
        // We already processed one iteration, simulate count-1 more.
        for _ in 1..count {
            for _ in 0..delta {
                let depth = stack.len();
                stack.push(Var::new(depth));
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

/// Transform subscripts for a producing loop.
///
/// In a producing loop, variables created at or after entry_depth have
/// iteration-dependent subscripts. The loop variable is added to any
/// existing subscript to account for nested loop effects.
fn transform_producing_subscripts(
    stmts: Vec<Stmt>,
    entry_depth: usize,
    loop_var_id: usize,
) -> Vec<Stmt> {
    stmts
        .into_iter()
        .map(|stmt| transform_stmt_producing(stmt, entry_depth, loop_var_id))
        .collect()
}

fn transform_stmt_producing(stmt: Stmt, entry_depth: usize, loop_var_id: usize) -> Stmt {
    match stmt {
        Stmt::Assign { dest, expr } => {
            let dest = transform_var_producing(dest, entry_depth, loop_var_id);
            let expr = transform_expr_producing(expr, entry_depth, loop_var_id);
            Stmt::Assign { dest, expr }
        }
        Stmt::Repeat {
            loop_var,
            loop_count,
            body,
        } => Stmt::Repeat {
            loop_var,
            loop_count,
            body: transform_producing_subscripts(body, entry_depth, loop_var_id),
        },
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => Stmt::If {
            cond: transform_expr_producing(cond, entry_depth, loop_var_id),
            then_body: transform_producing_subscripts(then_body, entry_depth, loop_var_id),
            else_body: transform_producing_subscripts(else_body, entry_depth, loop_var_id),
        },
        Stmt::While { cond, body } => Stmt::While {
            cond: transform_expr_producing(cond, entry_depth, loop_var_id),
            body: transform_producing_subscripts(body, entry_depth, loop_var_id),
        },
        Stmt::Return(vars) => Stmt::Return(
            vars.into_iter()
                .map(|v| transform_var_producing(v, entry_depth, loop_var_id))
                .collect(),
        ),
        // Other statement types pass through unchanged for now
        other => other,
    }
}

fn transform_var_producing(var: Var, entry_depth: usize, loop_var_id: usize) -> Var {
    // Only transform variables at or after entry_depth (produced values)
    if var.stack_depth >= entry_depth {
        let loop_var = IndexExpr::LoopVar(loop_var_id);
        let new_subscript = match &var.subscript {
            Subscript::None => loop_var,
            Subscript::Expr(existing) => {
                // Add outer loop's contribution to inner loop's subscript
                add_index_exprs(loop_var, existing.clone())
            }
        };
        var.with_subscript(Subscript::Expr(new_subscript))
    } else {
        var
    }
}

fn transform_expr_producing(expr: Expr, entry_depth: usize, loop_var_id: usize) -> Expr {
    match expr {
        Expr::Var(v) => Expr::Var(transform_var_producing(v, entry_depth, loop_var_id)),
        Expr::Binary(op, lhs, rhs) => Expr::Binary(
            op,
            Box::new(transform_expr_producing(*lhs, entry_depth, loop_var_id)),
            Box::new(transform_expr_producing(*rhs, entry_depth, loop_var_id)),
        ),
        Expr::Unary(op, inner) => Expr::Unary(
            op,
            Box::new(transform_expr_producing(*inner, entry_depth, loop_var_id)),
        ),
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
    entry_depth: usize,
    loop_var_id: usize,
) -> Vec<Stmt> {
    stmts
        .into_iter()
        .map(|stmt| transform_stmt_consuming(stmt, entry_depth, loop_var_id))
        .collect()
}

fn transform_stmt_consuming(stmt: Stmt, entry_depth: usize, loop_var_id: usize) -> Stmt {
    match stmt {
        Stmt::Assign { dest, expr } => {
            let dest = transform_var_consuming(dest, entry_depth, loop_var_id);
            let expr = transform_expr_consuming(expr, entry_depth, loop_var_id);
            Stmt::Assign { dest, expr }
        }
        Stmt::Repeat {
            loop_var,
            loop_count,
            body,
        } => Stmt::Repeat {
            loop_var,
            loop_count,
            body: transform_consuming_subscripts(body, entry_depth, loop_var_id),
        },
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => Stmt::If {
            cond: transform_expr_consuming(cond, entry_depth, loop_var_id),
            then_body: transform_consuming_subscripts(then_body, entry_depth, loop_var_id),
            else_body: transform_consuming_subscripts(else_body, entry_depth, loop_var_id),
        },
        Stmt::While { cond, body } => Stmt::While {
            cond: transform_expr_consuming(cond, entry_depth, loop_var_id),
            body: transform_consuming_subscripts(body, entry_depth, loop_var_id),
        },
        Stmt::Return(vars) => Stmt::Return(
            vars.into_iter()
                .map(|v| transform_var_consuming(v, entry_depth, loop_var_id))
                .collect(),
        ),
        // Other statement types pass through unchanged for now
        other => other,
    }
}

fn transform_var_consuming(var: Var, _entry_depth: usize, loop_var_id: usize) -> Var {
    // For consuming loops, subtract loop_var from the subscript.
    // This represents the decreasing indices as values are consumed.
    let neg_loop_var = IndexExpr::Mul(
        Box::new(IndexExpr::Const(-1)),
        Box::new(IndexExpr::LoopVar(loop_var_id)),
    );

    let new_subscript = match &var.subscript {
        Subscript::None => {
            // Base case: subscript = stack_depth - loop_var
            add_index_exprs(IndexExpr::Const(var.stack_depth as i64), neg_loop_var)
        }
        Subscript::Expr(existing) => {
            // Nested case: subscript = existing - loop_var
            add_index_exprs(existing.clone(), neg_loop_var)
        }
    };
    var.with_subscript(Subscript::Expr(new_subscript))
}

fn transform_expr_consuming(expr: Expr, entry_depth: usize, loop_var_id: usize) -> Expr {
    match expr {
        Expr::Var(v) => Expr::Var(transform_var_consuming(v, entry_depth, loop_var_id)),
        Expr::Binary(op, lhs, rhs) => Expr::Binary(
            op,
            Box::new(transform_expr_consuming(*lhs, entry_depth, loop_var_id)),
            Box::new(transform_expr_consuming(*rhs, entry_depth, loop_var_id)),
        ),
        Expr::Unary(op, inner) => Expr::Unary(
            op,
            Box::new(transform_expr_consuming(*inner, entry_depth, loop_var_id)),
        ),
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

    // Process the loop body once. (Since we only support stack-neutral while
    // loops, we do not need to track the loop variable).
    let mut body_stack = stack.clone();
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
    Ok(vec![Stmt::While {
        cond,
        body: body_stmts,
    }])
}
