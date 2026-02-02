//! Direct AST-to-IR lifting.
//!
//! This module transforms MASM AST directly into structured IR statements,
//! without an intermediate CFG representation. The approach mirrors signature
//! inference: recursive AST traversal with symbolic stack tracking.

mod inst;
mod stack;

use log::debug;
use miden_assembly_syntax::ast::{Block, Instruction, Op, Procedure};

use crate::ir::{Expr, Stmt, Var};
use crate::signature::{ProcSignature, SignatureMap};

pub use stack::SymbolicStack;

/// Errors that can occur during lifting.
#[derive(Debug)]
pub enum LiftError {
    /// Unsupported instruction encountered.
    UnsupportedInstruction(Instruction),
    /// Call to procedure with unknown signature.
    UnknownCallTarget(String),
    /// Unbalanced if-statement (branches have different stack effects).
    UnbalancedIf,
    /// Non-neutral while loop.
    NonNeutralWhile,
}

impl std::fmt::Display for LiftError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LiftError::UnsupportedInstruction(inst) => {
                write!(f, "unsupported instruction: {inst}")
            }
            LiftError::UnknownCallTarget(target) => {
                write!(f, "unknown call target: {target}")
            }
            LiftError::UnbalancedIf => write!(f, "unbalanced if-statement"),
            LiftError::NonNeutralWhile => write!(f, "non-neutral while loop"),
        }
    }
}

impl std::error::Error for LiftError {}

/// Result type for lifting operations.
pub type LiftResult<T> = Result<T, LiftError>;

/// Context for tracking loop nesting during lifting.
#[derive(Debug, Clone, Default)]
pub struct LoopContext {
    /// Stack of (loop_var, entry_depth) for each enclosing loop.
    loops: Vec<(Var, usize)>,
}

impl LoopContext {
    /// Create a new empty loop context.
    pub fn new() -> Self {
        Self { loops: Vec::new() }
    }

    /// Enter a new loop with the given loop variable and entry stack depth.
    pub fn enter(&mut self, loop_var: Var, entry_depth: usize) {
        self.loops.push((loop_var, entry_depth));
    }

    /// Exit the current loop.
    pub fn exit(&mut self) {
        self.loops.pop();
    }

    /// Get the current loop depth (number of enclosing loops).
    pub fn depth(&self) -> usize {
        self.loops.len()
    }

    /// Get the innermost loop info, if any.
    pub fn innermost(&self) -> Option<&(Var, usize)> {
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
) -> LiftResult<Vec<Stmt>> {
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
) -> LiftResult<Vec<Stmt>> {
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
) -> LiftResult<Vec<Stmt>> {
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
) -> LiftResult<Vec<Stmt>> {
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
        return Err(LiftError::UnbalancedIf);
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
) -> LiftResult<Vec<Stmt>> {
    let entry_depth = stack.len();

    // Allocate loop variable at current depth.
    let loop_var = Var::new(entry_depth);

    // Enter loop context.
    loop_ctx.enter(loop_var.clone(), entry_depth);

    // Process body once to get template and determine stack effect.
    let body_stmts = lift_block(body, stack, loop_ctx, module_path, sigs)?;

    // Exit loop context.
    loop_ctx.exit();

    let exit_depth = stack.len();

    // Compute net effect per iteration.
    let delta = exit_depth as isize - entry_depth as isize;

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

/// Lift a while loop construct.
///
/// We only support stack-neutral while loops.
fn lift_while(
    body: &Block,
    stack: &mut SymbolicStack,
    loop_ctx: &mut LoopContext,
    module_path: &str,
    sigs: &SignatureMap,
) -> LiftResult<Vec<Stmt>> {
    // Pop initial condition.
    let cond_var = stack.pop();
    let cond = Expr::Var(cond_var);

    let entry_depth = stack.len();

    // Process body once (loop context not entered for while - no loop var).
    let mut body_stack = stack.clone();
    let body_stmts = lift_block(body, &mut body_stack, loop_ctx, module_path, sigs)?;

    // The body should end with pushing a condition value.
    // Pop the continuation condition.
    if !body_stack.is_empty() {
        body_stack.pop();
    }

    // Verify stack-neutral.
    if body_stack.len() != entry_depth {
        return Err(LiftError::NonNeutralWhile);
    }

    // Stack is unchanged after while loop (neutral).
    Ok(vec![Stmt::While {
        cond,
        body: body_stmts,
    }])
}
