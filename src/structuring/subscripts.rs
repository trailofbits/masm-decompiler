//! Stack-depth-based subscript assignment for SSA variables.
//!
//! This module computes **semantic** subscripts for variables based on their birth
//! depth (the stack depth when they were created) and the loop context they're in.
//! This is distinct from `reindex_vars`, which handles index densification.
//!
//! ## Input Requirements
//!
//! - `var_depths: HashMap<usize, usize>`: Maps variable index → birth depth
//!   (populated during SSA lifting)
//! - `loop_contexts: HashMap<NodeId, LoopContext>`: Maps loop header → loop metadata
//!   including entry depth, effect per iteration, and loop variable index
//!
//! ## Algorithm
//!
//! **Variables outside loops:**
//! ```text
//! subscript = Const(birth_depth)
//! ```
//!
//! **Producing loops** (effect > 0, e.g., `repeat.N { push.0 }`):
//! ```text
//! subscript = (birth_depth - entry_depth) + effect * i
//! ```
//! Example: `repeat.4 { push.0 }` with entry_depth=0 and effect=1:
//! - Iteration 0: v_0
//! - Iteration 1: v_1
//! - Iteration 2: v_2
//! - ...
//!
//! **Consuming loops** (effect < 0, e.g., `repeat.N { add }`):
//! Uses stack-position arithmetic for binary operations:
//! ```text
//! first_operand:  subscript = (entry_depth - 1) - i
//! second_operand: subscript = (entry_depth - 2) - i
//! destination:    subscript = (entry_depth - 2) - i
//! ```
//! Example: `repeat.4 { add }` with entry_depth=5:
//! - Iteration 0: v_3 = v_4 + v_3
//! - Iteration 1: v_2 = v_3 + v_2
//! - Iteration 2: v_1 = v_2 + v_1
//! - Iteration 3: v_0 = v_1 + v_0
//!
//! **Neutral loops** (effect = 0):
//! ```text
//! subscript = Const(birth_depth)
//! ```

use log::{error, trace};
use std::collections::HashMap;

use crate::cfg::LoopContext;
use crate::ssa::{Expr, IndexExpr, Stmt, Subscript, Var};

/// Compute subscripts for all variables in the code based on their birth depths
/// and the loop contexts they appear in.
pub fn compute_subscripts(
    code: &mut [Stmt],
    var_depths: &HashMap<usize, usize>,
    loop_contexts: &HashMap<usize, LoopContext>,
) {
    let mut ctx = SubscriptContext {
        var_depths,
        loop_contexts,
        loop_stack: Vec::new(),
    };
    ctx.process_block(code);
}

struct SubscriptContext<'a> {
    var_depths: &'a HashMap<usize, usize>,
    loop_contexts: &'a HashMap<usize, LoopContext>,
    /// Stack of active loop contexts (innermost last).
    loop_stack: Vec<ActiveLoop>,
}

#[derive(Clone)]
struct ActiveLoop {
    loop_var_index: usize,
    entry_depth: usize,
    effect_per_iter: isize,
    #[allow(dead_code)]
    iter_count: usize, // Kept for potential future use in computing final values
}

impl<'a> SubscriptContext<'a> {
    fn process_block(&mut self, code: &mut [Stmt]) {
        for stmt in code {
            self.process_stmt(stmt);
        }
    }

    fn process_stmt(&mut self, stmt: &mut Stmt) {
        match stmt {
            Stmt::Assign { dest, expr } => {
                // For consuming loops, compute subscripts based on stack position arithmetic
                if let Some(loop_ctx) = self.innermost_consuming_loop() {
                    self.process_consuming_assign(dest, expr, &loop_ctx.clone());
                } else {
                    self.assign_subscript_to_var(dest);
                    self.process_expr(expr);
                }
            }
            Stmt::Repeat {
                loop_var,
                loop_count,
                body,
                ..
            } => {
                // Find the loop context for this repeat
                // We need to match by loop_var.index
                let loop_ctx = self
                    .loop_contexts
                    .values()
                    .find(|ctx| ctx.loop_var_index == loop_var.index);

                let pushed = if let Some(ctx) = loop_ctx {
                    self.loop_stack.push(ActiveLoop {
                        loop_var_index: ctx.loop_var_index,
                        entry_depth: ctx.entry_depth,
                        effect_per_iter: ctx.effect_per_iter,
                        iter_count: *loop_count,
                    });
                    true
                } else {
                    false
                };

                self.process_block(body);

                if pushed {
                    self.loop_stack.pop();
                }
            }
            Stmt::While { cond, body } => {
                self.process_expr(cond);
                self.process_block(body);
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                self.process_expr(cond);
                self.process_block(then_body);
                self.process_block(else_body);
            }
            Stmt::Return(vars) => {
                for v in vars {
                    self.assign_subscript_to_var(v);
                }
            }
            Stmt::Phi { var, sources } => {
                self.assign_subscript_to_var(var);
                for src in sources {
                    self.assign_subscript_to_var(src);
                }
            }
            Stmt::MemLoad(mem) => {
                for v in mem.address.iter_mut().chain(mem.outputs.iter_mut()) {
                    self.assign_subscript_to_var(v);
                }
            }
            Stmt::MemStore(mem) => {
                for v in mem.address.iter_mut().chain(mem.values.iter_mut()) {
                    self.assign_subscript_to_var(v);
                }
            }
            Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
                for v in call.args.iter_mut().chain(call.results.iter_mut()) {
                    self.assign_subscript_to_var(v);
                }
            }
            Stmt::DynCall { args, results } => {
                for v in args.iter_mut().chain(results.iter_mut()) {
                    self.assign_subscript_to_var(v);
                }
            }
            Stmt::Intrinsic(intr) => {
                for v in intr.args.iter_mut().chain(intr.results.iter_mut()) {
                    self.assign_subscript_to_var(v);
                }
            }
            Stmt::AdvLoad(load) => {
                for v in load.outputs.iter_mut() {
                    self.assign_subscript_to_var(v);
                }
            }
            Stmt::AdvStore(store) => {
                for v in store.values.iter_mut() {
                    self.assign_subscript_to_var(v);
                }
            }
            Stmt::LocalLoad(load) => {
                for v in load.outputs.iter_mut() {
                    self.assign_subscript_to_var(v);
                }
            }
            Stmt::LocalStore(store) => {
                for v in store.values.iter_mut() {
                    self.assign_subscript_to_var(v);
                }
            }
            Stmt::IfBranch(_)
            | Stmt::WhileBranch(_)
            | Stmt::RepeatBranch(_)
            | Stmt::Inst(_)
            | Stmt::Nop => {}
        }
    }

    fn process_expr(&mut self, expr: &mut Expr) {
        match expr {
            Expr::Var(v) => self.assign_subscript_to_var(v),
            Expr::Binary(_, a, b) => {
                self.process_expr(a);
                self.process_expr(b);
            }
            Expr::Unary(_, a) => self.process_expr(a),
            Expr::Constant(_) | Expr::True | Expr::False | Expr::Unknown => {}
        }
    }

    /// Return the innermost consuming loop context, if any.
    /// Note: Only loops with negative effect (consuming) should use stack-position arithmetic.
    /// Neutral loops (effect = 0) should use birth-depth based subscripts.
    fn innermost_consuming_loop(&self) -> Option<&ActiveLoop> {
        self.loop_stack
            .iter()
            .rev()
            .find(|l| l.effect_per_iter < 0)
    }

    /// Process an assignment inside a consuming loop using stack position arithmetic.
    fn process_consuming_assign(&mut self, dest: &mut Var, expr: &mut Expr, loop_ctx: &ActiveLoop) {
        // For consuming loops like `repeat.N { add }`:
        // - At iteration i, stack depth is (entry_depth - i)
        // - Binary ops read top two positions and write to (depth - 2) after
        //
        // For `add` specifically:
        // - First operand (top): position (entry_depth - 1 - i)
        // - Second operand: position (entry_depth - 2 - i)
        // - Result: position (entry_depth - 2 - i) = (entry_depth - 2) - i

        match expr {
            Expr::Binary(_, lhs, rhs) => {
                // Operand subscripts: (entry_depth - 1 - i) and (entry_depth - 2 - i)
                let entry = loop_ctx.entry_depth as i64;
                let loop_var_idx = loop_ctx.loop_var_index;

                // First operand (top of stack): subscript = (entry - 1) - i
                if let Expr::Var(v) = lhs.as_mut() {
                    let sub = make_decreasing_subscript(entry - 1, loop_var_idx);
                    v.subscript = sub;
                }

                // Second operand: subscript = (entry - 2) - i
                if let Expr::Var(v) = rhs.as_mut() {
                    let sub = make_decreasing_subscript(entry - 2, loop_var_idx);
                    v.subscript = sub;
                }

                // Result: subscript = (entry - 2) - i (same position as second operand after consuming)
                let dest_sub = make_decreasing_subscript(entry - 2, loop_var_idx);
                dest.subscript = dest_sub;
            }
            _ => {
                // For non-binary expressions, fall back to birth_depth approach
                self.assign_subscript_to_var(dest);
                self.process_expr(expr);
            }
        }
    }

    /// Assign a subscript to a variable based on its birth depth and loop context.
    fn assign_subscript_to_var(&mut self, var: &mut Var) {
        // Skip if already has a subscript
        if !matches!(var.subscript, Subscript::None) {
            return;
        }

        let Some(&birth_depth) = self.var_depths.get(&var.index) else {
            error!("failed to determine birth depth for variable {}", var.index);
            // No depth info - leave subscript as None
            return;
        };
        trace!("variable {} has has birth depth {}", var.index, birth_depth);
        // Find the innermost loop this variable was born inside
        let subscript = self.compute_subscript_for_depth(birth_depth);
        trace!(
            "assigning subscript {:?} to variable {}",
            subscript, var.index
        );

        var.subscript = subscript;
    }

    /// Compute the subscript for a variable with the given birth depth,
    /// considering the current loop stack.
    fn compute_subscript_for_depth(&self, birth_depth: usize) -> Subscript {
        if self.loop_stack.is_empty() {
            // Not inside any loop - just use birth depth as constant subscript
            return Subscript::Expr(IndexExpr::Const(birth_depth as i64));
        }

        // Find the innermost loop that contains this depth
        // (i.e., the variable was born inside or after the loop started)
        let mut containing_loop: Option<&ActiveLoop> = None;
        for loop_ctx in &self.loop_stack {
            if birth_depth >= loop_ctx.entry_depth {
                containing_loop = Some(loop_ctx);
            }
        }

        match containing_loop {
            None => {
                // Variable was born before all loops - constant subscript
                Subscript::Expr(IndexExpr::Const(birth_depth as i64))
            }
            Some(loop_ctx) => {
                // Variable was born inside this loop
                // Subscript depends on loop iteration
                self.compute_loop_subscript(birth_depth, loop_ctx)
            }
        }
    }

    /// Compute a symbolic subscript for a variable born inside a loop.
    fn compute_loop_subscript(&self, birth_depth: usize, loop_ctx: &ActiveLoop) -> Subscript {
        let effect = loop_ctx.effect_per_iter;

        if effect > 0 {
            // Producing loop: subscript = (birth_depth - entry_depth) + effect * i
            // Simplified: birth_depth - entry_depth is the offset within iteration 0
            // Each iteration adds 'effect' more values
            let base_offset = (birth_depth - loop_ctx.entry_depth) as i64;

            // subscript = base_offset + effect * loop_var
            let loop_term = IndexExpr::Mul(
                Box::new(IndexExpr::Const(effect as i64)),
                Box::new(IndexExpr::LoopVar(loop_ctx.loop_var_index)),
            );

            if base_offset == 0 {
                Subscript::Expr(loop_term)
            } else {
                Subscript::Expr(IndexExpr::Add(
                    Box::new(IndexExpr::Const(base_offset)),
                    Box::new(loop_term),
                ))
            }
        } else if effect < 0 {
            // Consuming loop: values at higher positions are consumed first
            // At iteration i, we're working with values at positions that decrease
            // subscript = birth_depth - entry_depth + |effect| * (N - 1 - i)
            // Simplified: (N - 1) * |effect| + birth_depth - entry_depth - |effect| * i

            // Actually for a consuming loop like repeat.N { add }:
            // - At iteration 0, we consume from positions (entry_depth-1) and (entry_depth-2)
            // - At iteration i, we consume from positions (entry_depth-1-i) and (entry_depth-2-i)
            //
            // So if birth_depth = entry_depth - 1 - k for some k,
            // the subscript for that position at iteration i is: (entry_depth - 1 - k) = birth_depth
            // But wait, that's just the constant birth_depth...
            //
            // The symbolic part comes in when we want to express which VALUE is at that position
            // at different iterations. For consuming loops, the same position holds different
            // values at different iterations (loop-carried).
            //
            // For simplicity, use: subscript = birth_depth - |effect| * i
            // This gives decreasing subscripts as i increases.

            let abs_effect = (-effect) as i64;
            let neg_term = IndexExpr::Mul(
                Box::new(IndexExpr::Const(-abs_effect)),
                Box::new(IndexExpr::LoopVar(loop_ctx.loop_var_index)),
            );

            Subscript::Expr(IndexExpr::Add(
                Box::new(IndexExpr::Const(birth_depth as i64)),
                Box::new(neg_term),
            ))
        } else {
            // Neutral loop (effect == 0): constant subscript
            Subscript::Expr(IndexExpr::Const(birth_depth as i64))
        }
    }
}

/// Create a subscript expression of the form: base - loop_var
/// This represents positions that decrease with each iteration.
fn make_decreasing_subscript(base: i64, loop_var_index: usize) -> Subscript {
    // subscript = base - i = base + (-1) * i
    let neg_term = IndexExpr::Mul(
        Box::new(IndexExpr::Const(-1)),
        Box::new(IndexExpr::LoopVar(loop_var_index)),
    );
    Subscript::Expr(IndexExpr::Add(
        Box::new(IndexExpr::Const(base)),
        Box::new(neg_term),
    ))
}
