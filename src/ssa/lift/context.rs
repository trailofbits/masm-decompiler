//! Shared SSA lifting context, frame state, and allocation helpers.

use std::collections::{HashMap, HashSet};

use crate::cfg::NodeId;
use crate::signature::{ProcSignature, SignatureMap};

use crate::ssa::{Expr, SsaStack, Var, VarArena};

/// Per-block symbolic frame containing the stack and expression bindings.
#[derive(Clone)]
pub(super) struct Frame {
    /// Current symbolic stack state.
    pub(super) stack: SsaStack,
    /// Expressions bound to SSA variables in this frame.
    pub(super) exprs: HashMap<Var, Expr>,
}

impl Frame {
    /// Ensure the stack meets a required depth, allocating inputs as needed.
    pub(super) fn ensure_depth(
        &mut self,
        ctx: &mut SsaContext,
        alloc: &mut impl VarAlloc,
        required_depth: usize,
    ) {
        let exprs = &mut self.exprs;
        self.stack.ensure_depth(required_depth, || {
            let value = alloc.alloc(ctx);
            exprs.insert(value.clone(), Expr::Var(value.clone()));
            value
        });
    }

    /// Pop a fixed number of values, extending the stack if needed.
    pub(super) fn pop_many(
        &mut self,
        ctx: &mut SsaContext,
        alloc: &mut impl VarAlloc,
        pops: usize,
        required_depth: usize,
    ) -> Vec<Var> {
        let exprs = &mut self.exprs;
        self.stack.pop_many(pops, required_depth, || {
            let value = alloc.alloc(ctx);
            exprs.insert(value.clone(), Expr::Var(value.clone()));
            value
        })
    }

    /// Pop a single value from the stack.
    pub(super) fn pop_one(
        &mut self,
        ctx: &mut SsaContext,
        alloc: &mut impl VarAlloc,
        required_depth: usize,
    ) -> Var {
        let mut popped = self.pop_many(ctx, alloc, 1, required_depth);
        popped.pop().unwrap()
    }

    /// Push a fixed number of new SSA values onto the stack.
    pub(super) fn push_many(
        &mut self,
        ctx: &mut SsaContext,
        alloc: &mut impl VarAlloc,
        pushes: usize,
    ) -> Vec<Var> {
        self.stack.push_many(pushes, || alloc.alloc(ctx))
    }
}

/// Build the entry frame using a known procedure signature, if any.
pub(super) fn build_entry_frame(
    proc_path: &str,
    sigs: &SignatureMap,
    ctx: &mut SsaContext,
) -> Frame {
    let mut inputs = Vec::new();
    let mut exprs = HashMap::new();
    if let Some(ProcSignature::Known { inputs: count, .. }) = sigs.get(proc_path) {
        for _ in 0..*count {
            let v = ctx.new_var();
            exprs.insert(v.clone(), Expr::Var(v.clone()));
            inputs.push(v);
        }
    }
    Frame {
        stack: SsaStack::from_inputs(inputs),
        exprs,
    }
}

/// Drop expression bindings for variables not present on the stack.
pub(super) fn retain_live_exprs(state: &mut Frame) {
    let live: HashSet<Var> = state.stack.iter().cloned().collect();
    state.exprs.retain(|k, _| live.contains(k));
}

/// Shared SSA lifting context for variable allocation and lookups.
pub(super) struct SsaContext {
    /// Arena used to allocate SSA variables.
    arena: VarArena,
}

impl SsaContext {
    /// Create a new context from an existing variable arena.
    pub(super) fn new(arena: VarArena) -> Self {
        Self { arena }
    }

    /// Return the inner arena when lifting completes.
    pub(super) fn into_arena(self) -> VarArena {
        self.arena
    }

    /// Allocate a fresh SSA variable.
    pub(super) fn new_var(&mut self) -> Var {
        self.arena.new_var()
    }

    /// Resolve an SSA variable to its bound expression if present.
    pub(super) fn lookup_expr(&self, frame: &Frame, var: Var) -> Expr {
        frame.exprs.get(&var).cloned().unwrap_or(Expr::Var(var))
    }
}

/// Trait for scoped SSA variable allocation.
pub(super) trait VarAlloc {
    /// Allocate an SSA variable, potentially reusing cached slots.
    fn alloc(&mut self, ctx: &mut SsaContext) -> Var;
}

/// Per-statement allocator that reuses cached SSA variables by index.
pub(super) struct AllocScope<'a> {
    /// Cached variables for the current statement.
    cache: &'a mut Vec<Var>,
    /// Current allocation cursor in the cache.
    cursor: usize,
}

impl<'a> VarAlloc for AllocScope<'a> {
    /// Allocate a variable, reusing an existing slot if available.
    fn alloc(&mut self, ctx: &mut SsaContext) -> Var {
        if let Some(existing) = self.cache.get(self.cursor).cloned() {
            self.cursor += 1;
            existing
        } else {
            let v = ctx.new_var();
            self.cache.push(v.clone());
            self.cursor += 1;
            v
        }
    }
}

/// Create an allocation scope for a specific block statement.
pub(super) fn alloc_scope<'a>(
    def_cache: &'a mut Vec<Vec<Vec<Var>>>,
    node: NodeId,
    stmt_idx: usize,
) -> AllocScope<'a> {
    if def_cache.len() <= node {
        def_cache.resize_with(node + 1, Vec::new);
    }
    if def_cache[node].len() <= stmt_idx {
        def_cache[node].resize_with(stmt_idx + 1, Vec::new);
    }
    let cache = &mut def_cache[node][stmt_idx];
    AllocScope { cache, cursor: 0 }
}
