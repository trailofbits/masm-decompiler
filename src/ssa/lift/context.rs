//! Shared SSA lifting context, frame state, and allocation helpers.

use std::collections::HashMap;

use crate::cfg::NodeId;
use crate::signature::{ProcSignature, SignatureMap};

use crate::ssa::{SsaStack, Var, VarArena};

/// Per-block symbolic frame containing the stack state.
#[derive(Clone)]
pub(super) struct Frame {
    /// Current symbolic stack state.
    pub(super) stack: SsaStack,
}

impl Frame {
    /// Ensure the stack meets a required depth, allocating inputs as needed.
    /// New variables are recorded with their birth depth (position from bottom).
    pub(super) fn ensure_depth(
        &mut self,
        ctx: &mut SsaContext,
        alloc: &mut impl VarAlloc,
        required_depth: usize,
    ) {
        // Variables added to the front get depths 0, 1, 2, ... as they're prepended.
        // We need to track how many we're adding and assign depths accordingly.
        let current_len = self.stack.len();
        if required_depth <= current_len {
            return;
        }
        let to_add = required_depth - current_len;
        // Variables are prepended (pushed to front), so they get depths 0, 1, ..., to_add-1
        // and existing variables shift up by to_add.
        for depth in (0..to_add).rev() {
            let value = alloc.alloc(ctx);
            ctx.record_depth(&value, depth);
            self.stack.push_front_one(value);
        }
    }

    /// Pop a fixed number of values, extending the stack if needed.
    /// New variables created for underflow are recorded with their birth depth.
    pub(super) fn pop_many(
        &mut self,
        ctx: &mut SsaContext,
        alloc: &mut impl VarAlloc,
        pops: usize,
        required_depth: usize,
    ) -> Vec<Var> {
        // First ensure we have enough depth
        self.ensure_depth(ctx, alloc, required_depth.max(pops));
        // Now pop from the stack
        let mut out = Vec::with_capacity(pops);
        for _ in 0..pops {
            if let Some(value) = self.stack.pop_back_one() {
                out.push(value);
            }
        }
        out
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
    /// Each new variable is recorded with its birth depth.
    pub(super) fn push_many(
        &mut self,
        ctx: &mut SsaContext,
        alloc: &mut impl VarAlloc,
        pushes: usize,
    ) -> Vec<Var> {
        let mut vars = Vec::with_capacity(pushes);
        for _ in 0..pushes {
            let depth = self.stack.len();
            let value = alloc.alloc(ctx);
            ctx.record_depth(&value, depth);
            self.stack.push_back_one(value.clone());
            vars.push(value);
        }
        vars
    }
}

/// Build the entry frame using a known procedure signature, if any.
/// Records birth depths for all procedure inputs (0, 1, 2, ... from bottom).
pub(super) fn build_entry_frame(
    proc_path: &str,
    sigs: &SignatureMap,
    ctx: &mut SsaContext,
) -> Frame {
    let mut inputs = Vec::new();
    if let Some(ProcSignature::Known {
        inputs: input_count,
        ..
    }) = sigs.get(proc_path)
    {
        for depth in 0..*input_count {
            let v = ctx.new_var_at_depth(depth);
            inputs.push(v);
        }
    }
    Frame {
        stack: SsaStack::from_inputs(inputs),
    }
}

/// Shared SSA lifting context for variable allocation and lookups.
pub(super) struct SsaContext {
    /// Arena used to allocate SSA variables.
    arena: VarArena,
    /// Maps variable index to its birth depth (stack depth when created).
    var_depths: HashMap<usize, usize>,
}

impl SsaContext {
    /// Create a new context from an existing variable arena.
    pub(super) fn new(arena: VarArena) -> Self {
        Self {
            arena,
            var_depths: HashMap::new(),
        }
    }

    /// Return both the arena and var_depths when lifting completes.
    pub(super) fn into_parts(self) -> (VarArena, HashMap<usize, usize>) {
        (self.arena, self.var_depths)
    }

    /// Allocate a fresh SSA variable.
    pub(super) fn new_var(&mut self) -> Var {
        self.arena.new_var()
    }

    /// Allocate a fresh SSA variable and record its birth depth.
    pub(super) fn new_var_at_depth(&mut self, depth: usize) -> Var {
        let var = self.arena.new_var();
        self.var_depths.insert(var.index, depth);
        var
    }

    /// Record the birth depth of an existing variable.
    pub(super) fn record_depth(&mut self, var: &Var, depth: usize) {
        self.var_depths.insert(var.index, depth);
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
