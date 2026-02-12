# Architecture

We restrict ourself to instructions where stack effects can be determined
statically. This means that

- We do not support dynamic calls since the call target cannot be determined
  statically.
- We only support `exec` calls to procedures for which the signature can be
  inferred statically.
- We only support stack-neutral while-loops.
- We only support balanced if-statements where both branches have the same
  stack effect.

The decompiler implements the following analysis passes.

1. **Call graph generation.** (`src/callgraph`) Recursively generate a call
   graph by resolving referenced symbols to the corresponding procedure
   definitions. These may be either local (same module) or remote (in a
   transitively imported module). This relies on a robust symbol resolver that can
   resolve symbols across the workspace and libraries. Since MASM only supports
   recursion through dynamic calls, and these are not supported, the generated call
   graph cannot contain cycles.

2. **Signature inference.** (`src/signature`) We visit each transitively called
   procedure in DFS order. For each procedure, we symbolically execute each
   instruction, tracking provenance of referenced stack slots. (We start out by
   assuming that the stack depth is 0. Any slots below this point are considered
   procedure arguments. When a slot like this is accessed, we adjust our assumption
   about the required depth accordingly. Any slots above the minimum argument
   height that is changed by the procedure and remains on the stack on exit is
   considered to be an output.) Repeat loops are unrolled during execution. We only
   support stack neutral while-loops, which means that stack effects can be
   computed statically. Conditional statements (if-statements) where the branches
   have different stack effects are not supported. If an unsupported instruction is
   encountered, the analysis exits early and returns `ProcSignature::Unknown`.

3. **Lifting to SSA.** (`src/ssa`) We lift each AST to structured SSA, lifting
   `repeat.N`, `while.true`, and `if.true` to corresponding IR statement variants.
   Phi-nodes are tracked by the corresponding control-flow statement variants to
   ensure that no information is lost. SSA variables are tracked by an ID and index
   (an `IndexExpr`). The SSA IR is defined in `src/ir/mod.rs`. This phase also
   assigns symbolic variable subscripts.

4. **Optimization.** (`src/simplify`) Constant propagation, expression inlining,
   and dead-code elimination takes place during this phase to make the final result
   more readable.

5. **Formatting.** (`src/fmt`). The final output is formatted and printed.

Parallel to the main decompilation pipeline, we also implement a type inference
pass (`src/types`) that performs best-effort type inference for SSA variables.
This is used to annotate procedure signatures with type information, and is also
used to identify potential typing errors in the original MASM code.
