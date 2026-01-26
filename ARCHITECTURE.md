# MASM Decompiler

This crate implements a best-effort decompiler for the Miden assembly language.

## Overview

Miden assembly (MASM) is a stack-based assembly language used in the Miden
zero-knowledge VM. It is challenging to provide faithful decompilation for MASM
for a few different reasons.

- MASM `exec` calls do not conform to an ABI, and the net stack effect of such
  calls is generally impossible to determine statically.
- Most procedures do not have declared signatures, which means that the number
  of inputs and outputs have to be inferred from context.
- While-loops do not need to be stack neutral. In particular, while-loop
  conditions may occupy a different stack slot in each iteration.
- Branches in conditional statements may have different stack effects, which
  makes signature inference and faithful decompilation challenging.

## Architecture

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

1. **Call graph generation.** (`src/callgraph`). Recursively generate a call
   graph by resolving referenced symbols to the corresponding procedure
   definitions. These may be either local (same module) or remote (in a
   transitively imported module). This relies on a robust symbol resolver that can
   resolve symbols across the workspace and libraries. Since MASM only supports
   recursion through dynamic calls, and these are not supported, the generated call
   graph cannot contain cycles.

2. **Signature inference.** (`src/signature`). We visit each transitively called
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

3. **CFG construction.** (`src/cfg`). We construct a control-flow graph (CFG)
   for each procedure by creating basic blocks for straight-line code, and lifting
   branching and looping constructs into structured control-flow using
   `Stmt::RepeatBranch`, `Stmt::WhileBranch` and `Stmt::IfBranch`. All other
   instructions are wrapped using `Stmt::Inst` in this phase.

4. **Lifting to SSA.** (`src/ssa`) We lift each CFG to SSA. This introduces
   Phi-nodes to handle while-loop conditions and joining if-statement branches. SSA
   variables are tracked by an ID and index (an `IndexExpr`). The SSA IR is minimal
   with the following instructions types.
   - `Stmt::Assign`
   - `Stmt::Call`
   - `Stmt::RepeatBranch`
   - `Stmt::WhileBranch`
   - `Stmt::IfBranch`
   - `Stmt::Repeat`
   - `Stmt::If`
   - `Stmt::While`
   - `Stmt::Return`
   - `Stmt::MemLoad`
   - `Stmt::MemStore`
   - `Stmt::LocalLoad`
   - `Stmt::LocalStore`
   - `Stmt::AdviceLoad`
   - `Stmt::AdviceStore`
   - `Stmt::Intrinsic`
   - `Stmt::Phi`

   The `Stmt::Repeat`, `Stmt::While`, and `Stmt::If` are not emitted in this
   phase. After this phase, the CFG will not contain any `Stmt::Inst`
   instructions.

5. **Variable subscript assignment.** (`src/structuring`).Variable subscripts
   are computed. Synthetic index variables are introduced to handle indexing in
   producing and consuming repeat-loops. The net stack effect of the loop is
   determined by the corresponding `Stmt::RepeatBranch` instruction. For producing
   and consuming loops, the base index and step are determined from context and the
   net effect of the loop. (Note that for nested loops, the base index may also be
   an index expression.)

After this phase, all SSA variables will have concrete subscripts.

6. **Structuring.** (`src/structuring`).Constant propagation, expression
   inlining, and dead-code elimination takes place during this phase to make the
   final result more readable. Loop constructs are converted from the branching
   forms (`Stmt::RepeatBranch`, `Stmt::WhileBranch`, `Stmt::IfBranch`) to the
   corresponding straight-line forms (`Stmt::Repeat`, `Stmt::While`, `Stmt::If`).

   After this phase, the CFG will not contain any `Stmt::RepeatBranch`,
   `Stmt::WhileBranch`, `Stmt::IfBranch`, or `Stmt::Phi` instructions.

7. **Formatting.** (`src/fmt`). The final output is formatted and printed.
