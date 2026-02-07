# SSA and Indexed Stack Values Design

This document explains how SSA lifting works in the decompiler, **why** it is
implemented the way it is, and **how** it preserves semantics when translating
stack-based MASM into structured, SSA-like IR.

## Goals (and the problems they solve)

1. **Preserve value identity across stack manipulation.**
   - Stack instructions like `swap`, `movup`, `movdn`, and `dup` move values
     without changing them. If we used only stack position to identify values,
     we would incorrectly treat these moves as redefinitions.
2. **Represent repeat-loop semantics accurately.**
   - Repeat loops consume or produce stack values over iterations. A single
     stack position inside the loop body can refer to different *entry* values
     on each iteration. We must make this explicit in the output.
3. **Make control-flow merges explicit.**
   - `if` and `while` introduce multiple reaching definitions. We represent these
     merges with phi metadata (without new `Stmt` variants) so later analyses
     (naming, DCE, def-use checks) can remain correct.
4. **Keep printed output semantically faithful.**
   - The textual output is the only user-facing result. Any mismatch between
     printed variables and actual semantics is a correctness bug.

## Scope and Correctness Conditions

The lifting design is correct **within the supported subset**:

- All stack effects are statically known.
- `if` branches are stack-balanced.
- `while` loops are stack-neutral (excluding the condition).
- `repeat` counts are known and finite.
- Dynamic calls remain unsupported.

If these constraints are violated, the implementation returns an error
(`UnsupportedRepeatPattern`, `UnbalancedIf`, `NonNeutralWhile`, etc.) rather than
emitting potentially incorrect output.

## Core Concepts

### `ValueId` — SSA identity

A `ValueId` uniquely identifies a single definition. Instructions that create a
new value allocate a fresh `ValueId`. Stack moves **do not** create new values
and therefore preserve the same `ValueId`.

### `SlotId` — stack position identity

`SlotId` tracks a *stack slot* across instructions. It is used for repeat-loop
analysis, where values can move but we still need to track *which stack slot* a
value belongs to after each iteration.

### `VarBase`

A variable’s identity source:

- `VarBase::Value(ValueId)` — a concrete SSA value.
- `VarBase::LoopInput { loop_depth }` — a symbolic reference to the **entry
  stack snapshot** of a repeat loop. Used when the same stack position in the
  loop body refers to different entry values across iterations.

### `Var`

A variable reference carries:

- `base: VarBase` — identity source.
- `stack_depth: usize` — birth depth (debug/display only).
- `subscript: IndexExpr` — loop-indexed identity (what prints as `v_…`).

## How SSA Lifting Works (Why each step exists)

### 1. Symbolic stack tracking

The lifter maintains a `SymbolicStack` of `Var` and `SlotId` pairs:

- **New values** allocate a new `ValueId` and a new slot (or reuse a popped
  slot id for stack-effect instructions like `add`).
- **Moves** (`swap`, `movup`, `movdn`, `reversew`) only reorder stack entries;
  the value identity is unchanged.

**Why:** This preserves *value identity* independently of stack position,
so stack rearrangements never create false redefinitions.

### 2. `if` merges → phi metadata

Each branch is lifted with a cloned stack. If branches disagree at a slot,
we allocate a fresh `ValueId` and create an `IfPhi { dest, then_var, else_var }`.

**Why:** The output is structured, but multiple reaching definitions still exist.
Phi metadata preserves correctness for later naming and analysis.

### 3. `while` loops → per-slot phi

We create a phi for each slot at loop entry, lift the body once, and then
record `LoopPhi { dest, init, step }`.

**Why:** A `while` loop is zero-or-more iterations. The phi captures the loop-
carried value for each slot explicitly.

### 4. `repeat` loops — the tricky case

Repeat loops are handled in several stages:

1. **Lift the body once** from the entry stack.
2. **Compare entry vs. exit slots** to identify loop-carried values.
3. **Compute subscript deltas** from slot movement (see `SUBSCRIPTS.md`).
4. **Rewrite entry values to loop inputs** in consuming loops.
5. **Rebuild the post-loop stack** using tag-aware simulation across *all*
   iterations (see below).

#### Why tag-aware post-loop simulation is required

In consuming loops, the loop-carried value can **move to a different slot id
on each iteration**. A one-iteration analysis identifies *which* value is
loop-carried but does not reveal *where it ends up* after N iterations.

**Example:**

```
repeat.4
  add
end
```

- The loop body reuses the deeper operand’s slot id.
- After each iteration, the accumulator moves down one slot.
- After 4 iterations, the accumulator ends up at the bottom.

If we rebuild the post-loop stack using only the slot ids from the first
iteration, we return the original input (`v_0`) instead of the accumulator.

**Fix:** A tag-aware slot simulation propagates “loop-carried tags” through
all iterations, so the accumulator is mapped to its **final** slot.

### 5. Output naming

`assign_var_names` ensures printed names are stable and disambiguated:

- Inputs and loop-inputs keep their base names (`v_0`, `v_(6 - i)` …).
- Later collisions are suffixed (`v_0_1`, `v_(6 - i)_1`).

This is display-only: SSA identity is always based on `(ValueId, IndexExpr)`.

## Examples

### A. Stack move does **not** redefine

```
proc f
  swap
end
```

The top two values swap, but their `ValueId`s remain unchanged. If we used
stack position as identity, we would incorrectly treat this as redefinition.

### B. Consuming repeat accumulator (requires tag simulation)

```
repeat.4
  add
end
```

Correct output keeps the accumulator and returns it:

```
for i in 0..4 {
  v_3 = v_3 + v_(4 - i);
}
return v_3;
```

### C. Producing repeat loop

```
repeat.4
  push.0
end
```

Each iteration produces a new value indexed by the loop counter:

```
for i in 0..4 {
  v_i = 0;
}
return v_3, v_2, v_1, v_0;
```

### D. Consuming loop inputs as `LoopInput`

```
eq.0
repeat.7
  swap
  eq.0
  and
end
```

The loop body references different entry values each iteration, so these
values are rewritten to loop inputs like `v_(6 - i)`.

## Guarantees

Within the supported subset, this design ensures:

- Stack moves do not cause false redefinitions.
- Repeat-loop semantics are preserved for consuming and producing loops.
- Post-loop stack values are correct even when loop-carried values migrate.
- Output naming is deterministic and semantically faithful.

If a pattern cannot be represented safely (e.g., loop-carried value merges),
the lifter returns `UnsupportedRepeatPattern` instead of emitting incorrect
output.

## Related Documents

- `SUBSCRIPTS.md` — detailed rules and correctness arguments for subscript
  assignment.
