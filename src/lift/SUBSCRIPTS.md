# Variable Subscripts and Loop Indexing

This document explains how variable subscripts (`v_0`, `v_(6 - i)`, etc.) are
assigned and why the analysis preserves semantic accuracy.

## What a subscript means

A variable is rendered as `v_(expr)` where `expr` is an `IndexExpr`:

- `IndexExpr::Const(n)` → `v_n`
- `IndexExpr::LoopVar(i)` → `v_i`
- `IndexExpr::Add` / `IndexExpr::Mul` → `v_(...)`

Subscripts are **not** identity by themselves. Identity is
`(VarBase, subscript)` where:

- `VarBase::Value(ValueId)` identifies a concrete SSA value.
- `VarBase::LoopInput { loop_depth }` identifies a loop-entry snapshot.

## Base subscript assignment

When a new SSA value is created, its subscript is initialized to the **stack
birth depth** at that point:

- `v_0` is the bottom of the stack.
- `v_n` is the top at depth `n`.

This gives stable, intuitive names outside loops.

## Loop indexing overview

Repeat loops require subscripts that change with the loop counter. The lifter:

1. **Computes slot movement per iteration** (see below).
2. **Adds a loop term** to the subscript for values whose slot moves linearly.

Subscripts are adjusted by:

```
subscript := subscript + delta * loop_var
```

where `delta` is the per-iteration movement of the slot (positive for producing,
and negative for consuming loops).

### Why this is correct

- `SlotId` tracks stack _slots_ across instructions.
- If a slot moves linearly with each iteration, its corresponding values must be
  indexed by that linear term to reflect which entry value is used each time.
- If the slot does **not** move, then the value is loop-carried and the subscript
  should remain constant.

If slot movement is non-linear or unstable, the lifter returns
`UnsupportedRepeatPattern`.

## Computing slot movement (`compute_slot_indices`)

The lifter compares the **entry stack** to the **exit stack** after one iteration.
If the loop executes more than once, it also compares the exit stack after the
second iteration. This detects whether slots move linearly.

- `delta = exit_pos - entry_pos` for steady slots.
- For consumed slots, `delta = -consumed_stride`.
- For produced slots, `delta` is derived from exit → exit2 movement.

If the movement is inconsistent across iterations, the loop is rejected.

## Consuming loops (`delta < 0`)

In consuming loops, the same stack position in the body refers to _different
entry values_ over time. To represent this correctly:

- Entry values that are consumed are rewritten to `VarBase::LoopInput`.
- Their subscripts receive a **negative** loop term.

Example:

```
repeat.4
  add
end
```

Body output:

```
for i in 0..4 {
  v_3 = v_3 + v_(4 - i);
}
```

The term `v_(4 - i)` represents a _different input_ each iteration.

## Producing loops (`delta > 0`)

Produced values (created in the loop body in produced slots) are indexed by the
loop counter to give a unique name per iteration.

Example:

```
repeat.4
  push.0
end
```

Output:

```
for i in 0..4 {
  v_i = 0;
}
```

## Neutral loops (`delta == 0`)

No subscript adjustment is applied. Loop-carried values are represented as
ordinary assignments with constant subscripts.

## Correctness arguments

The subscript analysis is correct because:

1. **Slot identity is stable** across stack moves.
2. **Linear movement is enforced** (otherwise the loop is rejected).
3. **Loop-input bases are used** whenever a single stack position corresponds
   to different entry values across iterations.
4. **Loop-carried values keep constant subscripts**, which matches their
   semantic identity across iterations.

These rules ensure the printed variable names correspond to the correct
underlying values at each iteration.

## Related document

- `SSA.md` — broader SSA lifting design and control-flow handling.
