# Structuring Module

This module transforms a CFG with branch markers into structured statements (`If`,
`While`, `Repeat`) and assigns final variable names for output.

## Pipeline Overview

The structuring pipeline in `structure()` follows these steps:

1. **Lower loop phis** (`lower_loop_phis_with_cfg`): Convert phi nodes at loop headers
   into explicit initialization and update assignments while CFG edge info is available.

2. **Flatten control flow** (`flatten::flatten_control_flow`): Convert CFG to a flat
   sequence of structured statements.

3. **Cleanup passes**: Remove nops, refine conditions, hoist shared conditions, prune
   side effects, simplify expressions.

4. **Apply loop subscripts** (`apply_loop_subscripts`): Assign symbolic subscripts
   (e.g., `LoopVar(idx)`) to variables inside loop bodies.

5. **Rename variables** (`rename_vars::apply`): Assign dense indices and resolve
   subscript conflicts.

6. **Final simplification**: One more simplify pass for cleanup.

## Variable Subscript System

Variables (`Var`) have two components:

- `index`: A unique identifier for the logical variable
- `subscript`: Tracks loop iteration context (`None`, `Const(n)`, or `LoopVar(idx)`)

### Subscript Assignment Phases

Subscripts are assigned in TWO phases:

1. **During SSA lifting** (`ssa/lift/mod.rs:compute_repeat_exit_frame`):
   Variables that ESCAPE a producing repeat loop get concrete subscripts.
   For a `repeat.4` loop, escaped values get subscripts `Const(0)`, `Const(1)`,
   `Const(2)`, `Const(3)`.

2. **During structuring** (`apply_loop_subscripts` via `loop_indices.rs`):
   Variables INSIDE loop bodies get symbolic subscripts like `LoopVar(idx)`.
   These represent "the value at iteration i" rather than a specific iteration.

This split exists because:

- SSA lifting needs concrete values to compute the stack frame that exits the loop
- Structuring needs symbolic subscripts for human-readable output (`v_i`)

### Dead Code Elimination Interaction

DCE runs BEFORE structuring, so it sees variables with mismatched subscripts:

- Loop body defines: `Var { index: 0, subscript: None }`
- Return uses: `Var { index: 0, subscript: Const(0) }`

The DCE in `analysis/dead_code_elimination.rs` handles this by using **index-based
liveness**: if ANY variable with a given index is used, ALL definitions with that
index are kept alive. This is documented in detail in that file.

## Variable Renaming (`rename_vars.rs`)

The renaming pass assigns dense indices and subscripts for final output.

### Algorithm

1. **Collect claimed subscripts**: Scan code for variables that already have concrete
   subscripts (from SSA lifting). These values are "claimed" and won't be reused.

2. **Build equivalence classes**: Variables connected via phi nodes or carrier
   assignments form equivalence classes. All variables in a class get the same
   final index.

3. **Build index mapping**: Map original indices to dense sequential indices.
   LoopVar references in subscripts are also remapped.

4. **Assign class subscripts**: If any variable in an equivalence class has a
   concrete subscript, use it. Otherwise, allocate a new subscript that doesn't
   conflict with claimed values.

5. **Rename the code**: Walk all statements, updating indices and subscripts.
   Variables without subscripts get one from their class or a newly allocated one.

### Key Assumptions

1. **Equivalence classes are built once**: The top-level `build_carrier_classes`
   recursively walks ALL nested blocks (If, While, Repeat). Inner blocks don't
   need to rebuild classes.

2. **Loop variables don't get numeric subscripts**: Variables declared as loop
   counters (`Stmt::Repeat { loop_var, .. }`) keep subscript `None`. The formatter
   handles them specially.

3. **Index consistency**: Once a subscript is allocated for an index, it's cached
   in `index_subscripts` to ensure the same variable always gets the same subscript.

### Restrictions

1. **Subscript conflicts**: If a loop claims subscripts 0-3, non-loop variables
   must use 4+. The `claimed` set and `find_next_free_subscript` handle this.

2. **LoopVar remapping**: When indices are remapped, `IndexExpr::LoopVar(idx)`
   references must also be updated to point to the new index.

## Consuming vs Producing Loops

**Producing loops** (positive stack delta per iteration):

- Push values onto the stack
- Each iteration's output gets a unique subscript
- Example: `repeat.4 { push.0 }` produces `v_0, v_1, v_2, v_3`
- Variables inside the loop body get `LoopVar(idx)` subscripts

**Consuming loops** (negative or zero stack delta):

- Consume values from the stack
- Variables may be loop-carried (updated each iteration)
- The `carriers` set from `lower_loop_phis_with_cfg` tracks these relationships
- Variables get simple numeric subscripts (no `LoopVar` expressions)

### Carrier Assignment Handling

The SSA lifting phase generates carrier assignments (simple var-to-var copies) to
maintain values across loop iterations. In `loop_indices.rs`, `summarize_stmt`
treats these as no-ops (effect 0,0, no outputs) to prevent them from inflating
the delta calculation. Without this, a consuming loop with carrier assignments
would appear to be a producing loop.

For example, `repeat.2 { add }` might have a body like:

```
phi1, phi2  (iteration state)
v_add = phi1 + phi2    (the actual add)
v_carrier = input      (maintaining a value)
```

Without carrier handling: `outputs=2, pops=2, delta=0` → still wrong
With carrier handling: the carrier is a `Var` copy, so `outputs=1, pops=2, delta=0`

## Known Limitations

1. **Duplicate stack simulation**: `loop_indices.rs` and `ssa/lift/repeat.rs` both
   contain stack simulation logic (`summarize_stmt`, `effect_parts`, etc.). This
   duplication exists because they operate at different phases and on slightly
   different statement sets.

2. **Conservative DCE**: The index-based liveness in DCE may keep some dead code
   alive if unrelated variables happen to share an index (shouldn't happen in
   proper SSA, but could occur in edge cases).
