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

4. **Compute subscripts** (`subscripts::compute_subscripts`): Assign symbolic subscripts
   based on stack depth tracking and loop context.

5. **Reindex variables** (`reindex_vars::apply`): Remap sparse SSA indices to dense
   sequential indices and propagate subscripts through equivalence classes.

6. **Final simplification**: One more simplify pass for cleanup.

## Variable Subscript System

Variables (`Var`) have two components:

- `index`: A unique identifier for the logical variable
- `subscript`: Tracks loop iteration context (`None`, `Const(n)`, or symbolic expressions)

### Subscript Assignment Algorithm (`subscripts.rs`)

The subscript system uses **stack-depth-based tracking** to assign meaningful subscripts
that reflect a variable's position in the stack at different points in execution.

#### Data Structures

**`var_depths: HashMap<usize, usize>`** (stored on `Cfg`):
- Maps variable index to its "birth depth" (stack depth when created)
- Populated during SSA lifting as variables are allocated
- For consuming loop outputs, updated to reflect final position after the loop

**`loop_contexts: HashMap<NodeId, LoopContext>`** (stored on `Cfg`):
- Records context for each repeat loop
- `LoopContext` contains:
  - `loop_var_index`: The loop counter variable's index
  - `entry_depth`: Stack depth when entering the loop
  - `effect_per_iter`: Net stack change per iteration (+1 for producing, -1 for consuming)
  - `iter_count`: Number of iterations

#### Algorithm Overview

1. **During SSA lifting**: Record birth depths for all variables as they're created.
   For consuming loops, `compute_repeat_exit_frame` updates depths of output variables
   to their final positions (e.g., position 0 for a loop that reduces to one value).

2. **During structuring**: `compute_subscripts` walks the code and assigns subscripts:

   - **Outside loops**: Variables get `Const(birth_depth)` subscripts

   - **Inside producing loops** (effect > 0): Variables born inside get symbolic
     subscripts: `base_offset + effect * loop_var` where `base_offset` is the
     position within one iteration

   - **Inside consuming loops** (effect < 0): Special handling for binary operations:
     - First operand (top of stack): `(entry_depth - 1) - loop_var`
     - Second operand: `(entry_depth - 2) - loop_var`
     - Destination: `(entry_depth - 2) - loop_var`

#### Example: Consuming Loop `repeat.4 { add }`

Input: Stack `[v_0, v_1, v_2, v_3, v_4]` (depth 5)

Loop context:
- `entry_depth = 5`
- `effect_per_iter = -1`
- `iter_count = 4`

Subscript assignment for the `add` operation:
- First operand: `(5-1) - i = 4 - i` → reads `v_(4-i)`
- Second operand: `(5-2) - i = 3 - i` → reads `v_(3-i)`
- Destination: `(5-2) - i = 3 - i` → writes `v_(3-i)`

Output:
```
for i in 0..4 {
  v_(3 - i) = v_(4 - i) + v_(3 - i);
}
return v_0;
```

The return value has subscript 0 because `compute_repeat_exit_frame` updated
the output variable's depth to position 0 (final stack has 1 element).

### Dead Code Elimination Interaction

DCE runs BEFORE structuring, so it sees variables with mismatched subscripts:

- Loop body defines: `Var { index: 0, subscript: None }`
- Return uses: `Var { index: 0, subscript: Const(0) }`

The DCE in `analysis/dead_code_elimination.rs` handles this by using **index-based
liveness**: if ANY variable with a given index is used, ALL definitions with that
index are kept alive. This is documented in detail in that file.

## Variable Reindexing (`reindex_vars.rs`)

The reindexing pass remaps sparse SSA indices to dense sequential indices for
readable output. This is distinct from `compute_subscripts`, which assigns the
**semantic** subscript values based on stack positions and loop context.

### Separation of Concerns

| Phase | Responsibility |
|-------|----------------|
| `compute_subscripts` | Assigns subscript **values** using stack semantics and CFG metadata |
| `reindex_vars` | Remaps SSA **indices** to dense form and propagates subscripts |

The `compute_subscripts` phase requires CFG metadata (`var_depths`, `loop_contexts`)
that is only available before flattening. The `reindex_vars` phase operates purely
on the code structure and doesn't need this metadata.

### Algorithm

1. **Collect claimed subscripts**: Scan code for variables that already have concrete
   subscripts (assigned by `compute_subscripts`). These values are "claimed" and
   won't be reused for other variables.

2. **Build equivalence classes**: Variables connected via phi nodes or carrier
   assignments form equivalence classes. All variables in a class get the same
   final index.

3. **Build index mapping**: Map original sparse SSA indices to dense sequential
   indices (e.g., {7, 42, 100} → {0, 1, 2}). LoopVar indices are also added to
   this mapping.

4. **Assign class subscripts**: If any variable in an equivalence class has a
   subscript (from `compute_subscripts`), propagate it to the class. Otherwise,
   allocate a new subscript that doesn't conflict with claimed values.

5. **Reindex the code**: Walk all statements, updating indices to use the dense
   mapping. Transform `LoopVar(old_idx)` references in symbolic subscripts to
   `LoopVar(new_idx)`.

### Key Assumptions

1. **Equivalence classes are built once**: The top-level `build_carrier_classes`
   recursively walks ALL nested blocks (If, While, Repeat). Inner blocks don't
   need to rebuild classes.

2. **Loop variables don't get numeric subscripts**: Variables declared as loop
   counters (`Stmt::Repeat { loop_var, .. }`) keep subscript `None`. The formatter
   handles them specially.

3. **Index consistency**: Once a subscript is allocated for an index, it's cached
   in `index_subscripts` to ensure the same variable always gets the same subscript.

### Why Both Phases Are Necessary

- Without `compute_subscripts`: Variables would have no meaningful subscripts
  reflecting their stack positions or loop iteration context.

- Without `reindex_vars`: SSA indices would be sparse (e.g., v_7, v_42, v_100
  instead of v_0, v_1, v_2), equivalence classes wouldn't be detected, and
  `LoopVar` references in subscripts would point to stale indices after the
  index remapping.

## Consuming vs Producing Loops

**Producing loops** (positive stack delta per iteration):

- Push values onto the stack
- Each iteration's output gets a unique subscript
- Example: `repeat.4 { push.0 }` produces `v_0, v_1, v_2, v_3`
- Variables inside the loop body get symbolic subscripts like `base + effect * i`

**Consuming loops** (negative stack delta per iteration):

- Consume values from the stack
- Stack positions decrease with each iteration
- Example: `repeat.4 { add }` consumes 4 pairs, produces 1 final sum
- Variables get decreasing symbolic subscripts like `(entry - 1) - i`

### Carrier Assignment Handling

The SSA lifting phase generates carrier assignments (simple var-to-var copies) to
maintain values across loop iterations. These are processed during subscript
assignment but don't affect the stack effect calculation (they're not binary ops).

For example, `repeat.2 { add }` might have a body like:

```
v_carrier = input      (maintaining a value for next iteration)
v_add = v_a + v_b      (the actual add operation)
```

The carrier assignment uses birth-depth based subscripts, while the add operation
uses stack-position arithmetic for its operands and destination.

## Known Limitations

1. **Conservative DCE**: The index-based liveness in DCE may keep some dead code
   alive if unrelated variables happen to share an index (shouldn't happen in
   proper SSA, but could occur in edge cases).

2. **Constant propagation into repeat loops**: When constant values are pushed
   before a repeat loop, expression propagation may inline those constants into
   the loop body, producing semantically incorrect output. For example,
   `push.3.4; repeat.2 { add }` might produce:

   ```
   for i in 0..2 {
     v_(1 - i) = 3 + 4;  // Wrong: should be v_(2-i) + v_(1-i)
   }
   ```

   This is a pre-existing issue in expression propagation that doesn't properly
   account for loop-iteration semantics. With symbolic inputs (no constants),
   repeat loops produce correct output:

   ```
   for i in 0..4 {
     v_(3 - i) = v_(4 - i) + v_(3 - i);  // Correct
   }
   ```
