//! Lightweight passthrough analysis for procedure inputs/outputs.
//!
//! Determines which procedure outputs are unmodified copies of inputs by
//! tracing variable origins through copies, phi nodes, and call results.
//! This is a standalone analysis — it does not depend on the type lattice.

use std::collections::HashMap;

use crate::ir::{Expr, Stmt, ValueId, Var};
use crate::types::{TypeSummaryMap, VarKey};

/// Compute the output-to-input passthrough map for a procedure.
///
/// Returns a vector where `result[i] == Some(j)` means output position `i`
/// is an unmodified copy of input position `j` (0 = deepest stack element).
///
/// The analysis traces origins through copy assignments, ternary selects,
/// if-phi merges, loop-phi merges, and call/exec results with known
/// passthrough summaries. It iterates to a fixed point so nested loops
/// are handled correctly.
///
/// `callee_summaries` provides passthrough maps for callees. When `None`,
/// all call/exec results are treated as computed (no inter-procedural
/// passthrough propagation).
pub fn compute_passthrough_map(
    stmts: &[Stmt],
    input_count: usize,
    output_count: usize,
    callee_summaries: Option<&TypeSummaryMap>,
) -> Vec<Option<usize>> {
    let origins = compute_origins(stmts, input_count, callee_summaries);

    let return_values = find_return_values(stmts);
    let mut map = Vec::with_capacity(output_count);
    for index in (0..output_count).rev() {
        let origin = return_values
            .and_then(|values| values.get(index))
            .and_then(|var| origins.get(&VarKey::from_var(var)))
            .copied()
            .unwrap_or(Origin::Computed);
        match origin {
            Origin::Input(i) => map.push(Some(i)),
            Origin::Computed => map.push(None),
        }
    }
    map
}

// --- Internal types and helpers ---

/// Provenance of a variable value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Origin {
    /// Unmodified copy of procedure input at given index (0 = deepest).
    Input(usize),
    /// Produced by a computation or incompatible merge.
    Computed,
}

/// Build the canonical VarKey for input variable at depth-based `index`.
///
/// Uses the same convention as the lifter: `Var::new(ValueId(index), index)`.
fn input_var_key(index: usize) -> VarKey {
    let var = Var::new(ValueId::new(index as u64), index);
    VarKey::from_var(&var)
}

/// Find the top-level return statement values.
fn find_return_values(stmts: &[Stmt]) -> Option<&[Var]> {
    for stmt in stmts {
        if let Stmt::Return { values, .. } = stmt {
            return Some(values);
        }
    }
    None
}

/// Merge two origins: both must agree on the same input, otherwise Computed.
fn merge_origins(a: Origin, b: Origin) -> Origin {
    match (a, b) {
        (Origin::Input(i), Origin::Input(j)) if i == j => Origin::Input(i),
        _ => Origin::Computed,
    }
}

/// Look up the origin for a variable expression, or Computed if not a variable.
fn origin_of_expr(expr: &Expr, origins: &HashMap<VarKey, Origin>) -> Origin {
    match expr {
        Expr::Var(var) => origins
            .get(&VarKey::from_var(var))
            .copied()
            .unwrap_or(Origin::Computed),
        _ => Origin::Computed,
    }
}

/// Compute the origin of each variable, iterating to a fixed point.
fn compute_origins(
    stmts: &[Stmt],
    input_count: usize,
    callee_summaries: Option<&TypeSummaryMap>,
) -> HashMap<VarKey, Origin> {
    let mut origins: HashMap<VarKey, Origin> = HashMap::new();

    // Seed input variables.
    for index in 0..input_count {
        origins.insert(input_var_key(index), Origin::Input(index));
    }

    // Fixed-point iteration. Each pass can only demote Input → Computed
    // (monotonic), so convergence is guaranteed.
    loop {
        let prev = origins.clone();
        propagate_block(stmts, &mut origins, callee_summaries);
        if origins == prev {
            break;
        }
    }

    origins
}

/// Propagate origins through a statement block.
fn propagate_block(
    stmts: &[Stmt],
    origins: &mut HashMap<VarKey, Origin>,
    callee_summaries: Option<&TypeSummaryMap>,
) {
    for stmt in stmts {
        propagate_stmt(stmt, origins, callee_summaries);
    }
}

/// Propagate origins through a single statement.
fn propagate_stmt(
    stmt: &Stmt,
    origins: &mut HashMap<VarKey, Origin>,
    callee_summaries: Option<&TypeSummaryMap>,
) {
    match stmt {
        Stmt::Assign { dest, expr, .. } => {
            let origin = match expr {
                Expr::Var(src) => origins
                    .get(&VarKey::from_var(src))
                    .copied()
                    .unwrap_or(Origin::Computed),
                Expr::Ternary {
                    then_expr,
                    else_expr,
                    ..
                } => merge_origins(
                    origin_of_expr(then_expr, origins),
                    origin_of_expr(else_expr, origins),
                ),
                _ => Origin::Computed,
            };
            origins.insert(VarKey::from_var(dest), origin);
        }

        Stmt::If {
            then_body,
            else_body,
            phis,
            ..
        } => {
            propagate_block(then_body, origins, callee_summaries);
            propagate_block(else_body, origins, callee_summaries);
            for phi in phis {
                let then_origin = origins
                    .get(&VarKey::from_var(&phi.then_var))
                    .copied()
                    .unwrap_or(Origin::Computed);
                let else_origin = origins
                    .get(&VarKey::from_var(&phi.else_var))
                    .copied()
                    .unwrap_or(Origin::Computed);
                origins.insert(
                    VarKey::from_var(&phi.dest),
                    merge_origins(then_origin, else_origin),
                );
            }
        }

        Stmt::While { body, phis, .. } | Stmt::Repeat { body, phis, .. } => {
            for phi in phis {
                let init_origin = origins
                    .get(&VarKey::from_var(&phi.init))
                    .copied()
                    .unwrap_or(Origin::Computed);
                let current = origins
                    .get(&VarKey::from_var(&phi.dest))
                    .copied()
                    .unwrap_or(init_origin);
                origins.insert(
                    VarKey::from_var(&phi.dest),
                    merge_origins(current, init_origin),
                );
            }
            propagate_block(body, origins, callee_summaries);
            for phi in phis {
                let dest_origin = origins
                    .get(&VarKey::from_var(&phi.dest))
                    .copied()
                    .unwrap_or(Origin::Computed);
                let step_origin = origins
                    .get(&VarKey::from_var(&phi.step))
                    .copied()
                    .unwrap_or(Origin::Computed);
                origins.insert(
                    VarKey::from_var(&phi.dest),
                    merge_origins(dest_origin, step_origin),
                );
            }
        }

        Stmt::Call { call, .. } | Stmt::Exec { call, .. } | Stmt::SysCall { call, .. } => {
            let callee_map = callee_summaries
                .and_then(|s| s.get(&crate::SymbolPath::new(call.target.to_string())))
                .map(|s| &s.output_input_map);
            for (idx, result) in call.results.iter().enumerate() {
                let origin = if let Some(Some(input_idx)) = callee_map.and_then(|m| m.get(idx)) {
                    call.args
                        .len()
                        .checked_sub(1 + *input_idx)
                        .and_then(|i| call.args.get(i))
                        .and_then(|arg| origins.get(&VarKey::from_var(arg)).copied())
                        .unwrap_or(Origin::Computed)
                } else {
                    Origin::Computed
                };
                origins.insert(VarKey::from_var(result), origin);
            }
        }

        Stmt::DynCall { results, .. } => {
            for result in results {
                origins.insert(VarKey::from_var(result), Origin::Computed);
            }
        }

        Stmt::Intrinsic { intrinsic, .. } => {
            for result in &intrinsic.results {
                origins.insert(VarKey::from_var(result), Origin::Computed);
            }
        }

        Stmt::MemLoad { load, .. } => {
            for output in &load.outputs {
                origins.insert(VarKey::from_var(output), Origin::Computed);
            }
        }

        Stmt::LocalLoad { load, .. } => {
            for output in &load.outputs {
                origins.insert(VarKey::from_var(output), Origin::Computed);
            }
        }

        Stmt::AdvLoad { load, .. } => {
            for output in &load.outputs {
                origins.insert(VarKey::from_var(output), Origin::Computed);
            }
        }

        Stmt::MemStore { .. }
        | Stmt::AdvStore { .. }
        | Stmt::LocalStore { .. }
        | Stmt::LocalStoreW { .. }
        | Stmt::Return { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::callgraph::CallGraph;
    use crate::frontend::testing::workspace_from_modules;
    use crate::lift::lift_proc;
    use crate::signature::infer_signatures;
    use crate::symbol::resolution::create_resolver;

    /// Helper: lift a single procedure and compute its passthrough map.
    fn passthrough_map_for(source: &str, proc_name: &str) -> Vec<Option<usize>> {
        use crate::signature::ProcSignature;

        let ws = workspace_from_modules(&[("test", source)]);
        let callgraph = CallGraph::from(&ws);
        let signatures = infer_signatures(&ws, &callgraph);
        let proc_path = crate::SymbolPath::new(format!("test::{proc_name}"));
        let (program, proc) = ws.lookup_proc_entry(&proc_path).unwrap();
        let resolver = create_resolver(program.module(), ws.source_manager());
        let stmts = lift_proc(proc, &proc_path, &resolver, &signatures).unwrap();

        let sig = signatures.get(&proc_path).unwrap();
        let (inputs, outputs) = match sig {
            ProcSignature::Known {
                inputs, outputs, ..
            } => (*inputs, *outputs),
            ProcSignature::Unknown => panic!("expected Known signature for {proc_name}"),
        };
        compute_passthrough_map(&stmts, inputs, outputs, None)
    }

    #[test]
    fn computed_output_with_passthrough_underneath() {
        // proc foo: takes 1 input, duplicates it, then adds 1 to the copy.
        // Stack: [x] -> [x, x] -> [x, x, 1] -> [x, x+1]
        // The top of the stack is computed (x+1), the bottom is the original
        // input (passthrough). Signature: 1 input, 2 outputs.
        let source = "proc foo\n  dup.0\n  push.1\n  add\nend\n";
        let map = passthrough_map_for(source, "foo");
        assert_eq!(map, vec![Some(0), None]);
    }

    #[test]
    fn computed_output_is_none() {
        // proc foo: takes 1 input, returns a constant
        let source = "proc foo\n  drop\n  push.42\nend\n";
        let map = passthrough_map_for(source, "foo");
        assert_eq!(map, vec![None]);
    }

    #[test]
    fn swap_passthroughs() {
        // proc foo: takes 2 inputs, swaps them.
        // Signature: 2 inputs, 2 outputs (positions changed).
        // Both outputs are passthroughs of the original inputs.
        let source = "proc foo\n  swap\nend\n";
        let map = passthrough_map_for(source, "foo");
        // Both should be Some(_) (swapped inputs).
        assert!(
            map.iter().all(|m| m.is_some()),
            "swap should produce all-passthrough: {map:?}"
        );
        assert_ne!(
            map[0], map[1],
            "swapped outputs should trace to different inputs: {map:?}"
        );
    }
}
