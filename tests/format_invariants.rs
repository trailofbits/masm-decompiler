//! Invariant checks for printed names and SSA identities.

mod common;

use common::{assert_names_defined_when_used, decompile_no_optimizations};
use masm_decompiler::fmt::assign_var_names;
use masm_decompiler::frontend::testing::workspace_from_modules;
use masm_decompiler::ir::{Expr, IndexExpr, Stmt, ValueId, Var, VarBase};
use std::collections::{HashMap, HashSet};

/// Identity key for relating printed names to SSA identity.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct IdentityKey {
    /// Base identity for the variable.
    base: VarBase,
    /// Subscript expression for the variable.
    subscript: IndexExpr,
}

/// Collect all variables that appear in printed statements.
fn collect_printed_vars(stmts: &[Stmt]) -> Vec<Var> {
    let mut vars = Vec::new();
    for stmt in stmts {
        collect_stmt_vars(stmt, &mut vars);
    }
    vars
}

/// Collect variables used in a single statement that appears in output.
fn collect_stmt_vars(stmt: &Stmt, vars: &mut Vec<Var>) {
    match stmt {
        Stmt::Assign { dest, expr, .. } => {
            vars.push(dest.clone());
            collect_expr_vars(expr, vars);
        }
        Stmt::MemLoad { load, .. } => {
            vars.extend(load.address.iter().cloned());
            vars.extend(load.outputs.iter().cloned());
        }
        Stmt::MemStore { store, .. } => {
            vars.extend(store.address.iter().cloned());
            vars.extend(store.values.iter().cloned());
        }
        Stmt::AdvLoad { load, .. } => {
            vars.extend(load.outputs.iter().cloned());
        }
        Stmt::AdvStore { store, .. } => {
            vars.extend(store.values.iter().cloned());
        }
        Stmt::LocalLoad { load, .. } => {
            vars.extend(load.outputs.iter().cloned());
        }
        Stmt::LocalStore { store, .. } => {
            vars.extend(store.values.iter().cloned());
        }
        Stmt::LocalStoreW { store, .. } => {
            vars.extend(store.values.iter().cloned());
        }
        Stmt::Call { call, .. } | Stmt::Exec { call, .. } | Stmt::SysCall { call, .. } => {
            vars.extend(call.args.iter().cloned());
            vars.extend(call.results.iter().cloned());
        }
        Stmt::DynCall { args, results, .. } => {
            vars.extend(args.iter().cloned());
            vars.extend(results.iter().cloned());
        }
        Stmt::Intrinsic { intrinsic, .. } => {
            vars.extend(intrinsic.args.iter().cloned());
            vars.extend(intrinsic.results.iter().cloned());
        }
        Stmt::Repeat { body, .. } | Stmt::While { body, .. } => {
            for stmt in body {
                collect_stmt_vars(stmt, vars);
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            ..
        } => {
            collect_expr_vars(cond, vars);
            for stmt in then_body {
                collect_stmt_vars(stmt, vars);
            }
            for stmt in else_body {
                collect_stmt_vars(stmt, vars);
            }
        }
        Stmt::Return {
            values: vars_out, ..
        } => {
            vars.extend(vars_out.iter().cloned());
        }
    }
}

/// Collect variables used in an expression.
fn collect_expr_vars(expr: &Expr, vars: &mut Vec<Var>) {
    match expr {
        Expr::Var(v) => vars.push(v.clone()),
        Expr::Binary(_, lhs, rhs) => {
            collect_expr_vars(lhs, vars);
            collect_expr_vars(rhs, vars);
        }
        Expr::Unary(_, inner) => collect_expr_vars(inner, vars),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_vars(cond, vars);
            collect_expr_vars(then_expr, vars);
            collect_expr_vars(else_expr, vars);
        }
        Expr::EqW { lhs, rhs } => {
            vars.extend(lhs.iter().cloned());
            vars.extend(rhs.iter().cloned());
        }
        Expr::True | Expr::False | Expr::Constant(_) => {}
    }
}

/// Assert that printed names map to equivalent identities and each SSA value ID
/// maps to a single printed name.
fn assert_name_identity_invariants(stmts: &[Stmt]) {
    let names = assign_var_names(stmts);
    let vars = collect_printed_vars(stmts);

    let mut name_identities: HashMap<String, HashSet<IdentityKey>> = HashMap::new();
    let mut value_id_names: HashMap<ValueId, HashSet<String>> = HashMap::new();

    for var in vars {
        let name = names
            .get(&var)
            .unwrap_or_else(|| panic!("missing name for var: {var:?}"))
            .clone();
        let identity = IdentityKey {
            base: var.base.clone(),
            subscript: var.subscript.clone(),
        };
        name_identities
            .entry(name.clone())
            .or_default()
            .insert(identity);

        if let VarBase::Value(id) = var.base {
            value_id_names.entry(id).or_default().insert(name);
        }
    }

    let mut parents = HashMap::new();
    collect_phi_equivalences(stmts, &mut parents);

    for (name, identities) in &name_identities {
        let mut reps = HashSet::new();
        for identity in identities {
            reps.insert(find_rep(&mut parents, identity));
        }
        assert!(
            reps.len() == 1,
            "printed name `{}` refers to multiple non-equivalent identities: {:?}",
            name,
            identities
        );
    }

    for (id, names) in &value_id_names {
        assert!(
            names.len() == 1,
            "value id {:?} maps to multiple printed names: {:?}",
            id,
            names
        );
    }
}

/// Collect phi-related equivalence classes for identities.
fn collect_phi_equivalences(stmts: &[Stmt], parents: &mut HashMap<IdentityKey, IdentityKey>) {
    for stmt in stmts {
        match stmt {
            Stmt::If {
                then_body,
                else_body,
                phis,
                ..
            } => {
                for phi in phis {
                    union_identities(
                        parents,
                        &identity_key(&phi.dest),
                        &identity_key(&phi.then_var),
                    );
                    union_identities(
                        parents,
                        &identity_key(&phi.dest),
                        &identity_key(&phi.else_var),
                    );
                }
                collect_phi_equivalences(then_body, parents);
                collect_phi_equivalences(else_body, parents);
            }
            Stmt::While { body, phis, .. } | Stmt::Repeat { body, phis, .. } => {
                for phi in phis {
                    union_identities(parents, &identity_key(&phi.dest), &identity_key(&phi.init));
                    union_identities(parents, &identity_key(&phi.dest), &identity_key(&phi.step));
                }
                collect_phi_equivalences(body, parents);
            }
            _ => {}
        }
    }
}

/// Build an identity key for a variable.
fn identity_key(var: &Var) -> IdentityKey {
    IdentityKey {
        base: var.base.clone(),
        subscript: var.subscript.clone(),
    }
}

/// Find the representative identity for a key.
fn find_rep(parents: &mut HashMap<IdentityKey, IdentityKey>, key: &IdentityKey) -> IdentityKey {
    let parent = parents
        .entry(key.clone())
        .or_insert_with(|| key.clone())
        .clone();
    if &parent == key {
        return parent;
    }
    let rep = find_rep(parents, &parent);
    parents.insert(key.clone(), rep.clone());
    rep
}

/// Union two identity keys into the same equivalence class.
fn union_identities(
    parents: &mut HashMap<IdentityKey, IdentityKey>,
    a: &IdentityKey,
    b: &IdentityKey,
) {
    let ra = find_rep(parents, a);
    let rb = find_rep(parents, b);
    if ra != rb {
        parents.insert(rb, ra);
    }
}

/// Ensure printed-name and identity invariants hold for fixtures.
#[test]
fn printed_names_are_identity_stable() {
    let ws = workspace_from_modules(&[
        ("u256", include_str!("fixtures/u256.masm")),
        ("repeat", include_str!("fixtures/repeat.masm")),
    ]);
    let procs = [
        "u256::wrapping_add",
        "u256::wrapping_sub",
        "u256::and",
        "u256::or",
        "u256::xor",
        "u256::eqz",
        "u256::mulstep",
        "u256::mulstep4",
        "repeat::neutral_repeat_0",
        "repeat::producing_repeat_0",
        "repeat::producing_repeat_1",
        "repeat::consuming_repeat_0",
        "repeat::consuming_repeat_1",
        "repeat::consuming_repeat_2",
        "repeat::nested_repeat_0",
    ];

    for proc in procs {
        let stmts = decompile_no_optimizations(&ws, proc);
        assert_name_identity_invariants(&stmts);
    }
}

/// Ensure all variables are defined before they are used in key fixtures.
#[test]
fn defined_when_used_invariants() {
    let ws = workspace_from_modules(&[
        ("u256", include_str!("fixtures/u256.masm")),
        ("repeat", include_str!("fixtures/repeat.masm")),
    ]);
    let procs = [
        // u256
        "u256::wrapping_add",
        "u256::wrapping_sub",
        "u256::and",
        "u256::or",
        "u256::xor",
        "u256::eqz",
        "u256::mulstep",
        "u256::mulstep4",
        // repeat
        "repeat::neutral_repeat_0",
        "repeat::producing_repeat_0",
        "repeat::producing_repeat_1",
        "repeat::consuming_repeat_0",
        "repeat::consuming_repeat_1",
        "repeat::consuming_repeat_2",
        "repeat::nested_repeat_0",
    ];

    for proc in procs {
        let stmts = decompile_no_optimizations(&ws, proc);
        assert_names_defined_when_used(proc, &stmts);
    }
}
