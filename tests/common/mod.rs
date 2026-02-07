#![allow(dead_code)]

pub mod strategies;

use masm_decompiler::{
    decompile::{DecompilationConfig, Decompiler},
    fmt::assign_var_names,
    frontend::Workspace,
    ir::{Expr, IndexExpr, Stmt, ValueId, Var, VarBase},
};
use std::collections::HashSet;

/// Decompile a procedure with the default configuration (all optimizations enabled).
pub fn decompile(ws: &Workspace, proc_name: &str, _module: &str) -> Vec<Stmt> {
    let decompiler = Decompiler::new(ws);
    decompiler
        .decompile_proc(proc_name)
        .expect("decompilation should succeed")
        .body
        .stmts
        .clone()
}

/// Decompile a procedure with custom configuration.
pub fn decompile_with_config(
    ws: &Workspace,
    proc_name: &str,
    config: DecompilationConfig,
) -> Vec<Stmt> {
    let decompiler = Decompiler::new(ws).with_config(config);
    decompiler
        .decompile_proc(proc_name)
        .expect("decompilation should succeed")
        .body
        .stmts
        .clone()
}

/// Decompile a procedure without expression or copy propagation (for debugging).
pub fn decompile_no_propagation(ws: &Workspace, proc_name: &str, _module: &str) -> Vec<Stmt> {
    let config = DecompilationConfig::default().with_expression_propagation(false);
    let decompiler = Decompiler::new(ws).with_config(config);
    decompiler
        .decompile_proc(proc_name)
        .expect("decompilation should succeed")
        .body
        .stmts
        .clone()
}

/// Decompile with no optimizations at all.
pub fn decompile_no_optimizations(ws: &Workspace, proc_name: &str) -> Vec<Stmt> {
    let decompiler = Decompiler::new(ws).with_config(DecompilationConfig::no_optimizations());
    decompiler
        .decompile_proc(proc_name)
        .expect("decompilation should succeed")
        .body
        .stmts
        .clone()
}

// Legacy aliases for backward compatibility
pub fn run_structure(ws: &Workspace, proc_name: &str, module: &str) -> Vec<Stmt> {
    decompile(ws, proc_name, module)
}

/// Linear subscript expression of the form `base + step * loop_var`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LinearIndex {
    /// Constant term of the linear subscript.
    pub base: i64,
    /// Coefficient for the loop variable.
    pub step: i64,
    /// Loop nesting depth for the loop variable.
    pub loop_depth: usize,
}

/// Return the constant index value if the expression is a constant.
pub fn const_index(expr: &IndexExpr) -> Option<i64> {
    match expr {
        IndexExpr::Const(value) => Some(*value),
        _ => None,
    }
}

/// Return the constant index value if the variable subscript is a constant.
pub fn var_const_index(var: &Var) -> Option<i64> {
    const_index(&var.subscript)
}

/// Interpret an index expression as `base + step * loop_var` if possible.
pub fn linear_index(expr: &IndexExpr) -> Option<LinearIndex> {
    fn parse(expr: &IndexExpr) -> Option<(i64, Option<(usize, i64)>)> {
        match expr {
            IndexExpr::Const(value) => Some((*value, None)),
            IndexExpr::LoopVar(depth) => Some((0, Some((*depth, 1)))),
            IndexExpr::Add(lhs, rhs) => {
                let (base_l, term_l) = parse(lhs)?;
                let (base_r, term_r) = parse(rhs)?;
                let base = base_l + base_r;
                match (term_l, term_r) {
                    (None, None) => Some((base, None)),
                    (Some(term), None) | (None, Some(term)) => Some((base, Some(term))),
                    (Some((depth_l, step_l)), Some((depth_r, step_r))) if depth_l == depth_r => {
                        Some((base, Some((depth_l, step_l + step_r))))
                    }
                    _ => None,
                }
            }
            IndexExpr::Mul(lhs, rhs) => match (&**lhs, &**rhs) {
                (IndexExpr::Const(c), other) | (other, IndexExpr::Const(c)) => {
                    let (base, term) = parse(other)?;
                    let base = base * *c;
                    let term = term.map(|(depth, step)| (depth, step * *c));
                    Some((base, term))
                }
                _ => None,
            },
        }
    }

    let (base, term) = parse(expr)?;
    let (loop_depth, step) = term?;
    Some(LinearIndex {
        base,
        step,
        loop_depth,
    })
}

/// Interpret a variable subscript as `base + step * loop_var` if possible.
pub fn var_linear_index(var: &Var) -> Option<LinearIndex> {
    linear_index(&var.subscript)
}

/// Collect used and defined value identifiers in structured statements.
pub fn collect_used_defined_value_ids(stmts: &[Stmt]) -> (HashSet<ValueId>, HashSet<ValueId>) {
    let mut used = HashSet::new();
    let mut defined = HashSet::new();
    for stmt in stmts {
        collect_stmt_ids(stmt, &mut used, &mut defined);
    }
    (used, defined)
}

/// Check that every variable use is defined (or is a loop input / procedure input).
///
/// Returns a list of error messages for any use-before-definition cases.
pub fn check_names_defined_when_used(stmts: &[Stmt]) -> Vec<String> {
    let names = assign_var_names(stmts);
    let (used, defined) = collect_used_defined_value_ids(stmts);
    let input_ids: HashSet<ValueId> = used.difference(&defined).cloned().collect();
    let mut defined_names = HashSet::new();

    for (var, name) in &names {
        if matches!(var.base, VarBase::Value(id) if input_ids.contains(&id)) {
            defined_names.insert(name.clone());
        }
    }

    let mut errors = Vec::new();
    check_stmt_list_defined(stmts, &names, &mut defined_names, &mut errors);
    errors
}

/// Traverse a statement list, tracking defined variable names.
fn check_stmt_list_defined(
    stmts: &[Stmt],
    names: &std::collections::HashMap<Var, String>,
    defined: &mut HashSet<String>,
    errors: &mut Vec<String>,
) {
    for stmt in stmts {
        check_stmt_defined(stmt, names, defined, errors);
    }
}

/// Traverse a single statement, updating defined variable names.
fn check_stmt_defined(
    stmt: &Stmt,
    names: &std::collections::HashMap<Var, String>,
    defined: &mut HashSet<String>,
    errors: &mut Vec<String>,
) {
    match stmt {
        Stmt::Assign { dest, expr } => {
            check_expr_defined(expr, names, defined, errors);
            define_var(dest, names, defined);
        }
        Stmt::MemLoad(load) => {
            for v in &load.address {
                check_var_defined(v, names, defined, errors);
            }
            for v in &load.outputs {
                define_var(v, names, defined);
            }
        }
        Stmt::MemStore(store) => {
            for v in &store.address {
                check_var_defined(v, names, defined, errors);
            }
            for v in &store.values {
                check_var_defined(v, names, defined, errors);
            }
        }
        Stmt::AdvLoad(load) => {
            for v in &load.outputs {
                define_var(v, names, defined);
            }
        }
        Stmt::AdvStore(store) => {
            for v in &store.values {
                check_var_defined(v, names, defined, errors);
            }
        }
        Stmt::LocalLoad(load) => {
            for v in &load.outputs {
                define_var(v, names, defined);
            }
        }
        Stmt::LocalStore(store) => {
            for v in &store.values {
                check_var_defined(v, names, defined, errors);
            }
        }
        Stmt::LocalStoreW(store) => {
            for v in &store.values {
                check_var_defined(v, names, defined, errors);
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in &call.args {
                check_var_defined(v, names, defined, errors);
            }
            for v in &call.results {
                define_var(v, names, defined);
            }
        }
        Stmt::DynCall { args, results } => {
            for v in args {
                check_var_defined(v, names, defined, errors);
            }
            for v in results {
                define_var(v, names, defined);
            }
        }
        Stmt::Intrinsic(intrinsic) => {
            for v in &intrinsic.args {
                check_var_defined(v, names, defined, errors);
            }
            for v in &intrinsic.results {
                define_var(v, names, defined);
            }
        }
        Stmt::Repeat {
            loop_var: _,
            loop_count: _,
            body,
            phis,
        } => {
            for phi in phis {
                check_var_defined(&phi.init, names, defined, errors);
            }
            let mut loop_defined = defined.clone();
            for phi in phis {
                define_var(&phi.dest, names, &mut loop_defined);
            }
            check_stmt_list_defined(body, names, &mut loop_defined, errors);
            for phi in phis {
                check_var_defined(&phi.step, names, &mut loop_defined, errors);
            }
            for phi in phis {
                define_var(&phi.dest, names, defined);
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            phis,
        } => {
            check_expr_defined(cond, names, defined, errors);
            let mut then_defined = defined.clone();
            let mut else_defined = defined.clone();
            check_stmt_list_defined(then_body, names, &mut then_defined, errors);
            check_stmt_list_defined(else_body, names, &mut else_defined, errors);
            for phi in phis {
                check_var_defined(&phi.then_var, names, &then_defined, errors);
                check_var_defined(&phi.else_var, names, &else_defined, errors);
                define_var(&phi.dest, names, defined);
            }
        }
        Stmt::While { cond, body, phis } => {
            check_expr_defined(cond, names, defined, errors);
            for phi in phis {
                check_var_defined(&phi.init, names, defined, errors);
            }
            let mut loop_defined = defined.clone();
            for phi in phis {
                define_var(&phi.dest, names, &mut loop_defined);
            }
            check_stmt_list_defined(body, names, &mut loop_defined, errors);
            for phi in phis {
                check_var_defined(&phi.step, names, &mut loop_defined, errors);
            }
            for phi in phis {
                define_var(&phi.dest, names, defined);
            }
        }
        Stmt::Return(vars) => {
            for v in vars {
                check_var_defined(v, names, defined, errors);
            }
        }
    }
}

/// Check that variables in an expression are defined.
fn check_expr_defined(
    expr: &Expr,
    names: &std::collections::HashMap<Var, String>,
    defined: &HashSet<String>,
    errors: &mut Vec<String>,
) {
    match expr {
        Expr::Var(v) => check_var_defined(v, names, defined, errors),
        Expr::Binary(_, lhs, rhs) => {
            check_expr_defined(lhs, names, defined, errors);
            check_expr_defined(rhs, names, defined, errors);
        }
        Expr::Unary(_, inner) => check_expr_defined(inner, names, defined, errors),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            check_expr_defined(cond, names, defined, errors);
            check_expr_defined(then_expr, names, defined, errors);
            check_expr_defined(else_expr, names, defined, errors);
        }
        Expr::True | Expr::False | Expr::Constant(_) => {}
    }
}

/// Record a variable definition in the current scope.
fn define_var(
    var: &Var,
    names: &std::collections::HashMap<Var, String>,
    defined: &mut HashSet<String>,
) {
    if let VarBase::LoopInput { .. } = var.base {
        return;
    }
    if let Some(name) = names.get(var) {
        defined.insert(name.clone());
    }
}

/// Check that a variable is defined (or is a loop-input reference).
fn check_var_defined(
    var: &Var,
    names: &std::collections::HashMap<Var, String>,
    defined: &HashSet<String>,
    errors: &mut Vec<String>,
) {
    if let VarBase::LoopInput { .. } = var.base {
        return;
    }
    let Some(name) = names.get(var) else {
        errors.push(format!("missing name for var: {var:?}"));
        return;
    };
    if !defined.contains(name) {
        errors.push(format!("use of `{name}` before definition"));
    }
}

/// Record the value identifier for a variable if it is value-based.
fn record_var_id(var: &Var, ids: &mut HashSet<ValueId>) {
    if let Some(id) = var.base.value_id() {
        ids.insert(id);
    }
}

/// Collect used and defined value identifiers from a statement.
fn collect_stmt_ids(stmt: &Stmt, used: &mut HashSet<ValueId>, defined: &mut HashSet<ValueId>) {
    match stmt {
        Stmt::Assign { dest, expr } => {
            record_var_id(dest, defined);
            collect_expr_ids(expr, used);
        }
        Stmt::MemLoad(load) => {
            for v in &load.address {
                record_var_id(v, used);
            }
            for v in &load.outputs {
                record_var_id(v, defined);
            }
        }
        Stmt::MemStore(store) => {
            for v in &store.address {
                record_var_id(v, used);
            }
            for v in &store.values {
                record_var_id(v, used);
            }
        }
        Stmt::AdvLoad(load) => {
            for v in &load.outputs {
                record_var_id(v, defined);
            }
        }
        Stmt::AdvStore(store) => {
            for v in &store.values {
                record_var_id(v, used);
            }
        }
        Stmt::LocalLoad(load) => {
            for v in &load.outputs {
                record_var_id(v, defined);
            }
        }
        Stmt::LocalStore(store) => {
            for v in &store.values {
                record_var_id(v, used);
            }
        }
        Stmt::LocalStoreW(store) => {
            for v in &store.values {
                record_var_id(v, used);
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in &call.args {
                record_var_id(v, used);
            }
            for v in &call.results {
                record_var_id(v, defined);
            }
        }
        Stmt::DynCall { args, results } => {
            for v in args {
                record_var_id(v, used);
            }
            for v in results {
                record_var_id(v, defined);
            }
        }
        Stmt::Intrinsic(intrinsic) => {
            for v in &intrinsic.args {
                record_var_id(v, used);
            }
            for v in &intrinsic.results {
                record_var_id(v, defined);
            }
        }
        Stmt::Repeat { body, phis, .. } => {
            for phi in phis {
                record_var_id(&phi.dest, defined);
                record_var_id(&phi.init, used);
                record_var_id(&phi.step, used);
            }
            for stmt in body {
                collect_stmt_ids(stmt, used, defined);
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            phis,
        } => {
            collect_expr_ids(cond, used);
            for phi in phis {
                record_var_id(&phi.dest, defined);
                record_var_id(&phi.then_var, used);
                record_var_id(&phi.else_var, used);
            }
            for stmt in then_body {
                collect_stmt_ids(stmt, used, defined);
            }
            for stmt in else_body {
                collect_stmt_ids(stmt, used, defined);
            }
        }
        Stmt::While { cond, body, phis } => {
            collect_expr_ids(cond, used);
            for phi in phis {
                record_var_id(&phi.dest, defined);
                record_var_id(&phi.init, used);
                record_var_id(&phi.step, used);
            }
            for stmt in body {
                collect_stmt_ids(stmt, used, defined);
            }
        }
        Stmt::Return(vars) => {
            for v in vars {
                record_var_id(v, used);
            }
        }
    }
}

/// Collect used value identifiers from an expression.
fn collect_expr_ids(expr: &Expr, used: &mut HashSet<ValueId>) {
    match expr {
        Expr::Var(v) => record_var_id(v, used),
        Expr::Binary(_, lhs, rhs) => {
            collect_expr_ids(lhs, used);
            collect_expr_ids(rhs, used);
        }
        Expr::Unary(_, inner) => collect_expr_ids(inner, used),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_ids(cond, used);
            collect_expr_ids(then_expr, used);
            collect_expr_ids(else_expr, used);
        }
        Expr::True | Expr::False | Expr::Constant(_) => {}
    }
}
