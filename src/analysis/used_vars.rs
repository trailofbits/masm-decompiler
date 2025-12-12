use std::collections::{HashMap, HashSet};

use crate::{
    cfg::{Cfg, InstrPos},
    ssa::{Expr, Stmt, Var},
};

/// Mapping from variable definitions to their uses (and vice versa).
pub type DefUseMap = (HashMap<Var, InstrPos>, HashMap<Var, HashSet<InstrPos>>);

/// Build def→use and use→def maps for a CFG.
pub fn build_def_use_map(cfg: &Cfg) -> DefUseMap {
    let mut def_map: HashMap<Var, InstrPos> = HashMap::new();
    let mut use_map: HashMap<Var, HashSet<InstrPos>> = HashMap::new();

    for (node_idx, block) in cfg.nodes.iter().enumerate() {
        for (instr_idx, stmt) in block.code.iter().enumerate() {
            let pos = InstrPos {
                node: node_idx,
                instr: instr_idx,
            };

            if let Some(def) = defined_var(stmt) {
                def_map.insert(def, pos);
                use_map.entry(def).or_default();
            }

            for var in used_vars(stmt) {
                use_map.entry(var).or_default().insert(pos);
            }
        }
    }

    // Treat values defined in exit blocks (no forward successors) as observable outputs.
    for (node_idx, block) in cfg.nodes.iter().enumerate() {
        let has_forward_succ = block.next.iter().any(|e| !e.back_edge);
        if has_forward_succ {
            continue;
        }
        for (instr_idx, stmt) in block.code.iter().enumerate() {
            if let Some(def) = defined_var(stmt) {
                let pos = InstrPos {
                    node: node_idx,
                    instr: instr_idx,
                };
                use_map.entry(def).or_default().insert(pos);
            }
        }
    }

    (def_map, use_map)
}

/// Return variables used by a statement.
pub fn used_vars(stmt: &Stmt) -> Vec<Var> {
    match stmt {
        Stmt::Assign { expr, .. } => used_in_expr(expr),
        Stmt::Expr(expr) | Stmt::Branch(expr) => used_in_expr(expr),
        Stmt::StackOp(op) => op.pops.clone(),
        Stmt::MemLoad(mem) => mem.address.clone(),
        Stmt::MemStore(mem) => {
            let mut vars = mem.address.clone();
            vars.extend(mem.values.iter().copied());
            vars
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => call.args.clone(),
        Stmt::DynCall { args, .. } => args.clone(),
        Stmt::Intrinsic(intr) => intr.args.clone(),
        Stmt::AdvLoad(_) => Vec::new(),
        Stmt::AdvStore(store) => store.values.clone(),
        Stmt::LocalLoad(_) => Vec::new(),
        Stmt::LocalStore(store) => store.values.clone(),
        Stmt::Phi { sources, .. } => sources.clone(),
        Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => Vec::new(),
        Stmt::For {
            init,
            cond,
            step,
            body,
        } => {
            let mut vars = used_vars(init);
            vars.extend(used_in_expr(cond));
            vars.extend(used_vars(step));
            for s in body {
                vars.extend(used_vars(s));
            }
            vars
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            let mut vars = used_in_expr(cond);
            for s in then_body {
                vars.extend(used_vars(s));
            }
            for s in else_body {
                vars.extend(used_vars(s));
            }
            vars
        }
        Stmt::Switch {
            expr,
            cases,
            default,
        } => {
            let mut vars = used_in_expr(expr);
            for (_, body) in cases {
                for s in body {
                    vars.extend(used_vars(s));
                }
            }
            for s in default {
                vars.extend(used_vars(s));
            }
            vars
        }
        Stmt::While { cond, body } => {
            let mut vars = used_in_expr(cond);
            for s in body {
                vars.extend(used_vars(s));
            }
            vars
        }
        Stmt::Return(vals) => vals.clone(),
        Stmt::Break => Vec::new(),
        Stmt::Continue => Vec::new(),
        Stmt::Instr(_) | Stmt::Unknown | Stmt::Nop => Vec::new(),
    }
}

/// Return the variable defined by a statement, if any.
pub fn defined_var(stmt: &Stmt) -> Option<Var> {
    match stmt {
        Stmt::Assign { dst, .. } => Some(*dst),
        Stmt::Phi { var, .. } => Some(*var),
        Stmt::For { init, step, .. } => defined_var(init).or_else(|| defined_var(step)),
        Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => None,
        _ => None,
    }
}

/// Collect variables used within an expression.
pub fn used_in_expr(expr: &Expr) -> Vec<Var> {
    let mut out = Vec::new();
    collect_expr_vars(expr, &mut out);
    out
}

fn collect_expr_vars(expr: &Expr, out: &mut Vec<Var>) {
    match expr {
        Expr::Var(v) => out.push(*v),
        Expr::BinOp(_, a, b) => {
            collect_expr_vars(a, out);
            collect_expr_vars(b, out);
        }
        Expr::Unary(_, a) => collect_expr_vars(a, out),
        Expr::Constant(_) | Expr::True | Expr::Unknown => {}
    }
}
