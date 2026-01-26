use std::collections::{HashMap, HashSet};
use crate::{
    cfg::{Cfg, StmtPos},
    ssa::{Expr, Stmt, Var},
};

use super::used_vars::{DefUseMap, UsesVars};

pub fn eliminate_dead_code(cfg: &mut Cfg, def_use: &mut DefUseMap) {
    let (def_map, use_map) = def_use;
    let mut todo: Vec<Var> = def_map
        .keys()
        .filter(|var| is_dead(var, use_map))
        .cloned()
        .collect();

    while let Some(var) = todo.pop() {
        let Some(pos) = def_map.get(&var) else {
            continue;
        };
        let stmt = cfg.stmt_mut(*pos);
        let mut removed = false;
        match stmt {
            Stmt::Assign { expr, .. } => {
                if can_remove_expr(expr) {
                    for v in expr.uses_vars() {
                        if let Some(uses) = use_map.get_mut(&v) {
                            uses.remove(pos);
                            if is_dead(&v, use_map) {
                                todo.push(v);
                            }
                        }
                    }
                    *stmt = Stmt::Nop;
                    removed = true;
                }
            }
            Stmt::Phi { sources, .. } => {
                for src_var in sources {
                    if let Some(uses) = use_map.get_mut(src_var) {
                        uses.remove(pos);
                        if is_dead(src_var, use_map) {
                            todo.push(src_var.clone());
                        }
                    }
                }
                *stmt = Stmt::Nop;
                removed = true;
            }
            _ => {}
        }

        if removed {
            def_map.remove(&var);
        }
    }
}

fn is_dead(var: &Var, use_map: &HashMap<Var, HashSet<StmtPos>>) -> bool {
    match use_map.get(var) {
        Some(uses) => uses.is_empty(),
        None => true,
    }
}

fn can_remove_expr(expr: &Expr) -> bool {
    match expr {
        Expr::True | Expr::Var(_) | Expr::Constant(_) => true,
        Expr::Unary(_, a) => can_remove_expr(a),
        Expr::Binary(_, a, b) => can_remove_expr(a) && can_remove_expr(b),
        Expr::Unknown => false,
    }
}
