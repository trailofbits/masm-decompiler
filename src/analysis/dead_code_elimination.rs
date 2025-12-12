use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

use crate::{
    cfg::{Cfg, InstrPos},
    ssa::{Expr, Stmt, Var},
};

use super::used_vars::{DefUseMap, used_in_expr};

pub fn eliminate_dead_code(cfg: &mut Cfg, def_use: &mut DefUseMap) {
    let (def_map, use_map) = def_use;
    let mut todo = Vec::from_iter(
        def_map
            .keys()
            .filter(|var| is_dead(**var, use_map))
            .copied(),
    );

    while let Some(var) = todo.pop() {
        let Some(pos) = def_map.get(&var) else {
            continue;
        };
        let stmt = cfg.stmt_mut(*pos);
        match stmt {
            Stmt::Assign { expr, .. } => {
                if can_remove_expr(expr) {
                    for v in used_in_expr(expr) {
                        if let Some(uses) = use_map.get_mut(&v) {
                            uses.remove(pos);
                            if is_dead(v, use_map) {
                                todo.push(v);
                            }
                        }
                    }
                    *stmt = Stmt::Nop;
                } else {
                    let expr = std::mem::replace(expr, Expr::True);
                    *stmt = Stmt::Expr(expr);
                }
            }
            Stmt::Phi { sources, .. } => {
                for src_var in sources {
                    if let Some(uses) = use_map.get_mut(src_var) {
                        uses.remove(pos);
                        if is_dead(*src_var, use_map) {
                            todo.push(*src_var);
                        }
                    }
                }
                *stmt = Stmt::Nop;
            }
            Stmt::For {
                init,
                cond: _,
                step,
                body,
            } => {
                for s in [&mut **init, &mut **step].into_iter() {
                    if let Stmt::Assign { dst, .. } = s {
                        if is_dead(*dst, use_map) {
                            todo.push(*dst);
                        }
                    }
                }
                for s in body.iter_mut() {
                    if let Stmt::Assign { dst, .. } = s {
                        if is_dead(*dst, use_map) {
                            todo.push(*dst);
                        }
                    }
                }
            }
            Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => {}
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                for s in then_body.iter_mut().chain(else_body.iter_mut()) {
                    if let Stmt::Assign { dst, .. } = s {
                        if is_dead(*dst, use_map) {
                            todo.push(*dst);
                        }
                    }
                }
            }
            Stmt::Switch { cases, default, .. } => {
                for s in default.iter_mut() {
                    if let Stmt::Assign { dst, .. } = s {
                        if is_dead(*dst, use_map) {
                            todo.push(*dst);
                        }
                    }
                }
                for (_, body) in cases.iter_mut() {
                    for s in body.iter_mut() {
                        if let Stmt::Assign { dst, .. } = s {
                            if is_dead(*dst, use_map) {
                                todo.push(*dst);
                            }
                        }
                    }
                }
            }
            Stmt::While { body, .. } => {
                for s in body.iter_mut() {
                    if let Stmt::Assign { dst, .. } = s {
                        if is_dead(*dst, use_map) {
                            todo.push(*dst);
                        }
                    }
                }
            }
            Stmt::Break | Stmt::Continue => {}
            _ => {}
        }

        def_map.remove(&var);
    }
}

fn is_dead(var: Var, use_map: &HashMap<Var, HashSet<InstrPos>>) -> bool {
    match use_map.get(&var) {
        Some(uses) => uses.is_empty(),
        None => true,
    }
}

fn can_remove_expr(expr: &Expr) -> bool {
    match expr {
        Expr::True | Expr::Var(_) | Expr::Constant(_) => true,
        Expr::Unary(_, a) => can_remove_expr(a),
        Expr::BinOp(_, a, b) => can_remove_expr(a) && can_remove_expr(b),
        Expr::Unknown => false,
    }
}
