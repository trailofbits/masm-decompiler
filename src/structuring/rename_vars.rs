use std::collections::{HashMap, HashSet};

use crate::ssa::{Expr, Stmt, Var};

/// Simplistic variable renaming: collapse subscripts (already removed) into a dense numbering
/// and optional alphabetic names for readability.
pub fn apply(code: &mut [Stmt], carriers: &HashSet<(Var, Var)>) {
    let mut map: HashMap<Var, Var> = HashMap::new();
    let mut next = 0usize;
    let classes = build_carrier_classes(code, carriers);
    for class in classes {
        let rep = class
            .iter()
            .min_by_key(|v| v.index)
            .cloned()
            .unwrap_or_else(|| Var::new(next));
        let target_val = map.get(&rep).cloned().unwrap_or_else(|| {
            let v = Var::new(next);
            next += 1;
            map.insert(rep.clone(), v.clone());
            v
        });
        for v in class {
            map.entry(v).or_insert_with(|| target_val.clone());
        }
    }
    rename_block(code, carriers, &mut map, &mut next);
}

fn rename_block(
    code: &mut [Stmt],
    carriers: &HashSet<(Var, Var)>,
    map: &mut HashMap<Var, Var>,
    next: &mut usize,
) {
    // Build equivalence classes from phi connectivity in this block (excluding nested loops).
    let classes = build_carrier_classes(code, carriers);
    for class in classes {
        let rep = class
            .iter()
            .min_by_key(|v| v.index)
            .cloned()
            .unwrap_or_else(|| Var::new(*next));
        let target_val = map.get(&rep).cloned().unwrap_or_else(|| {
            let v = Var::new(*next);
            *next += 1;
            map.insert(rep.clone(), v.clone());
            v
        });
        for v in class {
            map.entry(v).or_insert_with(|| target_val.clone());
        }
    }

    for stmt in code.iter_mut() {
        rename_stmt(stmt, carriers, map, next);
    }
}

fn rename_stmt(
    stmt: &mut Stmt,
    carriers: &HashSet<(Var, Var)>,
    map: &mut HashMap<Var, Var>,
    next: &mut usize,
) {
    match stmt {
        Stmt::Assign { dest: dst, expr } => {
            rename_expr(expr, map, next);
            let new_var = map.entry(dst.clone()).or_insert_with(|| {
                let v = Var::new(*next);
                *next += 1;
                v
            });
            *dst = new_var.clone();
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            rename_expr(cond, map, next);
            for s in then_body.iter_mut().chain(else_body.iter_mut()) {
                rename_stmt(s, carriers, map, next);
            }
        }
        Stmt::Repeat {
            loop_var,
            body,
            ..
        } => {
            let new_var = map.entry(loop_var.clone()).or_insert_with(|| {
                let v = Var::new(*next);
                *next += 1;
                v
            });
            *loop_var = new_var.clone();
            rename_block(body, carriers, map, next);
        }
        Stmt::While { cond, body } => {
            rename_expr(cond, map, next);
            // Share the map so loop-carried vars keep the same names; new loop-local
            // vars will get fresh assignments without cloning outer mappings.
            rename_block(body, carriers, map, next);
        }
        Stmt::Return(vals) => {
            for v in vals.iter_mut() {
                let new = map.entry(v.clone()).or_insert_with(|| {
                    let v_new = Var::new(*next);
                    *next += 1;
                    v_new
                });
                *v = new.clone();
            }
        }
        Stmt::Phi { var, sources } => {
            // Group phi sources into the same logical variable.
            let target = map
                .entry(var.clone())
                .or_insert_with(|| {
                    let v = Var::new(*next);
                    *next += 1;
                    v
                })
                .clone();
            *var = target.clone();
            for src in sources.iter_mut() {
                let v = map.entry(src.clone()).or_insert_with(|| target.clone());
                *src = v.clone();
            }
        }
        Stmt::Break | Stmt::Continue => {}
        Stmt::Branch(expr) => rename_expr(expr, map, next),
        Stmt::MemLoad(mem) => {
            for v in mem.address.iter_mut().chain(mem.outputs.iter_mut()) {
                let new = map.entry(v.clone()).or_insert_with(|| {
                    let v_new = Var::new(*next);
                    *next += 1;
                    v_new
                });
                *v = new.clone();
            }
        }
        Stmt::MemStore(mem) => {
            for v in mem.address.iter_mut().chain(mem.values.iter_mut()) {
                let new = map.entry(v.clone()).or_insert_with(|| {
                    let v_new = Var::new(*next);
                    *next += 1;
                    v_new
                });
                *v = new.clone();
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in call.args.iter_mut().chain(call.results.iter_mut()) {
                let new = map.entry(v.clone()).or_insert_with(|| {
                    let v_new = Var::new(*next);
                    *next += 1;
                    v_new
                });
                *v = new.clone();
            }
        }
        Stmt::DynCall { args, results } => {
            for v in args.iter_mut().chain(results.iter_mut()) {
                let new = map.entry(v.clone()).or_insert_with(|| {
                    let v_new = Var::new(*next);
                    *next += 1;
                    v_new
                });
                *v = new.clone();
            }
        }
        Stmt::Intrinsic(intr) => {
            for v in intr.args.iter_mut().chain(intr.results.iter_mut()) {
                let new = map.entry(v.clone()).or_insert_with(|| {
                    let v_new = Var::new(*next);
                    *next += 1;
                    v_new
                });
                *v = new.clone();
            }
        }
        Stmt::AdvLoad(load) => {
            for v in load.outputs.iter_mut() {
                let new = map.entry(v.clone()).or_insert_with(|| {
                    let v_new = Var::new(*next);
                    *next += 1;
                    v_new
                });
                *v = new.clone();
            }
        }
        Stmt::AdvStore(store) => {
            for v in store.values.iter_mut() {
                let new = map.entry(v.clone()).or_insert_with(|| {
                    let v_new = Var::new(*next);
                    *next += 1;
                    v_new
                });
                *v = new.clone();
            }
        }
        Stmt::LocalLoad(load) => {
            for v in load.outputs.iter_mut() {
                let new = map.entry(v.clone()).or_insert_with(|| {
                    let v_new = Var::new(*next);
                    *next += 1;
                    v_new
                });
                *v = new.clone();
            }
        }
        Stmt::LocalStore(store) => {
            for v in store.values.iter_mut() {
                let new = map.entry(v.clone()).or_insert_with(|| {
                    let v_new = Var::new(*next);
                    *next += 1;
                    v_new
                });
                *v = new.clone();
            }
        }
        Stmt::Inst(_) | Stmt::Nop => {}
    }
}

fn rename_expr(expr: &mut Expr, map: &mut HashMap<Var, Var>, next: &mut usize) {
    match expr {
        Expr::Var(v) => {
            let new = map.entry(v.clone()).or_insert_with(|| {
                let v_new = Var::new(*next);
                *next += 1;
                v_new
            });
            *v = new.clone();
        }
        Expr::Binary(_, a, b) => {
            rename_expr(a, map, next);
            rename_expr(b, map, next);
        }
        Expr::Unary(_, a) => rename_expr(a, map, next),
        Expr::Constant(_) | Expr::True | Expr::Unknown => {}
    }
}

fn build_carrier_classes(code: &[Stmt], carriers: &HashSet<(Var, Var)>) -> Vec<HashSet<Var>> {
    let mut parent: HashMap<Var, Var> = HashMap::new();

    fn find(parent: &mut HashMap<Var, Var>, v: Var) -> Var {
        let p = parent.get(&v).cloned();
        if let Some(pv) = p {
            if pv != v {
                let root = find(parent, pv);
                parent.insert(v.clone(), root.clone());
                root
            } else {
                v
            }
        } else {
            parent.insert(v.clone(), v.clone());
            v
        }
    }

    fn union(parent: &mut HashMap<Var, Var>, a: Var, b: Var) {
        let ra = find(parent, a);
        let rb = find(parent, b);
        if ra != rb {
            parent.insert(ra, rb);
        }
    }

    fn walk(code: &[Stmt], parent: &mut HashMap<Var, Var>) {
        for stmt in code {
            match stmt {
                Stmt::Phi { var, sources } => {
                    for s in sources {
                        union(parent, var.clone(), s.clone());
                    }
                }
                Stmt::Assign {
                    dest: dst,
                    expr: crate::ssa::Expr::Binary(_, a, _),
                } => {
                    if let crate::ssa::Expr::Var(v) = &**a {
                        union(parent, dst.clone(), v.clone());
                    }
                }
                // Loop-carried assignment pattern inserted by CFG pass.
                Stmt::Assign {
                    dest: dst,
                    expr: Expr::Var(v),
                } => {
                    union(parent, dst.clone(), v.clone());
                }
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    walk(then_body, parent);
                    walk(else_body, parent);
                }
                Stmt::While { body, .. } => walk(body, parent),
                _ => {}
            }
        }
    }

    walk(code, &mut parent);
    for (a, b) in carriers {
        union(&mut parent, a.clone(), b.clone());
    }

    let mut classes: HashMap<Var, HashSet<Var>> = HashMap::new();
    let keys: Vec<_> = parent.keys().cloned().collect();
    for v in keys {
        let root = find(&mut parent, v.clone());
        classes.entry(root).or_default().insert(v);
    }
    classes.into_values().collect()
}
