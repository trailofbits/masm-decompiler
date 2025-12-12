use std::collections::{HashMap, HashSet};

use crate::ssa::{Expr, Stmt, Var};

/// Simplistic variable renaming: collapse subscripts (already removed) into a dense numbering
/// and optional alphabetic names for readability.
pub fn apply(code: &mut [Stmt], carriers: &HashSet<(Var, Var)>) {
    let mut map: HashMap<Var, Var> = HashMap::new();
    let mut next = 0u32;
    let classes = build_carrier_classes(code, carriers);
    for class in classes {
        let rep = *class
            .iter()
            .min_by_key(|v| v.index)
            .unwrap_or(&Var::no_sub(next));
        let target_val = map.get(&rep).copied().unwrap_or_else(|| {
            let v = Var::no_sub(next);
            next += 1;
            map.insert(rep, v);
            v
        });
        for v in class {
            map.entry(v).or_insert(target_val);
        }
    }
    rename_block(code, carriers, &mut map, &mut next);
}

fn rename_block(
    code: &mut [Stmt],
    carriers: &HashSet<(Var, Var)>,
    map: &mut HashMap<Var, Var>,
    next: &mut u32,
) {
    // Build equivalence classes from phi connectivity in this block (excluding nested loops).
    let classes = build_carrier_classes(code, carriers);
    for class in classes {
        let rep = *class
            .iter()
            .min_by_key(|v| v.index)
            .unwrap_or(&Var::no_sub(*next));
        let target_val = map.get(&rep).copied().unwrap_or_else(|| {
            let v = Var::no_sub(*next);
            *next += 1;
            map.insert(rep, v);
            v
        });
        for v in class {
            map.entry(v).or_insert(target_val);
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
    next: &mut u32,
) {
    match stmt {
        Stmt::Assign { dst, expr } => {
            rename_expr(expr, map, next);
            let new_var = map.entry(*dst).or_insert_with(|| {
                let v = Var::no_sub(*next);
                *next += 1;
                v
            });
            *dst = *new_var;
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
        Stmt::Switch {
            expr,
            cases,
            default,
        } => {
            rename_expr(expr, map, next);
            for (_, body) in cases {
                rename_block(body, carriers, map, next);
            }
            rename_block(default, carriers, map, next);
        }
        Stmt::For {
            init,
            cond,
            step,
            body,
        } => {
            rename_stmt(init, carriers, map, next);
            rename_expr(cond, map, next);
            rename_stmt(step, carriers, map, next);
            rename_block(body, carriers, map, next);
        }
        Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => {}
        Stmt::While { cond, body } => {
            rename_expr(cond, map, next);
            // Share the map so loop-carried vars keep the same names; new loop-local
            // vars will get fresh assignments without cloning outer mappings.
            rename_block(body, carriers, map, next);
        }
        Stmt::Return(vals) => {
            for v in vals.iter_mut() {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::Phi { var, sources } => {
            // Group phi sources into the same logical variable.
            let target = *map.entry(*var).or_insert_with(|| {
                let v = Var::no_sub(*next);
                *next += 1;
                v
            });
            *var = target;
            for src in sources.iter_mut() {
                let v = map.entry(*src).or_insert(target);
                *src = *v;
            }
        }
        Stmt::Break | Stmt::Continue => {}
        Stmt::Expr(expr) | Stmt::Branch(expr) => rename_expr(expr, map, next),
        Stmt::StackOp(op) => {
            for v in op.pops.iter_mut().chain(op.pushes.iter_mut()) {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::MemLoad(mem) => {
            for v in mem.address.iter_mut().chain(mem.outputs.iter_mut()) {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::MemStore(mem) => {
            for v in mem.address.iter_mut().chain(mem.values.iter_mut()) {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in call.args.iter_mut().chain(call.results.iter_mut()) {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::DynCall { args, results } => {
            for v in args.iter_mut().chain(results.iter_mut()) {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::Intrinsic(intr) => {
            for v in intr.args.iter_mut().chain(intr.results.iter_mut()) {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::AdvLoad(load) => {
            for v in load.outputs.iter_mut() {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::AdvStore(store) => {
            for v in store.values.iter_mut() {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::LocalLoad(load) => {
            for v in load.outputs.iter_mut() {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::LocalStore(store) => {
            for v in store.values.iter_mut() {
                let new = map.entry(*v).or_insert_with(|| {
                    let v_new = Var::no_sub(*next);
                    *next += 1;
                    v_new
                });
                *v = *new;
            }
        }
        Stmt::Instr(_) | Stmt::Unknown | Stmt::Nop => {}
    }
}

fn rename_expr(expr: &mut Expr, map: &mut HashMap<Var, Var>, next: &mut u32) {
    match expr {
        Expr::Var(v) => {
            let new = map.entry(*v).or_insert_with(|| {
                let v_new = Var::no_sub(*next);
                *next += 1;
                v_new
            });
            *v = *new;
        }
        Expr::BinOp(_, a, b) => {
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
        let p = parent.get(&v).copied();
        if let Some(pv) = p {
            if pv != v {
                let root = find(parent, pv);
                parent.insert(v, root);
                root
            } else {
                v
            }
        } else {
            parent.insert(v, v);
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
                        union(parent, *var, *s);
                    }
                }
                Stmt::Assign {
                    dst,
                    expr: crate::ssa::Expr::BinOp(_, a, _),
                } => {
                    if let crate::ssa::Expr::Var(v) = &**a {
                        union(parent, *dst, *v);
                    }
                }
                // Loop-carried assignment pattern inserted by CFG pass.
                Stmt::Assign {
                    dst,
                    expr: Expr::Var(v),
                } => {
                    union(parent, *dst, *v);
                }
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    walk(then_body, parent);
                    walk(else_body, parent);
                }
                Stmt::Switch { cases, default, .. } => {
                    for (_, body) in cases {
                        walk(body, parent);
                    }
                    walk(default, parent);
                }
                Stmt::For {
                    body, init, step, ..
                } => {
                    walk(&[*init.clone(), *step.clone()], parent);
                    walk(body, parent);
                }
                Stmt::While { body, .. } => walk(body, parent),
                _ => {}
            }
        }
    }

    walk(code, &mut parent);
    for (a, b) in carriers {
        union(&mut parent, *a, *b);
    }

    let mut classes: HashMap<Var, HashSet<Var>> = HashMap::new();
    let keys: Vec<_> = parent.keys().copied().collect();
    for v in keys {
        let root = find(&mut parent, v);
        classes.entry(root).or_default().insert(v);
    }
    classes.into_values().collect()
}
