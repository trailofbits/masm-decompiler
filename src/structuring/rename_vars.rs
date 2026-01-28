use std::collections::{HashMap, HashSet};

use crate::ssa::{Condition, Expr, IndexExpr, Stmt, Subscript, Var};

/// Variable renaming: assign dense subscripts while avoiding conflicts.
///
/// This pass assigns subscripts to variables for final output. Variables that
/// escaped from loops already have concrete subscripts (e.g., `Const(0)`).
/// Variables inside loops have symbolic subscripts (e.g., `LoopVar(idx)`).
/// Other variables are assigned new concrete subscripts that don't conflict
/// with existing ones.
pub fn apply(code: &mut [Stmt], carriers: &HashSet<(Var, Var)>) {
    // Phase 1: Collect all concrete subscript values that are "claimed".
    let mut claimed = collect_claimed_subscripts(code);

    // Phase 2: Build equivalence classes.
    let classes = build_carrier_classes(code, carriers);

    // Phase 3: Build index-to-index mapping for LoopVar remapping.
    let mut index_map: HashMap<usize, usize> = HashMap::new();
    let mut next_index = 0usize;
    for class in &classes {
        let rep_index = class.iter().map(|v| v.index).min().unwrap_or(next_index);
        let target_index = *index_map.entry(rep_index).or_insert_with(|| {
            let idx = next_index;
            next_index += 1;
            idx
        });
        for v in class {
            index_map.entry(v.index).or_insert(target_index);
        }
    }

    // Phase 4: Build subscript assignments for equivalence classes.
    // If any member has a concrete subscript, use that; otherwise allocate new.
    let mut class_subscripts: HashMap<usize, Subscript> = HashMap::new();
    let mut next_subscript = find_next_free_subscript(&claimed, 0);

    for class in &classes {
        // Find a concrete subscript in this class (if any).
        let class_subscript = find_class_subscript(class, &index_map);

        // Get a representative index for this class.
        let rep_index = class.iter().map(|v| v.index).min().unwrap_or(0);
        let target_index = index_map.get(&rep_index).copied().unwrap_or(rep_index);

        match class_subscript {
            Some(sub) => {
                // Use the existing concrete subscript.
                class_subscripts.insert(target_index, sub);
            }
            None => {
                // Allocate a new subscript that doesn't conflict.
                let new_sub = Subscript::Expr(IndexExpr::Const(next_subscript));
                claimed.insert(next_subscript);
                class_subscripts.insert(target_index, new_sub);
                next_subscript = find_next_free_subscript(&claimed, next_subscript + 1);
            }
        }
    }

    // Phase 5: Rename the code.
    // Track subscript assignments per index to ensure consistency.
    let mut index_subscripts: HashMap<usize, Subscript> = HashMap::new();

    rename_block(
        code,
        carriers,
        &mut index_map,
        &mut next_index,
        &class_subscripts,
        &mut claimed,
        &mut next_subscript,
        &mut index_subscripts,
    );
}

/// Find the next subscript value >= start that isn't in the claimed set.
fn find_next_free_subscript(claimed: &HashSet<i64>, start: i64) -> i64 {
    let mut candidate = start;
    while claimed.contains(&candidate) {
        candidate += 1;
    }
    candidate
}

/// Find a concrete subscript within an equivalence class.
/// Returns `Some(subscript)` if a member has a concrete subscript, `None` otherwise.
fn find_class_subscript(class: &HashSet<Var>, index_map: &HashMap<usize, usize>) -> Option<Subscript> {
    for var in class {
        match &var.subscript {
            Subscript::Expr(IndexExpr::Const(_)) => {
                // Found a concrete subscript, use it.
                return Some(var.subscript.clone());
            }
            Subscript::Expr(expr) => {
                // Symbolic subscript - transform LoopVar indices.
                return Some(Subscript::Expr(rename_index_expr(expr, index_map)));
            }
            Subscript::None => continue,
        }
    }
    None
}

/// Collect all concrete subscript values from variables in the code.
fn collect_claimed_subscripts(code: &[Stmt]) -> HashSet<i64> {
    let mut claimed = HashSet::new();
    collect_subscripts_block(code, &mut claimed);
    claimed
}

fn collect_subscripts_block(code: &[Stmt], claimed: &mut HashSet<i64>) {
    for stmt in code {
        collect_subscripts_stmt(stmt, claimed);
    }
}

fn collect_subscripts_stmt(stmt: &Stmt, claimed: &mut HashSet<i64>) {
    match stmt {
        Stmt::Assign { dest, expr } => {
            collect_subscript_var(dest, claimed);
            collect_subscripts_expr(expr, claimed);
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            collect_subscripts_expr(cond, claimed);
            collect_subscripts_block(then_body, claimed);
            collect_subscripts_block(else_body, claimed);
        }
        Stmt::Repeat { loop_var, body, .. } => {
            collect_subscript_var(loop_var, claimed);
            collect_subscripts_block(body, claimed);
        }
        Stmt::While { cond, body } => {
            collect_subscripts_expr(cond, claimed);
            collect_subscripts_block(body, claimed);
        }
        Stmt::Return(vals) => {
            for v in vals {
                collect_subscript_var(v, claimed);
            }
        }
        Stmt::Phi { var, sources } => {
            collect_subscript_var(var, claimed);
            for src in sources {
                collect_subscript_var(src, claimed);
            }
        }
        Stmt::MemLoad(mem) => {
            for v in mem.address.iter().chain(mem.outputs.iter()) {
                collect_subscript_var(v, claimed);
            }
        }
        Stmt::MemStore(mem) => {
            for v in mem.address.iter().chain(mem.values.iter()) {
                collect_subscript_var(v, claimed);
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in call.args.iter().chain(call.results.iter()) {
                collect_subscript_var(v, claimed);
            }
        }
        Stmt::DynCall { args, results } => {
            for v in args.iter().chain(results.iter()) {
                collect_subscript_var(v, claimed);
            }
        }
        Stmt::Intrinsic(intr) => {
            for v in intr.args.iter().chain(intr.results.iter()) {
                collect_subscript_var(v, claimed);
            }
        }
        Stmt::AdvLoad(load) => {
            for v in load.outputs.iter() {
                collect_subscript_var(v, claimed);
            }
        }
        Stmt::AdvStore(store) => {
            for v in store.values.iter() {
                collect_subscript_var(v, claimed);
            }
        }
        Stmt::LocalLoad(load) => {
            for v in load.outputs.iter() {
                collect_subscript_var(v, claimed);
            }
        }
        Stmt::LocalStore(store) => {
            for v in store.values.iter() {
                collect_subscript_var(v, claimed);
            }
        }
        Stmt::IfBranch(Condition::Stack(expr)) | Stmt::WhileBranch(Condition::Stack(expr)) => {
            collect_subscripts_expr(expr, claimed);
        }
        Stmt::IfBranch(_) | Stmt::WhileBranch(_) | Stmt::RepeatBranch(_) => {}
        Stmt::Inst(_) | Stmt::Nop | Stmt::Break | Stmt::Continue => {}
    }
}

fn collect_subscripts_expr(expr: &Expr, claimed: &mut HashSet<i64>) {
    match expr {
        Expr::Var(v) => collect_subscript_var(v, claimed),
        Expr::Binary(_, a, b) => {
            collect_subscripts_expr(a, claimed);
            collect_subscripts_expr(b, claimed);
        }
        Expr::Unary(_, a) => collect_subscripts_expr(a, claimed),
        Expr::Constant(_) | Expr::True | Expr::Unknown => {}
    }
}

fn collect_subscript_var(var: &Var, claimed: &mut HashSet<i64>) {
    if let Subscript::Expr(IndexExpr::Const(n)) = &var.subscript {
        claimed.insert(*n);
    }
}

fn rename_block(
    code: &mut [Stmt],
    carriers: &HashSet<(Var, Var)>,
    index_map: &mut HashMap<usize, usize>,
    next_index: &mut usize,
    class_subscripts: &HashMap<usize, Subscript>,
    claimed: &mut HashSet<i64>,
    next_subscript: &mut i64,
    index_subscripts: &mut HashMap<usize, Subscript>,
) {
    // Note: Equivalence classes are built once at the top level in `apply()`.
    // The top-level `build_carrier_classes` recursively walks all nested blocks,
    // so we don't need to rebuild classes here.

    for stmt in code.iter_mut() {
        rename_stmt(
            stmt,
            carriers,
            index_map,
            next_index,
            class_subscripts,
            claimed,
            next_subscript,
            index_subscripts,
        );
    }
}

/// Rename a single variable, assigning a subscript if needed.
fn rename_var(
    v: &mut Var,
    index_map: &mut HashMap<usize, usize>,
    next_index: &mut usize,
    class_subscripts: &HashMap<usize, Subscript>,
    claimed: &mut HashSet<i64>,
    next_subscript: &mut i64,
    index_subscripts: &mut HashMap<usize, Subscript>,
) {
    let new_index = *index_map.entry(v.index).or_insert_with(|| {
        let idx = *next_index;
        *next_index += 1;
        idx
    });

    // Determine the new subscript.
    let new_subscript = match &v.subscript {
        // Already has a concrete subscript - keep it.
        Subscript::Expr(IndexExpr::Const(_)) => v.subscript.clone(),
        // Symbolic subscript - transform LoopVar indices.
        Subscript::Expr(expr) => Subscript::Expr(rename_index_expr(expr, index_map)),
        // No subscript - check if we already assigned one for this index, or allocate new.
        Subscript::None => {
            // First check if this renamed index already has a subscript assigned.
            if let Some(sub) = index_subscripts.get(&new_index) {
                sub.clone()
            } else if let Some(sub) = class_subscripts.get(&new_index) {
                // Use the class subscript and cache it.
                index_subscripts.insert(new_index, sub.clone());
                sub.clone()
            } else {
                // Allocate a new subscript and cache it for this index.
                let sub = Subscript::Expr(IndexExpr::Const(*next_subscript));
                claimed.insert(*next_subscript);
                index_subscripts.insert(new_index, sub.clone());
                *next_subscript = find_next_free_subscript(claimed, *next_subscript + 1);
                sub
            }
        }
    };

    v.index = new_index;
    v.subscript = new_subscript;
}

/// Transform an IndexExpr, renaming LoopVar indices.
fn rename_index_expr(expr: &IndexExpr, index_map: &HashMap<usize, usize>) -> IndexExpr {
    match expr {
        IndexExpr::Const(c) => IndexExpr::Const(*c),
        IndexExpr::LoopVar(idx) => {
            // Look up the new index for this loop variable.
            let new_idx = index_map.get(idx).copied().unwrap_or(*idx);
            IndexExpr::LoopVar(new_idx)
        }
        IndexExpr::Add(a, b) => IndexExpr::Add(
            Box::new(rename_index_expr(a, index_map)),
            Box::new(rename_index_expr(b, index_map)),
        ),
        IndexExpr::Mul(a, b) => IndexExpr::Mul(
            Box::new(rename_index_expr(a, index_map)),
            Box::new(rename_index_expr(b, index_map)),
        ),
    }
}

fn rename_stmt(
    stmt: &mut Stmt,
    carriers: &HashSet<(Var, Var)>,
    index_map: &mut HashMap<usize, usize>,
    next_index: &mut usize,
    class_subscripts: &HashMap<usize, Subscript>,
    claimed: &mut HashSet<i64>,
    next_subscript: &mut i64,
    index_subscripts: &mut HashMap<usize, Subscript>,
) {
    match stmt {
        Stmt::Assign { dest: dst, expr } => {
            rename_expr(expr, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            rename_var(dst, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            rename_expr(cond, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            for s in then_body.iter_mut().chain(else_body.iter_mut()) {
                rename_stmt(s, carriers, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::Repeat {
            loop_var,
            body,
            ..
        } => {
            // Loop variables don't get numeric subscripts - they're loop counters.
            // Just rename the index and keep the subscript as None.
            let new_index = *index_map.entry(loop_var.index).or_insert_with(|| {
                let idx = *next_index;
                *next_index += 1;
                idx
            });
            loop_var.index = new_index;
            // Don't assign a subscript - the formatter will handle loop vars specially.

            rename_block(body, carriers, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
        }
        Stmt::While { cond, body } => {
            rename_expr(cond, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            rename_block(body, carriers, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
        }
        Stmt::Return(vals) => {
            for v in vals.iter_mut() {
                rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::Phi { var, sources } => {
            // Group phi sources into the same logical variable.
            let target_index = *index_map.entry(var.index).or_insert_with(|| {
                let idx = *next_index;
                *next_index += 1;
                idx
            });
            rename_var(var, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            for src in sources.iter_mut() {
                index_map.entry(src.index).or_insert(target_index);
                rename_var(src, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::Break | Stmt::Continue => {}
        Stmt::IfBranch(Condition::Stack(expr))
        | Stmt::WhileBranch(Condition::Stack(expr)) => {
            rename_expr(expr, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
        }
        Stmt::IfBranch(Condition::Count { .. })
        | Stmt::WhileBranch(Condition::Count { .. })
        | Stmt::RepeatBranch(_) => {}
        Stmt::MemLoad(mem) => {
            for v in mem.address.iter_mut().chain(mem.outputs.iter_mut()) {
                rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::MemStore(mem) => {
            for v in mem.address.iter_mut().chain(mem.values.iter_mut()) {
                rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            for v in call.args.iter_mut().chain(call.results.iter_mut()) {
                rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::DynCall { args, results } => {
            for v in args.iter_mut().chain(results.iter_mut()) {
                rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::Intrinsic(intr) => {
            for v in intr.args.iter_mut().chain(intr.results.iter_mut()) {
                rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::AdvLoad(load) => {
            for v in load.outputs.iter_mut() {
                rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::AdvStore(store) => {
            for v in store.values.iter_mut() {
                rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::LocalLoad(load) => {
            for v in load.outputs.iter_mut() {
                rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::LocalStore(store) => {
            for v in store.values.iter_mut() {
                rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            }
        }
        Stmt::Inst(_) | Stmt::Nop => {}
    }
}

fn rename_expr(
    expr: &mut Expr,
    index_map: &mut HashMap<usize, usize>,
    next_index: &mut usize,
    class_subscripts: &HashMap<usize, Subscript>,
    claimed: &mut HashSet<i64>,
    next_subscript: &mut i64,
    index_subscripts: &mut HashMap<usize, Subscript>,
) {
    match expr {
        Expr::Var(v) => {
            rename_var(v, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
        }
        Expr::Binary(_, a, b) => {
            rename_expr(a, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
            rename_expr(b, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
        }
        Expr::Unary(_, a) => {
            rename_expr(a, index_map, next_index, class_subscripts, claimed, next_subscript, index_subscripts);
        }
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
                Stmt::While { body, .. } | Stmt::Repeat { body, .. } => walk(body, parent),
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
