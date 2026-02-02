use std::collections::HashSet;

use crate::{
    cfg::{Cfg, StmtPos},
    ssa::{Condition, Expr, Stmt, Var},
};

use super::used_vars::{DefUseMap, UsesVars};

#[derive(Debug, Clone, Copy)]
struct ExprProperties {
    complexity: usize,
    contains_unknown: bool,
}

impl ExprProperties {
    fn compute(expr: &Expr) -> Self {
        Self {
            complexity: expr_complexity(expr),
            contains_unknown: expr_contains_unknown(expr),
        }
    }

    fn can_propagate_over_expr(self, _: &Expr) -> bool {
        true
    }

    fn can_propagate_over_stmt(self, stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Assign { expr, .. } => self.can_propagate_over_expr(expr),
            Stmt::IfBranch(Condition::Stack(expr)) | Stmt::WhileBranch(Condition::Stack(expr)) => {
                self.can_propagate_over_expr(expr)
            }
            Stmt::IfBranch(Condition::Count { .. })
            | Stmt::WhileBranch(Condition::Count { .. })
            | Stmt::RepeatBranch(_) => true,
            Stmt::Repeat { .. } => false,
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                self.can_propagate_over_expr(cond)
                    && then_body.iter().all(|s| self.can_propagate_over_stmt(s))
                    && else_body.iter().all(|s| self.can_propagate_over_stmt(s))
            }
            Stmt::While { cond, body } => {
                self.can_propagate_over_expr(cond)
                    && body.iter().all(|s| self.can_propagate_over_stmt(s))
            }
            Stmt::Return(_) => true,
            Stmt::Phi { .. } | Stmt::Nop => true,
            Stmt::Inst(_)
            | Stmt::AdvLoad(_)
            | Stmt::AdvStore(_)
            | Stmt::LocalLoad(_)
            | Stmt::LocalStore(_)
            | Stmt::MemLoad(_)
            | Stmt::MemStore(_)
            | Stmt::Call(_)
            | Stmt::Exec(_)
            | Stmt::SysCall(_)
            | Stmt::DynCall { .. }
            | Stmt::Intrinsic(_) => false,
        }
    }
}

fn expr_contains_unknown(expr: &Expr) -> bool {
    match expr {
        Expr::Unknown => true,
        Expr::Binary(_, a, b) => expr_contains_unknown(a) || expr_contains_unknown(b),
        Expr::Unary(_, a) => expr_contains_unknown(a),
        Expr::Var(_) | Expr::Constant(_) | Expr::True | Expr::False => false,
    }
}

fn expr_complexity(expr: &Expr) -> usize {
    match expr {
        Expr::True | Expr::False | Expr::Var(_) | Expr::Constant(_) => 1,
        Expr::Unary(_, a) => 1 + expr_complexity(a),
        Expr::Binary(_, a, b) => 1 + expr_complexity(a) + expr_complexity(b),
        Expr::Unknown => 100,
    }
}

pub fn propagate_expressions(cfg: &mut Cfg, def_use: &mut DefUseMap) {
    let (def_map, use_map) = def_use;
    let mut defs: Vec<_> = def_map.iter().collect();
    defs.sort_unstable_by_key(|(_, pos)| *pos);

    let mut changed = true;
    while changed {
        changed = false;
        for (var, def_pos) in defs.iter().copied() {
            let Some(uses) = use_map.get(var) else {
                continue;
            };
            if uses.is_empty() {
                continue;
            }
            let def_stmt = cfg.stmt(*def_pos);
            let Stmt::Assign { expr: def_expr, .. } = def_stmt else {
                continue;
            };
            let props = ExprProperties::compute(def_expr);
            if props.contains_unknown {
                continue;
            }

            let def_expr = def_expr.clone();
            let mut processed: HashSet<StmtPos> = HashSet::new();

            for &use_pos in uses.iter() {
                if can_propagate(cfg, &def_expr, *def_pos, use_pos, var, props) {
                    replace_all(cfg.stmt_mut(use_pos), var, &def_expr);
                    processed.insert(use_pos);
                    changed = true;
                }
            }

            if processed.is_empty() {
                continue;
            }

            if let Some(entries) = use_map.get_mut(var) {
                entries.retain(|pos| !processed.contains(pos));
            }

            for v in def_expr.uses_vars() {
                use_map
                    .entry(v)
                    .or_default()
                    .extend(processed.iter().copied());
            }
        }
    }
}

fn can_propagate(
    cfg: &Cfg,
    def_expr: &Expr,
    def_pos: StmtPos,
    use_pos: StmtPos,
    var: &Var,
    properties: ExprProperties,
) -> bool {
    let use_stmt = cfg.stmt(use_pos);
    match use_stmt {
        Stmt::Phi { .. } => return false,
        Stmt::MemLoad(_)
        | Stmt::MemStore(_)
        | Stmt::AdvLoad(_)
        | Stmt::AdvStore(_)
        | Stmt::LocalLoad(_)
        | Stmt::LocalStore(_)
        | Stmt::Call(_)
        | Stmt::Exec(_)
        | Stmt::SysCall(_)
        | Stmt::DynCall { .. }
        | Stmt::Intrinsic(_)
        | Stmt::Inst(_) => return false,
        Stmt::Repeat { .. } => return false,
        Stmt::If { .. } | Stmt::While { .. } => return false,
        Stmt::Return(_) => return false,
        Stmt::IfBranch(_) | Stmt::WhileBranch(_) | Stmt::RepeatBranch(_) => return false,
        Stmt::Assign { .. } | Stmt::Nop => {}
    }

    // Limit expression blow-up.
    if count_var_occ(use_stmt, var) > 1 {
        return false;
    }
    let use_complexity = use_stmt.complexity();
    if properties.complexity > 4 || properties.complexity + use_complexity > 7 {
        return false;
    }
    if !properties.can_propagate_over_stmt(use_stmt) {
        return false;
    }

    let used_vars: HashSet<_> = def_expr.uses_vars().into_iter().map(|v| v.index).collect();

    if def_pos.node == use_pos.node {
        let code = &cfg.nodes[def_pos.node].code[def_pos.instr..use_pos.instr];
        return can_propagate_over(code, &used_vars, properties);
    }

    // Different blocks: tail of def block
    let code = &cfg.nodes[def_pos.node].code[def_pos.instr..];
    if !can_propagate_over(code, &used_vars, properties) {
        return false;
    }

    // Head of use block
    let code = &cfg.nodes[use_pos.node].code[..use_pos.instr];
    if !can_propagate_over(code, &used_vars, properties) {
        return false;
    }

    // Intermediate blocks: conservative scan of all nodes between def and use (excluding them).
    // Without a full graph slice helper, scan every node except def/use as a barrier if needed.
    for (idx, block) in cfg.nodes.iter().enumerate() {
        if idx == def_pos.node || idx == use_pos.node {
            continue;
        }
        if !can_propagate_over(&block.code, &used_vars, properties) {
            return false;
        }
    }

    true
}

fn can_propagate_over(
    code: &[Stmt],
    used_vars: &HashSet<usize>,
    properties: ExprProperties,
) -> bool {
    for stmt in code {
        if let Some(def) = defined_var(stmt) {
            if used_vars.contains(&def.index) {
                return false;
            }
        }

        if !properties.can_propagate_over_stmt(stmt) {
            return false;
        }
    }
    true
}

fn defined_var(stmt: &Stmt) -> Option<Var> {
    match stmt {
        Stmt::Assign { dest, .. } => Some(dest.clone()),
        Stmt::Phi { var, .. } => Some(var.clone()),
        _ => None,
    }
}

fn replace_all(stmt: &mut Stmt, var: &Var, with: &Expr) {
    match stmt {
        Stmt::Assign { expr, .. } => replace_in_expr(expr, var, with),
        Stmt::IfBranch(Condition::Stack(expr)) | Stmt::WhileBranch(Condition::Stack(expr)) => {
            replace_in_expr(expr, var, with)
        }
        Stmt::IfBranch(Condition::Count { .. })
        | Stmt::WhileBranch(Condition::Count { .. })
        | Stmt::RepeatBranch(_) => {}
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            replace_in_expr(cond, var, with);
            for s in then_body.iter_mut().chain(else_body.iter_mut()) {
                replace_all(s, var, with);
            }
        }
        Stmt::Repeat { body, .. } => {
            for stmt in body {
                replace_all(stmt, var, with);
            }
        }
        Stmt::While { cond, body } => {
            replace_in_expr(cond, var, with);
            for s in body.iter_mut() {
                replace_all(s, var, with);
            }
        }
        Stmt::AdvLoad(_) | Stmt::AdvStore(_) | Stmt::LocalLoad(_) | Stmt::LocalStore(_) => {}
        Stmt::Return(_) | Stmt::Phi { .. } => {}
        Stmt::Inst(_)
        | Stmt::MemLoad(_)
        | Stmt::MemStore(_)
        | Stmt::Call(_)
        | Stmt::Exec(_)
        | Stmt::SysCall(_)
        | Stmt::DynCall { .. }
        | Stmt::Intrinsic(_)
        | Stmt::Nop => {}
    }
}

fn replace_in_expr(expr: &mut Expr, var: &Var, with: &Expr) {
    match expr {
        Expr::Var(v) if v == var => {
            *expr = with.clone();
        }
        Expr::Var(_) => {}
        Expr::Binary(_, a, b) => {
            replace_in_expr(a, var, with);
            replace_in_expr(b, var, with);
        }
        Expr::Unary(_, a) => replace_in_expr(a, var, with),
        Expr::True | Expr::False | Expr::Constant(_) | Expr::Unknown => {}
    }
}

fn count_var_occ(stmt: &Stmt, var: &Var) -> usize {
    match stmt {
        Stmt::Assign { expr, .. } => count_var_occ_expr(expr, var),
        Stmt::IfBranch(Condition::Stack(expr)) | Stmt::WhileBranch(Condition::Stack(expr)) => {
            count_var_occ_expr(expr, var)
        }
        Stmt::IfBranch(Condition::Count { .. })
        | Stmt::WhileBranch(Condition::Count { .. })
        | Stmt::RepeatBranch(_) => 0,
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            count_var_occ_expr(cond, var)
                + then_body
                    .iter()
                    .map(|s| count_var_occ(s, var))
                    .sum::<usize>()
                + else_body
                    .iter()
                    .map(|s| count_var_occ(s, var))
                    .sum::<usize>()
        }
        Stmt::While { cond, body } => {
            count_var_occ_expr(cond, var)
                + body.iter().map(|s| count_var_occ(s, var)).sum::<usize>()
        }
        Stmt::Repeat { body, .. } => body.iter().map(|s| count_var_occ(s, var)).sum(),
        Stmt::Phi { sources, .. } => sources.iter().filter(|s| *s == var).count(),
        Stmt::MemLoad(mem) => mem.address.iter().filter(|v| *v == var).count(),
        Stmt::MemStore(mem) => mem
            .address
            .iter()
            .chain(mem.values.iter())
            .filter(|v| *v == var)
            .count(),
        Stmt::AdvLoad(_) => 0,
        Stmt::AdvStore(store) => store.values.iter().filter(|v| *v == var).count(),
        Stmt::LocalLoad(_) => 0,
        Stmt::LocalStore(store) => store.values.iter().filter(|v| *v == var).count(),
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
            call.args.iter().filter(|v| *v == var).count()
        }
        Stmt::DynCall { args, .. } => args.iter().filter(|v| *v == var).count(),
        Stmt::Intrinsic(intr) => intr.args.iter().filter(|v| *v == var).count(),
        Stmt::Return(vals) => vals.iter().filter(|v| *v == var).count(),
        Stmt::Inst(_) | Stmt::Nop => 0,
    }
}

fn count_var_occ_expr(expr: &Expr, var: &Var) -> usize {
    match expr {
        Expr::Var(v) => {
            if v == var {
                1
            } else {
                0
            }
        }
        Expr::Binary(_, a, b) => count_var_occ_expr(a, var) + count_var_occ_expr(b, var),
        Expr::Unary(_, a) => count_var_occ_expr(a, var),
        Expr::Constant(_) | Expr::True | Expr::False | Expr::Unknown => 0,
    }
}

trait Complexity {
    fn complexity(&self) -> usize;
}

impl Complexity for Stmt {
    fn complexity(&self) -> usize {
        match self {
            Stmt::Assign { expr, .. } => expr.complexity(),
            Stmt::IfBranch(Condition::Stack(expr)) | Stmt::WhileBranch(Condition::Stack(expr)) => {
                expr.complexity()
            }
            Stmt::IfBranch(Condition::Count { .. })
            | Stmt::WhileBranch(Condition::Count { .. })
            | Stmt::RepeatBranch(_) => 1,
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => cond.complexity() + then_body.complexity() + else_body.complexity(),
            Stmt::While { cond, body } => cond.complexity() + body.complexity(),
            Stmt::Repeat { body, .. } => 1 + body.complexity(),
            Stmt::Phi { .. } | Stmt::Nop => 0,
            Stmt::Return(_) => 1,
            Stmt::Inst(_)
            | Stmt::AdvLoad(_)
            | Stmt::AdvStore(_)
            | Stmt::LocalLoad(_)
            | Stmt::LocalStore(_)
            | Stmt::MemLoad(_)
            | Stmt::MemStore(_)
            | Stmt::Call(_)
            | Stmt::Exec(_)
            | Stmt::SysCall(_)
            | Stmt::DynCall { .. }
            | Stmt::Intrinsic(_) => 10,
        }
    }
}

impl Complexity for Vec<Stmt> {
    fn complexity(&self) -> usize {
        self.iter().map(|s| s.complexity()).sum()
    }
}

impl Complexity for Expr {
    fn complexity(&self) -> usize {
        match self {
            Expr::True | Expr::False | Expr::Var(_) | Expr::Constant(_) => 1,
            Expr::Unary(_, a) => 1 + a.complexity(),
            Expr::Binary(_, a, b) => 1 + a.complexity() + b.complexity(),
            Expr::Unknown => 100,
        }
    }
}
