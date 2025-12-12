use std::collections::HashSet;

use crate::{
    cfg::{Cfg, InstrPos},
    ssa::{Expr, Stmt, Var},
};

use super::used_vars::{DefUseMap, defined_var, used_in_expr};

#[derive(Debug, Clone, Copy)]
struct ExprProperties {
    contains_unknown: bool,
    complexity: u32,
}

impl ExprProperties {
    fn compute(expr: &Expr) -> Self {
        Self {
            contains_unknown: contains_unknown(expr),
            complexity: expr.complexity(),
        }
    }

    fn can_propagate_over_expr(self, expr: &Expr) -> bool {
        if self.contains_unknown && contains_unknown(expr) {
            return false;
        }
        true
    }

    fn can_propagate_over_stmt(self, stmt: &Stmt) -> bool {
        match stmt {
            Stmt::Assign { expr, .. } | Stmt::Expr(expr) | Stmt::Branch(expr) => {
                self.can_propagate_over_expr(expr)
            }
            Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => false,
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                self.can_propagate_over_expr(cond)
                    && then_body.iter().all(|s| self.can_propagate_over_stmt(s))
                    && else_body.iter().all(|s| self.can_propagate_over_stmt(s))
            }
            Stmt::For {
                init,
                cond,
                step,
                body,
            } => {
                self.can_propagate_over_stmt(init)
                    && self.can_propagate_over_expr(cond)
                    && self.can_propagate_over_stmt(step)
                    && body.iter().all(|s| self.can_propagate_over_stmt(s))
            }
            Stmt::Switch {
                expr,
                cases,
                default,
            } => {
                self.can_propagate_over_expr(expr)
                    && cases
                        .iter()
                        .all(|(_, body)| body.iter().all(|s| self.can_propagate_over_stmt(s)))
                    && default.iter().all(|s| self.can_propagate_over_stmt(s))
            }
            Stmt::While { cond, body } => {
                self.can_propagate_over_expr(cond)
                    && body.iter().all(|s| self.can_propagate_over_stmt(s))
            }
            Stmt::Break | Stmt::Return(_) => true,
            Stmt::Phi { .. } | Stmt::Nop => true,
            Stmt::Instr(_)
            | Stmt::StackOp(_)
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
            | Stmt::Intrinsic(_)
            | Stmt::Unknown => false,
            Stmt::Continue => true,
        }
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
            let mut processed: HashSet<InstrPos> = HashSet::new();

            for &use_pos in uses.iter() {
                if can_propagate(cfg, &def_expr, *def_pos, use_pos, *var, props) {
                    replace_all(cfg.stmt_mut(use_pos), *var, &def_expr);
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

            for v in used_in_expr(&def_expr) {
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
    def_pos: InstrPos,
    use_pos: InstrPos,
    var: Var,
    properties: ExprProperties,
) -> bool {
    let use_stmt = cfg.stmt(use_pos);
    match use_stmt {
        Stmt::Phi { .. } => return false,
        Stmt::StackOp(_)
        | Stmt::MemLoad(_)
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
        | Stmt::Instr(_)
        | Stmt::Unknown => return false,
        Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => {
            return false;
        }
        Stmt::If { .. } | Stmt::While { .. } | Stmt::Switch { .. } => return false,
        Stmt::For { .. } => return false,
        Stmt::Break | Stmt::Continue | Stmt::Return(_) => return false,
        Stmt::Assign { .. } | Stmt::Expr(_) | Stmt::Branch(_) | Stmt::Nop => {}
    }

    // Limit expression blow-up.
    if count_var_occ(use_stmt, var) > 1 {
        return false;
    }
    let use_complexity = stmt_complexity(use_stmt);
    if properties.complexity > 4 || properties.complexity + use_complexity > 7 {
        return false;
    }
    if !properties.can_propagate_over_stmt(use_stmt) {
        return false;
    }

    let used_vars: HashSet<_> = used_in_expr(def_expr)
        .into_iter()
        .map(|v| v.index)
        .collect();

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

fn can_propagate_over(code: &[Stmt], used_vars: &HashSet<u32>, properties: ExprProperties) -> bool {
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

fn replace_all(stmt: &mut Stmt, var: Var, with: &Expr) {
    match stmt {
        Stmt::Assign { expr, .. } | Stmt::Expr(expr) | Stmt::Branch(expr) => {
            replace_in_expr(expr, var, with)
        }
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
        Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => {}
        Stmt::For {
            init,
            cond,
            step,
            body,
        } => {
            replace_all(init, var, with);
            replace_in_expr(cond, var, with);
            replace_all(step, var, with);
            for s in body.iter_mut() {
                replace_all(s, var, with);
            }
        }
        Stmt::Switch {
            expr,
            cases,
            default,
        } => {
            replace_in_expr(expr, var, with);
            for (_, body) in cases.iter_mut() {
                for s in body.iter_mut() {
                    replace_all(s, var, with);
                }
            }
            for s in default.iter_mut() {
                replace_all(s, var, with);
            }
        }
        Stmt::While { cond, body } => {
            replace_in_expr(cond, var, with);
            for s in body.iter_mut() {
                replace_all(s, var, with);
            }
        }
        Stmt::AdvLoad(_) | Stmt::AdvStore(_) | Stmt::LocalLoad(_) | Stmt::LocalStore(_) => {}
        Stmt::Return(vals) => {
            for v in vals.iter_mut() {
                if *v == var {
                    *v = var;
                }
            }
        }
        Stmt::Phi { sources, .. } => {
            for src in sources.iter_mut() {
                if *src == var {
                    // Do not replace inside phi sources; handled by SSA renaming.
                    *src = var;
                }
            }
        }
        Stmt::Break
        | Stmt::Continue
        | Stmt::Instr(_)
        | Stmt::StackOp(_)
        | Stmt::MemLoad(_)
        | Stmt::MemStore(_)
        | Stmt::Call(_)
        | Stmt::Exec(_)
        | Stmt::SysCall(_)
        | Stmt::DynCall { .. }
        | Stmt::Intrinsic(_)
        | Stmt::Unknown
        | Stmt::Nop => {}
    }
}

fn replace_in_expr(expr: &mut Expr, var: Var, with: &Expr) {
    match expr {
        Expr::Var(v) if *v == var => {
            *expr = with.clone();
        }
        Expr::Var(_) => {}
        Expr::BinOp(_, a, b) => {
            replace_in_expr(a, var, with);
            replace_in_expr(b, var, with);
        }
        Expr::Unary(_, a) => replace_in_expr(a, var, with),
        Expr::True | Expr::Constant(_) | Expr::Unknown => {}
    }
}

fn count_var_occ(stmt: &Stmt, var: Var) -> u32 {
    match stmt {
        Stmt::Assign { expr, .. } | Stmt::Expr(expr) | Stmt::Branch(expr) => {
            count_var_occ_expr(expr, var)
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            count_var_occ_expr(cond, var)
                + then_body.iter().map(|s| count_var_occ(s, var)).sum::<u32>()
                + else_body.iter().map(|s| count_var_occ(s, var)).sum::<u32>()
        }
        Stmt::Switch {
            expr,
            cases,
            default,
        } => {
            count_var_occ_expr(expr, var)
                + cases
                    .iter()
                    .map(|(_, body)| body.iter().map(|s| count_var_occ(s, var)).sum::<u32>())
                    .sum::<u32>()
                + default.iter().map(|s| count_var_occ(s, var)).sum::<u32>()
        }
        Stmt::While { cond, body } => {
            count_var_occ_expr(cond, var) + body.iter().map(|s| count_var_occ(s, var)).sum::<u32>()
        }
        Stmt::For {
            init,
            cond,
            step,
            body,
        } => {
            count_var_occ(init, var)
                + count_var_occ_expr(cond, var)
                + count_var_occ(step, var)
                + body.iter().map(|s| count_var_occ(s, var)).sum::<u32>()
        }
        Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => 0,
        Stmt::Phi { sources, .. } => sources.iter().filter(|s| **s == var).count() as u32,
        Stmt::StackOp(op) => op.pops.iter().filter(|v| **v == var).count() as u32,
        Stmt::MemLoad(mem) => mem.address.iter().filter(|v| **v == var).count() as u32,
        Stmt::MemStore(mem) => mem
            .address
            .iter()
            .chain(mem.values.iter())
            .filter(|v| **v == var)
            .count() as u32,
        Stmt::AdvLoad(_) => 0,
        Stmt::AdvStore(store) => store.values.iter().filter(|v| **v == var).count() as u32,
        Stmt::LocalLoad(_) => 0,
        Stmt::LocalStore(store) => store.values.iter().filter(|v| **v == var).count() as u32,
        Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => call
            .args
            .iter()
            .filter(|v| **v == var)
            .count() as u32,
        Stmt::DynCall { args, .. } => args.iter().filter(|v| **v == var).count() as u32,
        Stmt::Intrinsic(intr) => intr.args.iter().filter(|v| **v == var).count() as u32,
        Stmt::Return(vals) => vals.iter().filter(|v| **v == var).count() as u32,
        Stmt::Break | Stmt::Continue => 0,
        Stmt::Instr(_) | Stmt::Unknown | Stmt::Nop => 0,
    }
}

fn count_var_occ_expr(expr: &Expr, var: Var) -> u32 {
    match expr {
        Expr::Var(v) => {
            if *v == var {
                1
            } else {
                0
            }
        }
        Expr::BinOp(_, a, b) => count_var_occ_expr(a, var) + count_var_occ_expr(b, var),
        Expr::Unary(_, a) => count_var_occ_expr(a, var),
        Expr::Constant(_) | Expr::True | Expr::Unknown => 0,
    }
}

fn stmt_complexity(stmt: &Stmt) -> u32 {
    match stmt {
        Stmt::Assign { expr, .. } | Stmt::Expr(expr) | Stmt::Branch(expr) => expr.complexity(),
        Stmt::If {
            cond,
            then_body,
            else_body,
        } => {
            cond.complexity()
                + then_body.iter().map(stmt_complexity).sum::<u32>()
                + else_body.iter().map(stmt_complexity).sum::<u32>()
        }
        Stmt::Switch {
            expr,
            cases,
            default,
        } => {
            expr.complexity()
                + cases
                    .iter()
                    .map(|(_, body)| body.iter().map(stmt_complexity).sum::<u32>())
                    .sum::<u32>()
                + default.iter().map(stmt_complexity).sum::<u32>()
        }
        Stmt::While { cond, body } => {
            cond.complexity() + body.iter().map(stmt_complexity).sum::<u32>()
        }
        Stmt::For {
            init,
            cond,
            step,
            body,
        } => {
            stmt_complexity(init)
                + cond.complexity()
                + stmt_complexity(step)
                + body.iter().map(stmt_complexity).sum::<u32>()
        }
        Stmt::RepeatInit { .. } | Stmt::RepeatCond { .. } | Stmt::RepeatStep { .. } => 0,
        Stmt::Phi { .. } | Stmt::Nop => 0,
        Stmt::Return(_) => 1,
        Stmt::Break | Stmt::Continue => 1,
        Stmt::Instr(_)
        | Stmt::StackOp(_)
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
        | Stmt::Intrinsic(_)
        | Stmt::Unknown => 10,
    }
}

fn contains_unknown(expr: &Expr) -> bool {
    match expr {
        Expr::Unknown => true,
        Expr::BinOp(_, a, b) => contains_unknown(a) || contains_unknown(b),
        Expr::Unary(_, a) => contains_unknown(a),
        Expr::Var(_) | Expr::Constant(_) | Expr::True => false,
    }
}

trait Complexity {
    fn complexity(&self) -> u32;
}

impl Complexity for Expr {
    fn complexity(&self) -> u32 {
        match self {
            Expr::True | Expr::Var(_) | Expr::Constant(_) => 1,
            Expr::Unknown => 5,
            Expr::Unary(_, a) => 1 + a.complexity(),
            Expr::BinOp(_, a, b) => 1 + a.complexity() + b.complexity(),
        }
    }
}
