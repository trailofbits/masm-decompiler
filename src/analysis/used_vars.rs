use std::collections::{HashMap, HashSet};

use crate::{
    cfg::{Cfg, StmtPos},
    ssa::{Condition, Expr, Stmt, Var},
};

/// Mapping from variable definitions to their uses (and vice versa).
pub type DefUseMap = (HashMap<Var, StmtPos>, HashMap<Var, HashSet<StmtPos>>);

/// Build def→use and use→def maps for a CFG.
pub fn build_def_use_map(cfg: &Cfg) -> DefUseMap {
    let mut def_map: HashMap<Var, StmtPos> = HashMap::new();
    let mut use_map: HashMap<Var, HashSet<StmtPos>> = HashMap::new();

    for (node_idx, block) in cfg.nodes.iter().enumerate() {
        for (instr_idx, stmt) in block.code.iter().enumerate() {
            let pos = StmtPos {
                node: node_idx,
                instr: instr_idx,
            };

            for var in stmt.defines_vars() {
                def_map.insert(var.clone(), pos);
                use_map.entry(var).or_default();
            }

            for var in stmt.uses_vars() {
                use_map.entry(var).or_default().insert(pos);
            }
        }
    }

    (def_map, use_map)
}

pub trait UsesVars {
    /// Return the set of variables used by this statement/expression.
    fn uses_vars(&self) -> HashSet<Var>;
}

pub trait DefinesVars {
    /// Return the set of variables defined by this statement.
    fn defines_vars(&self) -> HashSet<Var>;
}

impl UsesVars for Stmt {
    fn uses_vars(&self) -> HashSet<Var> {
        match self {
            Stmt::Assign { expr, .. } => expr.uses_vars(),
            Stmt::MemLoad(load) => {
                let mut vars = HashSet::new();
                for v in load.address.iter().chain(load.outputs.iter()) {
                    vars.insert(v.clone());
                }
                vars
            }
            Stmt::MemStore(store) => {
                let mut vars = HashSet::new();
                for v in store.address.iter().chain(store.values.iter()) {
                    vars.insert(v.clone());
                }
                vars
            }
            Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
                call.args.iter().cloned().collect()
            }
            Stmt::DynCall { args, .. } => args.iter().cloned().collect(),
            Stmt::Intrinsic(intr) => intr.args.iter().cloned().collect(),
            Stmt::AdvLoad(_) => HashSet::new(),
            Stmt::AdvStore(store) => store.values.iter().cloned().collect(),
            Stmt::LocalLoad(_) => HashSet::new(),
            Stmt::LocalStore(store) => store.values.iter().cloned().collect(),
            Stmt::Phi { sources, .. } => sources.iter().cloned().collect(),
            Stmt::Repeat { body, .. } => {
                let mut vars = HashSet::new();
                for s in body {
                    vars.extend(s.uses_vars());
                }
                vars
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                let mut vars = cond.uses_vars();
                for s in then_body {
                    vars.extend(s.uses_vars());
                }
                for s in else_body {
                    vars.extend(s.uses_vars());
                }
                vars
            }
            Stmt::While { cond, body } => {
                let mut vars = cond.uses_vars();
                for s in body {
                    vars.extend(s.uses_vars());
                }
                vars
            }
            Stmt::Return(values) => values.iter().cloned().collect(),
            Stmt::IfBranch(Condition::Stack(expr)) | Stmt::WhileBranch(Condition::Stack(expr)) => {
                expr.uses_vars()
            }
            Stmt::IfBranch(Condition::Count { .. })
            | Stmt::WhileBranch(Condition::Count { .. })
            | Stmt::RepeatBranch(_) => HashSet::new(),
            Stmt::Inst(_) | Stmt::Nop | Stmt::Continue => HashSet::new(),
        }
    }
}

/// Return the variable defined by a statement, if any.
impl DefinesVars for Stmt {
    fn defines_vars(&self) -> HashSet<Var> {
        let mut defs = HashSet::new();
        match self {
            Stmt::Assign { dest: dst, .. } => {
                defs.insert(dst.clone());
            }
            Stmt::Phi { var, .. } => {
                defs.insert(var.clone());
            }
            Stmt::Call(call) | Stmt::Exec(call) | Stmt::SysCall(call) => {
                defs.extend(call.results.iter().cloned());
            }
            Stmt::DynCall { results, .. } => {
                defs.extend(results.iter().cloned());
            }
            Stmt::Intrinsic(intr) => {
                defs.extend(intr.results.iter().cloned());
            }
            Stmt::MemLoad(load) => {
                defs.extend(load.outputs.iter().cloned());
            }
            Stmt::AdvLoad(load) => {
                defs.extend(load.outputs.iter().cloned());
            }
            Stmt::LocalLoad(load) => {
                defs.extend(load.outputs.iter().cloned());
            }
            Stmt::MemStore(_) | Stmt::AdvStore(_) | Stmt::LocalStore(_) => {
                // No definitions.
            }
            Stmt::If {
                then_body,
                else_body,
                ..
            } => {
                defs.extend(then_body.defines_vars());
                defs.extend(else_body.defines_vars());
            }
            Stmt::While { body, .. } | Stmt::Repeat { body, .. } => {
                defs.extend(body.defines_vars());
            }
            Stmt::IfBranch(_) | Stmt::WhileBranch(_) | Stmt::RepeatBranch(_) => {
                // No definitions.
            }
            Stmt::Return(_) | Stmt::Inst(_) | Stmt::Nop | Stmt::Continue => {
                // No definitions.
            }
        }
        defs
    }
}

impl DefinesVars for Vec<Stmt> {
    fn defines_vars(&self) -> HashSet<Var> {
        let mut defs = HashSet::new();
        for stmt in self {
            defs.extend(stmt.defines_vars());
        }
        defs
    }
}

impl UsesVars for Vec<Stmt> {
    fn uses_vars(&self) -> HashSet<Var> {
        let mut uses = HashSet::new();
        for stmt in self {
            uses.extend(stmt.uses_vars());
        }
        uses
    }
}

/// Return the variable used by an expression, if any.
impl UsesVars for Expr {
    fn uses_vars(&self) -> HashSet<Var> {
        let mut result = HashSet::new();
        match self {
            Expr::Var(v) => {
                result.insert(v.clone());
            }
            Expr::Binary(_, a, b) => {
                result.extend(a.uses_vars());
                result.extend(b.uses_vars());
            }
            Expr::Unary(_, a) => {
                result.extend(a.uses_vars());
            }
            Expr::Constant(_) | Expr::True | Expr::False | Expr::Unknown => {}
        }
        result
    }
}
