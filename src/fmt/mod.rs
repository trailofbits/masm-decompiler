//! Pretty-printing helpers that emit a readable structured view of SSA statements and DOT CFGs.

use crate::{
    cfg::{Cfg, Edge},
    ssa::{
        AdvLoad, AdvStore, BinOp, Call, Constant, Expr, IndexExpr, Intrinsic, LocalLoad,
        LocalStore, MemLoad, MemStore, Stmt, Subscript, UnOp, Var,
    },
};

/// Trait for rendering IR nodes with indentation-aware `CodeWriter`.
pub trait CodeDisplay {
    fn fmt_code(&self, f: &mut CodeWriter);
}

#[derive(Default)]
pub struct CodeWriter {
    output: String,
    indent: usize,
    var_names: std::collections::HashMap<Var, String>,
    loop_var_names: std::collections::HashMap<usize, String>,
    loop_depth: usize,
}

impl CodeWriter {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn with_var_names(var_names: std::collections::HashMap<Var, String>) -> Self {
        Self {
            var_names,
            ..Self::default()
        }
    }

    pub fn indent(&mut self) {
        self.indent += 1;
    }

    pub fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    pub fn write(&mut self, item: impl CodeDisplay) {
        item.fmt_code(self);
    }

    pub fn write_block(&mut self, body: &[Stmt]) {
        for stmt in body {
            self.write(stmt.clone());
        }
    }

    pub fn finish(self) -> String {
        self.output
    }

    pub fn clone_var_names(&self) -> std::collections::HashMap<Var, String> {
        self.var_names.clone()
    }

    pub fn write_line(&mut self, line: &str) {
        for _ in 0..self.indent {
            self.output.push_str("  ");
        }
        self.output.push_str(line);
        self.output.push('\n');
    }

    pub fn fmt_var(&self, v: &Var) -> String {
        if let Some(name) = self.loop_var_names.get(&v.index) {
            return name.clone();
        }
        if let Some(name) = self.var_names.get(v) {
            return name.clone();
        }
        let base = format!("v_{}", v.index);
        match &v.subscript {
            Subscript::None => base,
            Subscript::Expr(expr) => format!("{base}_({})", self.fmt_index_expr(expr)),
        }
    }

    fn enter_loop(&mut self, loop_var: &Var) {
        let name = loop_name_for_depth(self.loop_depth);
        self.loop_var_names.insert(loop_var.index, name);
        self.loop_depth += 1;
    }

    fn exit_loop(&mut self, loop_var: &Var) {
        self.loop_depth = self.loop_depth.saturating_sub(1);
        let _ = loop_var;
    }

    fn loop_var_name(&self, idx: usize) -> String {
        if let Some(name) = self.loop_var_names.get(&idx) {
            return name.clone();
        }
        format!("i{idx}")
    }

    fn fmt_index_expr(&self, expr: &IndexExpr) -> String {
        match expr {
            IndexExpr::Const(v) => v.to_string(),
            IndexExpr::LoopVar(idx) => self.loop_var_name(*idx),
            IndexExpr::Add(a, b) => {
                let lhs = self.fmt_index_expr(a);
                match &**b {
                    IndexExpr::Const(c) if *c < 0 => format!("{lhs} - {}", -c),
                    IndexExpr::Mul(x, y) => match (&**x, &**y) {
                        (IndexExpr::Const(c), rhs) if *c < 0 => {
                            format!("{lhs} - {} * {}", -c, self.fmt_index_expr(rhs))
                        }
                        (lhs_term, IndexExpr::Const(c)) if *c < 0 => {
                            format!("{lhs} - {} * {}", -c, self.fmt_index_expr(lhs_term))
                        }
                        _ => format!("{lhs} + {}", self.fmt_index_expr(b)),
                    },
                    _ => format!("{lhs} + {}", self.fmt_index_expr(b)),
                }
            }
            IndexExpr::Mul(a, b) => {
                format!("{} * {}", self.fmt_index_expr(a), self.fmt_index_expr(b))
            }
        }
    }
}

impl CodeDisplay for Stmt {
    fn fmt_code(&self, f: &mut CodeWriter) {
        match self {
            Stmt::Assign { dest: dst, expr } => {
                f.write_line(&format!("{} = {};", f.fmt_var(dst), fmt_expr(f, expr, 0)));
            }
            Stmt::Return(values) => {
                let vals = values
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                if vals.is_empty() {
                    f.write_line("return;");
                } else {
                    f.write_line(&format!("return {vals};"));
                }
            }
            Stmt::MemLoad(MemLoad { address, outputs }) => {
                let args = address
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                let outs = outputs
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                if outs.is_empty() {
                    f.write_line(&format!("mem_load({args});"));
                } else {
                    f.write_line(&format!("{outs} = mem_load({args});"));
                }
            }
            Stmt::MemStore(MemStore { address, values }) => {
                let args = address
                    .iter()
                    .chain(values.iter())
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                f.write_line(&format!("mem_store({args});"));
            }
            Stmt::AdvLoad(AdvLoad { outputs }) => {
                let outs = outputs
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                if outs.is_empty() {
                    f.write_line("adv_load();");
                } else {
                    f.write_line(&format!("{outs} = adv_load();"));
                }
            }
            Stmt::AdvStore(AdvStore { values }) => {
                let args = values
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                f.write_line(&format!("adv_store({args});"));
            }
            Stmt::LocalLoad(LocalLoad { index, outputs }) => {
                let outs = outputs
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                if outs.is_empty() {
                    f.write_line(&format!("loc_load.{index}();"));
                } else {
                    f.write_line(&format!("{outs} = loc_load.{index}();"));
                }
            }
            Stmt::LocalStore(LocalStore { index, values }) => {
                let args = values
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                f.write_line(&format!("loc_store.{index}({args});"));
            }
            Stmt::Call(call) => write_call_like("call", call, f),
            Stmt::Exec(call) => write_call_like("exec", call, f),
            Stmt::SysCall(call) => write_call_like("syscall", call, f),
            Stmt::DynCall { args, results } => {
                let args = args
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                let outs = results
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                if outs.is_empty() {
                    f.write_line(&format!("dyncall({args});"));
                } else {
                    f.write_line(&format!("{outs} = dyncall({args});"));
                }
            }
            Stmt::Intrinsic(Intrinsic {
                name,
                args,
                results,
            }) => {
                let args = args
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                let outs = results
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                if outs.is_empty() {
                    f.write_line(&format!("{name}({args});"));
                } else {
                    f.write_line(&format!("{outs} = {name}({args});"));
                }
            }
            Stmt::Inst(inst) => {
                f.write_line(&format!("{inst:?};"));
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
            } => {
                f.write_line(&format!("if ({}) {{", fmt_expr(f, cond, 0)));
                f.indent();
                f.write_block(then_body);
                f.dedent();
                if !else_body.is_empty() {
                    f.write_line("} else {");
                    f.indent();
                    f.write_block(else_body);
                    f.dedent();
                }
                f.write_line("}");
            }
            Stmt::Repeat {
                loop_var,
                loop_count,
                body,
            } => {
                f.enter_loop(loop_var);
                f.write_line(&format!("repeat.{loop_count} {{"));
                f.indent();
                f.write_block(body);
                f.dedent();
                f.write_line("}");
                f.exit_loop(loop_var);
            }
            Stmt::While { cond, body } => {
                let head = if matches!(cond, Expr::True) {
                    "loop".to_string()
                } else {
                    format!("while ({})", fmt_expr(f, cond, 0))
                };
                f.write_line(&format!("{head} {{"));
                f.indent();
                f.write_block(body);
                f.dedent();
                f.write_line("}");
            }
            Stmt::Phi { var, sources } => {
                let srcs = sources
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                f.write_line(&format!("phi {} = [{srcs}];", f.fmt_var(var)));
            }
            Stmt::Branch(cond) => {
                f.write_line(&format!("branch {};", fmt_expr(f, cond, 0)));
            }
            Stmt::Break => {
                f.write_line("break;");
            }
            Stmt::Continue => {
                f.write_line("continue;");
            }
            Stmt::Nop => {}
        }
    }
}

/// Emit a simple DOT representation of the CFG.
pub fn cfg_to_dot(cfg: &Cfg) -> String {
    let mut out = String::from("digraph cfg {\n");
    for (idx, node) in cfg.nodes.iter().enumerate() {
        out.push_str(&format!("  n{idx} [label=\"{}\"];\n", idx));
        for edge in &node.next {
            let (target, label) = match edge {
                Edge::Unconditional { node, .. } => (*node, "".to_string()),
                Edge::Conditional {
                    node,
                    true_branch: expect_true,
                    ..
                } => (*node, if *expect_true { "T" } else { "F" }.to_string()),
            };
            out.push_str(&format!("  n{idx} -> n{target} [label=\"{}\"];\n", label));
        }
    }
    out.push_str("}\n");
    out
}

fn fmt_constant(c: &Constant) -> String {
    match c {
        Constant::Felt(v) => v.to_string(),
        Constant::Word(w) => format!("[{}, {}, {}, {}]", w[0], w[1], w[2], w[3]),
        Constant::Defined(name) => name.clone(),
    }
}

fn fmt_expr(f: &CodeWriter, expr: &Expr, parent_prec: u8) -> String {
    match expr {
        Expr::True => "true".to_string(),
        Expr::Unknown => "<?>".to_string(),
        Expr::Var(v) => f.fmt_var(v),
        Expr::Constant(c) => fmt_constant(c),
        Expr::Unary(op, inner) => {
            let op_str = match op {
                UnOp::Not => "!",
                UnOp::Neg => "-",
            };
            let inner_str = fmt_expr(f, inner, 5);
            format!("{op_str}{inner_str}")
        }
        Expr::Binary(op, a, b) => {
            let (prec, sym) = match op {
                BinOp::Mul | BinOp::Div => (
                    10,
                    match op {
                        BinOp::Mul => "*",
                        _ => "/",
                    },
                ),
                BinOp::Add | BinOp::Sub => (
                    9,
                    match op {
                        BinOp::Add => "+",
                        _ => "-",
                    },
                ),
                BinOp::And => (7, "&"),
                BinOp::Or => (6, "|"),
                BinOp::Xor => (6, "^"),
                BinOp::Eq => (5, "=="),
                BinOp::Neq => (5, "!="),
                BinOp::Lt => (4, "<"),
                BinOp::Lte => (4, "<="),
                BinOp::Gt => (4, ">"),
                BinOp::Gte => (4, ">="),
            };
            let lhs = fmt_expr(f, a, prec);
            let rhs = fmt_expr(f, b, prec + 1);
            let expr_str = format!("{lhs} {sym} {rhs}");
            if prec < parent_prec {
                format!("({expr_str})")
            } else {
                expr_str
            }
        }
    }
}

fn loop_name_for_depth(depth: usize) -> String {
    const NAMES: [&str; 6] = ["i", "j", "k", "l", "m", "n"];
    if depth < NAMES.len() {
        NAMES[depth].to_string()
    } else {
        format!("i{depth}")
    }
}

fn write_call_like(kind: &str, call: &Call, f: &mut CodeWriter) {
    let args = call
        .args
        .iter()
        .map(|v| f.fmt_var(v))
        .collect::<Vec<_>>()
        .join(", ");
    let outs = call
        .results
        .iter()
        .map(|v| f.fmt_var(v))
        .collect::<Vec<_>>()
        .join(", ");
    let head = format!("{kind} {}", call.target);
    if outs.is_empty() {
        f.write_line(&format!("{head}({args});"));
    } else {
        f.write_line(&format!("{outs} = {head}({args});"));
    }
}
