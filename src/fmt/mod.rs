//! Pretty-printing helpers.
//!
//! Emits a readable, structured form of the SSA statements and a simple DOT view of the CFG.

use crate::{
    cfg::{Cfg, EdgeType},
    ssa::{BinOp, Constant, Expr, Stmt, UnOp, Var},
};

#[derive(Default)]
pub struct CodeWriter {
    output: String,
    indent: usize,
}

impl CodeWriter {
    pub fn new() -> Self {
        Self::default()
    }

    /// Write a sequence of structured statements.
    pub fn write_block(&mut self, code: &[Stmt]) {
        for stmt in code {
            self.write_stmt(stmt);
        }
    }

    pub fn write_stmt(&mut self, stmt: &Stmt) {
        match stmt {
            Stmt::Assign { dst, expr } => {
                let lhs = fmt_var(dst);
                let rhs = fmt_expr(expr);
                self.write_line(&format!("{lhs} = {rhs};"));
            }
            Stmt::Expr(expr) => {
                let e = fmt_expr(expr);
                self.write_line(&format!("{e};"));
            }
            Stmt::StackOp(op) => {
                let pops = op.pops.iter().map(fmt_var).collect::<Vec<_>>().join(", ");
                let pushes = op.pushes.iter().map(fmt_var).collect::<Vec<_>>().join(", ");
                self.write_line(&format!(
                    "stackop {:?}  // pops [{pops}], pushes [{pushes}]",
                    op.inst
                ));
            }
            Stmt::Instr(inst) => self.write_line(&format!("{inst}")),
            Stmt::If { cond, then_body, else_body } => {
                let c = fmt_expr(cond);
                self.write_line(&format!("if ({c}) {{"));
                self.indent();
                self.write_block(then_body);
                self.dedent();
                if !else_body.is_empty() {
                    self.write_line("} else {");
                    self.indent();
                    self.write_block(else_body);
                    self.dedent();
                }
                self.write_line("}");
            }
            Stmt::Switch { expr, cases, default } => {
                let e = fmt_expr(expr);
                self.write_line(&format!("switch ({e}) {{"));
                self.indent();
                for (val, body) in cases {
                    self.write_line(&format!("case {}:", fmt_constant(val)));
                    self.indent();
                    self.write_block(body);
                    self.dedent();
                }
                if !default.is_empty() {
                    self.write_line("default:");
                    self.indent();
                    self.write_block(default);
                    self.dedent();
                }
                self.dedent();
                self.write_line("}");
            }
            Stmt::While { cond, body } => {
                let c = fmt_expr(cond);
                let keyword =
                    if matches!(cond, Expr::True) { "loop".to_string() } else { format!("while ({c})") };
                self.write_line(&format!("{keyword} {{"));
                self.indent();
                self.write_block(body);
                self.dedent();
                self.write_line("}");
            }
            Stmt::Break => self.write_line("break;"),
            Stmt::Continue => self.write_line("continue;"),
            Stmt::Phi { .. } | Stmt::Unknown | Stmt::Nop | Stmt::Branch(_) => {
                self.write_line(&format!("{:?}", stmt));
            }
        }
    }

    pub fn indent(&mut self) {
        self.indent += 1;
    }

    pub fn dedent(&mut self) {
        self.indent = self.indent.saturating_sub(1);
    }

    pub fn finish(self) -> String {
        self.output
    }

    fn write_line(&mut self, line: &str) {
        for _ in 0..self.indent {
            self.output.push_str("  ");
        }
        self.output.push_str(line);
        self.output.push('\n');
    }
}

/// Emit a simple DOT representation of the CFG.
pub fn cfg_to_dot(cfg: &Cfg) -> String {
    let mut out = String::from("digraph cfg {\n");
    for (idx, node) in cfg.nodes.iter().enumerate() {
        out.push_str(&format!("  n{idx} [label=\"{}\"];\n", idx));
        for edge in &node.next {
            let label = match edge.cond.edge_type {
                EdgeType::Unconditional => "".to_string(),
                EdgeType::Conditional(true) => "T".to_string(),
                EdgeType::Conditional(false) => "F".to_string(),
            };
            out.push_str(&format!("  n{idx} -> n{} [label=\"{}\"];\n", edge.node, label));
        }
    }
    out.push_str("}\n");
    out
}

fn fmt_var(v: &Var) -> String {
    if v.subscript == 0 {
        format!("v{}", v.index)
    } else {
        format!("v{}_{}", v.index, v.subscript)
    }
}

fn fmt_constant(c: &Constant) -> String {
    match c {
        Constant::Felt(v) => v.to_string(),
        Constant::Word(w) => format!("[{}, {}, {}, {}]", w[0], w[1], w[2], w[3]),
        Constant::Defined(name) => name.clone(),
    }
}

fn fmt_expr(expr: &Expr) -> String {
    match expr {
        Expr::True => "true".to_string(),
        Expr::Unknown => "<?>".to_string(),
        Expr::Var(v) => fmt_var(v),
        Expr::Constant(c) => fmt_constant(c),
        Expr::Unary(op, inner) => {
            let op_str = match op {
                UnOp::Not => "!",
                UnOp::Neg => "-",
            };
            format!("{op_str}{}", fmt_expr(inner))
        }
        Expr::BinOp(op, a, b) => {
            let op_str = match op {
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Div => "/",
                BinOp::And => "&",
                BinOp::Or => "|",
                BinOp::Xor => "^",
                BinOp::Eq => "==",
                BinOp::Neq => "!=",
                BinOp::Lt => "<",
                BinOp::Lte => "<=",
                BinOp::Gt => ">",
                BinOp::Gte => ">=",
            };
            format!("({} {} {})", fmt_expr(a), op_str, fmt_expr(b))
        }
    }
}
