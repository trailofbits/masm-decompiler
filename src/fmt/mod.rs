//! Pretty-printing helpers that emit a readable structured view of SSA statements and DOT CFGs.

use crate::{
    cfg::{Cfg, Edge},
    decompile::{DecompiledHeader, DecompiledProc},
    ssa::{
        AdvLoad, AdvStore, BinOp, Call, Condition, Constant, Expr, IndexExpr, Intrinsic, LocalLoad,
        LocalStore, MemLoad, MemStore, Stmt, Subscript, UnOp, Var,
    },
};
use yansi::Paint;

/// Syntax highlighting colors for decompiled output.
mod colors {
    use yansi::Color;

    pub const KEYWORD: Color = Color::Blue;
    pub const VARIABLE: Color = Color::Yellow;
    pub const CONSTANT: Color = Color::Yellow;
    pub const COMMENT: Color = Color::Green;
    pub const TYPE: Color = Color::Blue;
    pub const FUNCTION: Color = Color::BrightBlue;
}

/// Configuration for code output formatting.
#[derive(Debug, Clone)]
pub struct FormattingConfig {
    /// Enable ANSI color codes in output.
    ///
    /// Default: `true`
    pub color: bool,

    /// Number of spaces per indentation level.
    ///
    /// Default: `2`
    pub indent_size: usize,
}

impl Default for FormattingConfig {
    fn default() -> Self {
        Self {
            color: true,
            indent_size: 2,
        }
    }
}

impl FormattingConfig {
    /// Create a new config with default settings.
    pub fn new() -> Self {
        Self::default()
    }

    /// Set whether color output is enabled.
    pub fn with_color(mut self, enabled: bool) -> Self {
        self.color = enabled;
        self
    }

    /// Set the indentation size in spaces.
    pub fn with_indent_size(mut self, size: usize) -> Self {
        self.indent_size = size;
        self
    }
}

/// Format a keyword with syntax highlighting.
pub fn keyword(s: &str) -> String {
    s.fg(colors::KEYWORD).bold().to_string()
}

/// Format a variable name with syntax highlighting.
pub fn variable(s: String) -> String {
    s.fg(colors::VARIABLE).to_string()
}

/// Format a constant value with syntax highlighting.
pub fn constant(s: String) -> String {
    s.fg(colors::CONSTANT).to_string()
}

/// Format a comment with syntax highlighting.
pub fn comment(s: &str) -> String {
    s.fg(colors::COMMENT).italic().to_string()
}

/// Format a type name with syntax highlighting.
pub fn type_name(s: &str) -> String {
    s.fg(colors::TYPE).to_string()
}

/// Format a function/intrinsic name with syntax highlighting.
pub fn function_name(s: &str) -> String {
    s.fg(colors::FUNCTION).to_string()
}

/// Trait for rendering IR nodes with indentation-aware `CodeWriter`.
pub trait CodeDisplay {
    fn fmt_code(&self, f: &mut CodeWriter);
}

/// Pretty-printer for decompiled code with configurable formatting.
pub struct CodeWriter {
    config: FormattingConfig,
    output: String,
    indent: usize,
    var_names: std::collections::HashMap<Var, String>,
    /// Maps loop variable indices to their names (i, j, k, ...).
    loop_var_names: std::collections::HashMap<usize, String>,
    /// Set of loop variable indices that are currently "active" (inside their loop).
    /// Used to distinguish loop variables from regular variables with the same index.
    active_loop_vars: std::collections::HashSet<usize>,
    loop_depth: usize,
}

impl Default for CodeWriter {
    fn default() -> Self {
        Self::with_config(FormattingConfig::default())
    }
}

impl CodeWriter {
    /// Create a new code writer with default configuration.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new code writer with custom configuration.
    pub fn with_config(config: FormattingConfig) -> Self {
        // Disable yansi coloring globally if color is disabled
        if !config.color {
            yansi::disable();
        }
        Self {
            config,
            output: String::new(),
            indent: 0,
            var_names: std::collections::HashMap::new(),
            loop_var_names: std::collections::HashMap::new(),
            active_loop_vars: std::collections::HashSet::new(),
            loop_depth: 0,
        }
    }

    /// Create a new code writer with pre-defined variable names.
    pub fn with_var_names(var_names: std::collections::HashMap<Var, String>) -> Self {
        Self {
            var_names,
            ..Self::default()
        }
    }

    /// Pre-register all loop variables from the code.
    ///
    /// TODO: Move this to structuring.
    pub fn register_loop_vars(&mut self, code: &[Stmt]) {
        self.register_loop_vars_inner(code);
    }

    fn register_loop_vars_inner(&mut self, code: &[Stmt]) {
        for stmt in code {
            match stmt {
                Stmt::Repeat { loop_var, body, .. } => {
                    let name = loop_name_for_depth(self.loop_depth);
                    self.loop_var_names.insert(loop_var.index, name);
                    self.loop_depth += 1;
                    self.register_loop_vars_inner(body);
                    self.loop_depth -= 1;
                }
                Stmt::While { body, .. } => {
                    self.register_loop_vars_inner(body);
                }
                Stmt::If {
                    then_body,
                    else_body,
                    ..
                } => {
                    self.register_loop_vars_inner(then_body);
                    self.register_loop_vars_inner(else_body);
                }
                _ => {}
            }
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
        let spaces = " ".repeat(self.config.indent_size);
        for _ in 0..self.indent {
            self.output.push_str(&spaces);
        }
        self.output.push_str(line);
        self.output.push('\n');
    }

    /// Format a variable with syntax highlighting.
    pub fn fmt_var(&self, v: &Var) -> String {
        // Only use loop variable names for active loop variables (those currently in scope).
        // This prevents regular variables from being incorrectly named as loop variables
        // when they happen to have the same index after renaming.
        if self.active_loop_vars.contains(&v.index) {
            if let Some(name) = self.loop_var_names.get(&v.index) {
                return variable(name.clone());
            }
        }
        if let Some(name) = self.var_names.get(v) {
            return variable(name.clone());
        }

        // Format variable using only subscript when present.
        // This produces clean output like "v_0", "v_i", "v_(2*i + 1)" instead of "v_1_(i)".
        let raw = match &v.subscript {
            Subscript::None => {
                // Fallback: no subscript assigned (shouldn't happen after rename pass).
                format!("v_{}", v.index)
            }
            Subscript::Expr(IndexExpr::Const(n)) => {
                // Concrete subscript: v_0, v_1, etc.
                format!("v_{}", n)
            }
            Subscript::Expr(IndexExpr::LoopVar(idx)) => {
                // Single loop variable: v_i, v_j, etc.
                let loop_name = self.loop_var_name(*idx);
                format!("v_{}", loop_name)
            }
            Subscript::Expr(expr) => {
                // Complex expression: v_(2*i + 1), etc.
                format!("v_({})", self.fmt_index_expr(expr))
            }
        };
        variable(raw)
    }

    fn enter_loop(&mut self, loop_var: &Var) {
        let name = loop_name_for_depth(self.loop_depth);
        self.loop_var_names.insert(loop_var.index, name);
        self.active_loop_vars.insert(loop_var.index);
        self.loop_depth += 1;
    }

    fn exit_loop(&mut self, loop_var: &Var) {
        self.loop_depth = self.loop_depth.saturating_sub(1);
        self.active_loop_vars.remove(&loop_var.index);
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
                        // -1 * rhs => show as "lhs - rhs" (omit the 1)
                        (IndexExpr::Const(-1), rhs) => {
                            format!("{lhs} - {}", self.fmt_index_expr(rhs))
                        }
                        // c * rhs where c < 0 => show as "lhs - |c| * rhs"
                        (IndexExpr::Const(c), rhs) if *c < 0 => {
                            format!("{lhs} - {} * {}", -c, self.fmt_index_expr(rhs))
                        }
                        // lhs_term * -1 => show as "lhs - lhs_term" (omit the 1)
                        (lhs_term, IndexExpr::Const(-1)) => {
                            format!("{lhs} - {}", self.fmt_index_expr(lhs_term))
                        }
                        // lhs_term * c where c < 0 => show as "lhs - |c| * lhs_term"
                        (lhs_term, IndexExpr::Const(c)) if *c < 0 => {
                            format!("{lhs} - {} * {}", -c, self.fmt_index_expr(lhs_term))
                        }
                        _ => format!("{lhs} + {}", self.fmt_index_expr(b)),
                    },
                    _ => format!("{lhs} + {}", self.fmt_index_expr(b)),
                }
            }
            IndexExpr::Mul(a, b) => {
                // Omit coefficient of 1: "1 * x" => "x"
                match (&**a, &**b) {
                    (IndexExpr::Const(1), rhs) => self.fmt_index_expr(rhs),
                    (lhs, IndexExpr::Const(1)) => self.fmt_index_expr(lhs),
                    _ => format!("{} * {}", self.fmt_index_expr(a), self.fmt_index_expr(b)),
                }
            }
        }
    }
}

impl CodeDisplay for &DecompiledProc {
    fn fmt_code(&self, f: &mut CodeWriter) {
        f.register_loop_vars(self.stmts());

        // Write procedure header
        f.write(self.header());

        // Write body
        f.indent();
        for stmt in self.stmts() {
            f.write(stmt.clone());
        }
        f.dedent();
        f.write_line("}");
    }
}

impl CodeDisplay for DecompiledHeader {
    fn fmt_code(&self, f: &mut CodeWriter) {
        // Build argument list
        let mut args = Vec::new();
        for i in 0..self.inputs {
            let v = Var::new(i);
            args.push(f.fmt_var(&v));
        }
        let arg_list = args.join(", ");

        // Build return type list
        let ret_list = match self.outputs {
            0 => String::new(),
            1 => format!(" -> {}", type_name("Felt")),
            n => {
                let types = (0..n)
                    .map(|_| type_name("Felt"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!(" -> ({})", types)
            }
        };

        f.write_line(&format!(
            "{} {}({}){} {{",
            keyword("proc"),
            self.name,
            arg_list,
            ret_list
        ));
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
                    f.write_line(&format!("{};", keyword("return")));
                } else {
                    f.write_line(&format!("{} {vals};", keyword("return")));
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
                    f.write_line(&format!("{}({args});", function_name("mem_load")));
                } else {
                    f.write_line(&format!("{outs} = {}({args});", function_name("mem_load")));
                }
            }
            Stmt::MemStore(MemStore { address, values }) => {
                let args = address
                    .iter()
                    .chain(values.iter())
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                f.write_line(&format!("{}({args});", function_name("mem_store")));
            }
            Stmt::AdvLoad(AdvLoad { outputs }) => {
                let outs = outputs
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                if outs.is_empty() {
                    f.write_line(&format!("{}();", function_name("adv_load")));
                } else {
                    f.write_line(&format!("{outs} = {}();", function_name("adv_load")));
                }
            }
            Stmt::AdvStore(AdvStore { values }) => {
                let args = values
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                f.write_line(&format!("{}({args});", function_name("adv_store")));
            }
            Stmt::LocalLoad(LocalLoad { index, outputs }) => {
                let outs = outputs
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                if outs.is_empty() {
                    f.write_line(&format!("{}.{index}();", function_name("loc_load")));
                } else {
                    f.write_line(&format!(
                        "{outs} = {}.{index}();",
                        function_name("loc_load")
                    ));
                }
            }
            Stmt::LocalStore(LocalStore { index, values }) => {
                let args = values
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                f.write_line(&format!("{}.{index}({args});", function_name("loc_store")));
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
                    f.write_line(&format!("{}({args});", function_name("dyncall")));
                } else {
                    f.write_line(&format!("{outs} = {}({args});", function_name("dyncall")));
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
                    f.write_line(&format!("{}({args});", function_name(name)));
                } else {
                    f.write_line(&format!("{outs} = {}({args});", function_name(name)));
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
                f.write_line(&format!("{} ({}) {{", keyword("if"), fmt_expr(f, cond, 0)));
                f.indent();
                f.write_block(then_body);
                f.dedent();
                if !else_body.is_empty() {
                    f.write_line(&format!("}} {} {{", keyword("else")));
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
                let var_name = f.fmt_var(loop_var);
                f.write_line(&format!(
                    "{} {var_name} {} {}..{} {{",
                    keyword("for"),
                    keyword("in"),
                    constant("0".to_string()),
                    constant(loop_count.to_string())
                ));
                f.indent();
                f.write_block(body);
                f.dedent();
                f.write_line("}");
                f.exit_loop(loop_var);
            }
            Stmt::While { cond, body } => {
                let head = if matches!(cond, Expr::True) {
                    keyword("loop")
                } else {
                    format!("{} ({})", keyword("while"), fmt_expr(f, cond, 0))
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
                f.write_line(&format!(
                    "{} {} = [{srcs}];",
                    keyword("phi"),
                    f.fmt_var(var)
                ));
            }
            Stmt::IfBranch(cond) => {
                f.write_line(&format!(
                    "{} {};",
                    keyword("if_branch"),
                    fmt_condition(f, cond)
                ));
            }
            Stmt::WhileBranch(cond) => {
                f.write_line(&format!(
                    "{} {};",
                    keyword("while_branch"),
                    fmt_condition(f, cond)
                ));
            }
            Stmt::RepeatBranch(cond) => {
                f.write_line(&format!(
                    "{} {};",
                    keyword("repeat_branch"),
                    fmt_condition(f, cond)
                ));
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

fn fmt_condition(f: &CodeWriter, cond: &Condition) -> String {
    match cond {
        Condition::Stack(expr) => fmt_expr(f, expr, 0),
        Condition::Count { count, loop_var } => {
            let var_str = loop_var
                .as_ref()
                .map(|v| f.fmt_var(v))
                .unwrap_or_else(|| "?".to_string());
            format!("{var_str} in [0, {count})")
        }
    }
}

fn fmt_constant(c: &Constant) -> String {
    let raw = match c {
        Constant::Felt(v) => v.to_string(),
        Constant::Word(w) => format!("[{}, {}, {}, {}]", w[0], w[1], w[2], w[3]),
        Constant::Defined(name) => name.clone(),
    };
    constant(raw)
}

fn fmt_expr(f: &CodeWriter, expr: &Expr, parent_prec: u8) -> String {
    match expr {
        Expr::True => keyword("true"),
        Expr::False => keyword("false"),
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
    let head = format!("{} {}", keyword(kind), function_name(&call.target));
    if outs.is_empty() {
        f.write_line(&format!("{head}({args});"));
    } else {
        f.write_line(&format!("{outs} = {head}({args});"));
    }
}
