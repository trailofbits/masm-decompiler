//! Pretty-printing helpers that emit a readable structured view of IR statements.

use crate::{
    decompile::{DecompiledHeader, DecompiledProc},
    ir::{
        AdvLoad, AdvStore, BinOp, Call, Constant, Expr, IndexExpr, Intrinsic, LocalAccessKind,
        LocalLoad, LocalStore, LocalStoreW, LoopVar, MemAccessKind, MemLoad, MemStore, Stmt, UnOp,
        ValueId, Var, VarBase,
    },
    types::{InferredType, TypeRequirement},
};
use std::collections::{HashMap, HashSet};
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

/// Accumulated variable usage information for name assignment.
#[derive(Debug, Default)]
struct VarUsage {
    /// Variables in first-seen order.
    vars_in_order: Vec<Var>,
    /// Set of variables already recorded.
    seen: HashSet<Var>,
    /// SSA value IDs defined in the statement sequence.
    defined_ids: HashSet<ValueId>,
    /// SSA value IDs used in the statement sequence.
    used_ids: HashSet<ValueId>,
}

impl VarUsage {
    /// Record a variable occurrence, preserving first-seen order.
    fn record_var(&mut self, var: &Var) {
        if self.seen.insert(var.clone()) {
            self.vars_in_order.push(var.clone());
        }
    }

    /// Record a variable use.
    fn record_use(&mut self, var: &Var) {
        self.record_var(var);
        if let VarBase::Value(id) = var.base {
            self.used_ids.insert(id);
        }
    }

    /// Record a variable definition.
    fn record_def(&mut self, var: &Var) {
        self.record_var(var);
        if let VarBase::Value(id) = var.base {
            self.defined_ids.insert(id);
        }
    }
}

/// Assign stable, unique display names to variables based on SSA identity.
///
/// Input variables and repeat-loop entry values keep their base names
/// (`v_6`, `v_(3 - i)`), while later definitions that collide are suffixed
/// (`v_6_1`, `v_(3 - i)_1`).
pub fn assign_var_names(stmts: &[Stmt]) -> HashMap<Var, String> {
    let alias_names = collect_phi_alias_names(stmts);
    let usage = collect_var_usage(stmts);
    let input_ids: HashSet<ValueId> = usage
        .used_ids
        .difference(&usage.defined_ids)
        .cloned()
        .collect();

    let mut names = HashMap::new();
    let mut name_counts = HashMap::new();

    for name in alias_names.values() {
        name_counts.entry(name.clone()).or_insert(1);
    }
    for (var, name) in alias_names {
        names.insert(var, name);
    }

    for var in usage.vars_in_order.iter() {
        if is_reserved_var(var, &input_ids) {
            assign_name_for_var(var, &mut names, &mut name_counts);
        }
    }

    for var in usage.vars_in_order.iter() {
        if !names.contains_key(var) {
            assign_name_for_var(var, &mut names, &mut name_counts);
        }
    }

    names
}

/// Collect variable usage data for a statement list.
fn collect_var_usage(stmts: &[Stmt]) -> VarUsage {
    let mut usage = VarUsage::default();
    for stmt in stmts {
        collect_stmt_usage(stmt, &mut usage);
    }
    usage
}

/// Collect variable usage data for a single statement.
fn collect_stmt_usage(stmt: &Stmt, usage: &mut VarUsage) {
    match stmt {
        Stmt::Assign { dest, expr, .. } => {
            usage.record_def(dest);
            collect_expr_usage(expr, usage);
        }
        Stmt::MemLoad { load, .. } => {
            for v in &load.address {
                usage.record_use(v);
            }
            for v in &load.outputs {
                usage.record_def(v);
            }
        }
        Stmt::MemStore { store, .. } => {
            for v in &store.address {
                usage.record_use(v);
            }
            for v in &store.values {
                usage.record_use(v);
            }
        }
        Stmt::AdvLoad { load, .. } => {
            for v in &load.outputs {
                usage.record_def(v);
            }
        }
        Stmt::AdvStore { store, .. } => {
            for v in &store.values {
                usage.record_use(v);
            }
        }
        Stmt::LocalLoad { load, .. } => {
            for v in &load.outputs {
                usage.record_def(v);
            }
        }
        Stmt::LocalStore { store, .. } => {
            for v in &store.values {
                usage.record_use(v);
            }
        }
        Stmt::LocalStoreW { store, .. } => {
            for v in &store.values {
                usage.record_use(v);
            }
        }
        Stmt::Call { call, .. } | Stmt::Exec { call, .. } | Stmt::SysCall { call, .. } => {
            for v in &call.args {
                usage.record_use(v);
            }
            for v in &call.results {
                usage.record_def(v);
            }
        }
        Stmt::DynCall { args, results, .. } => {
            for v in args {
                usage.record_use(v);
            }
            for v in results {
                usage.record_def(v);
            }
        }
        Stmt::Intrinsic { intrinsic, .. } => {
            for v in &intrinsic.args {
                usage.record_use(v);
            }
            for v in &intrinsic.results {
                usage.record_def(v);
            }
        }
        Stmt::Repeat { body, phis, .. } => {
            for phi in phis {
                usage.record_def(&phi.dest);
                usage.record_use(&phi.init);
                usage.record_use(&phi.step);
            }
            for stmt in body {
                collect_stmt_usage(stmt, usage);
            }
        }
        Stmt::If {
            cond,
            then_body,
            else_body,
            phis,
            ..
        } => {
            collect_expr_usage(cond, usage);
            for phi in phis {
                usage.record_def(&phi.dest);
                usage.record_use(&phi.then_var);
                usage.record_use(&phi.else_var);
            }
            for stmt in then_body {
                collect_stmt_usage(stmt, usage);
            }
            for stmt in else_body {
                collect_stmt_usage(stmt, usage);
            }
        }
        Stmt::While {
            cond, body, phis, ..
        } => {
            collect_expr_usage(cond, usage);
            for phi in phis {
                usage.record_def(&phi.dest);
                usage.record_use(&phi.init);
                usage.record_use(&phi.step);
            }
            for stmt in body {
                collect_stmt_usage(stmt, usage);
            }
        }
        Stmt::Return { values, .. } => {
            for v in values {
                usage.record_use(v);
            }
        }
    }
}

/// Collect variable usage data from an expression.
fn collect_expr_usage(expr: &Expr, usage: &mut VarUsage) {
    match expr {
        Expr::Var(v) => usage.record_use(v),
        Expr::Binary(_, lhs, rhs) => {
            collect_expr_usage(lhs, usage);
            collect_expr_usage(rhs, usage);
        }
        Expr::Unary(_, inner) => collect_expr_usage(inner, usage),
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            collect_expr_usage(cond, usage);
            collect_expr_usage(then_expr, usage);
            collect_expr_usage(else_expr, usage);
        }
        Expr::EqW { lhs, rhs } => {
            for v in lhs {
                usage.record_use(v);
            }
            for v in rhs {
                usage.record_use(v);
            }
        }
        Expr::True | Expr::False | Expr::Constant(_) => {}
    }
}

/// Determine whether a variable should keep its base name.
fn is_reserved_var(var: &Var, input_ids: &HashSet<ValueId>) -> bool {
    match &var.base {
        VarBase::LoopInput { .. } => true,
        VarBase::Value(id) => input_ids.contains(id),
    }
}

/// Assign a unique display name for a variable based on its subscript.
fn assign_name_for_var(
    var: &Var,
    names: &mut HashMap<Var, String>,
    name_counts: &mut HashMap<String, usize>,
) {
    if names.contains_key(var) {
        return;
    }
    let base = base_name_for_var(var);
    let count = name_counts.entry(base.clone()).or_insert(0);
    let name = if *count == 0 {
        base.clone()
    } else {
        format!("{base}_{}", *count)
    };
    *count += 1;
    names.insert(var.clone(), name);
}

/// Build the base display name for a variable from its subscript.
fn base_name_for_var(var: &Var) -> String {
    match &var.subscript {
        IndexExpr::Const(n) => format!("v_{}", n),
        IndexExpr::LoopVar(idx) => format!("v_{}", loop_name_for_depth(*idx)),
        expr => format!("v_({})", format_index_expr_for_name(expr)),
    }
}

/// Format an index expression without syntax highlighting.
fn format_index_expr_for_name(expr: &IndexExpr) -> String {
    match expr {
        IndexExpr::Const(v) => v.to_string(),
        IndexExpr::LoopVar(idx) => loop_name_for_depth(*idx),
        IndexExpr::Add(a, b) => {
            let lhs = format_index_expr_for_name(a);
            match &**b {
                IndexExpr::Const(c) if *c < 0 => format!("{lhs} - {}", -c),
                IndexExpr::Mul(x, y) => match (&**x, &**y) {
                    (IndexExpr::Const(-1), rhs) => {
                        format!("{lhs} - {}", format_index_expr_for_name(rhs))
                    }
                    (IndexExpr::Const(c), rhs) if *c < 0 => {
                        format!("{lhs} - {} * {}", -c, format_index_expr_for_name(rhs))
                    }
                    (lhs_term, IndexExpr::Const(-1)) => {
                        format!("{lhs} - {}", format_index_expr_for_name(lhs_term))
                    }
                    (lhs_term, IndexExpr::Const(c)) if *c < 0 => {
                        format!("{lhs} - {} * {}", -c, format_index_expr_for_name(lhs_term))
                    }
                    _ => format!("{lhs} + {}", format_index_expr_for_name(b)),
                },
                _ => format!("{lhs} + {}", format_index_expr_for_name(b)),
            }
        }
        IndexExpr::Mul(a, b) => match (&**a, &**b) {
            (IndexExpr::Const(1), rhs) => format_index_expr_for_name(rhs),
            (lhs, IndexExpr::Const(1)) => format_index_expr_for_name(lhs),
            _ => format!(
                "{} * {}",
                format_index_expr_for_name(a),
                format_index_expr_for_name(b)
            ),
        },
    }
}

fn collect_phi_alias_names(stmts: &[Stmt]) -> HashMap<Var, String> {
    let mut aliases = HashMap::new();
    for stmt in stmts {
        collect_phi_alias_names_stmt(stmt, &mut aliases);
    }
    aliases
}

fn collect_phi_alias_names_stmt(stmt: &Stmt, aliases: &mut HashMap<Var, String>) {
    match stmt {
        Stmt::Repeat { body, phis, .. } => {
            for phi in phis {
                let base = base_name_for_var(&phi.init);
                aliases
                    .entry(phi.init.clone())
                    .or_insert_with(|| base.clone());
                aliases
                    .entry(phi.dest.clone())
                    .or_insert_with(|| base.clone());
                aliases
                    .entry(phi.step.clone())
                    .or_insert_with(|| base.clone());
            }
            for stmt in body {
                collect_phi_alias_names_stmt(stmt, aliases);
            }
        }
        Stmt::If {
            then_body,
            else_body,
            ..
        } => {
            for stmt in then_body {
                collect_phi_alias_names_stmt(stmt, aliases);
            }
            for stmt in else_body {
                collect_phi_alias_names_stmt(stmt, aliases);
            }
        }
        Stmt::While { body, phis, .. } => {
            for phi in phis {
                let base = base_name_for_var(&phi.init);
                aliases
                    .entry(phi.init.clone())
                    .or_insert_with(|| base.clone());
                aliases
                    .entry(phi.dest.clone())
                    .or_insert_with(|| base.clone());
                aliases
                    .entry(phi.step.clone())
                    .or_insert_with(|| base.clone());
            }
            for stmt in body {
                collect_phi_alias_names_stmt(stmt, aliases);
            }
        }
        _ => {}
    }
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
    /// Maps loop variable stack_depth to their names (i, j, k, ...).
    loop_var_names: std::collections::HashMap<usize, String>,
    /// Set of loop variable stack_depths that are currently "active" (inside their loop).
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
    pub fn register_loop_vars(&mut self, code: &[Stmt]) {
        self.register_loop_vars_inner(code);
    }

    fn register_loop_vars_inner(&mut self, code: &[Stmt]) {
        for stmt in code {
            match stmt {
                Stmt::Repeat { loop_var, body, .. } => {
                    let name = loop_name_for_depth(self.loop_depth);
                    self.loop_var_names.insert(loop_var.loop_depth, name);
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
    ///
    /// Variables are formatted based on their subscripts:
    /// - `IndexExpr::Const(n)`: Format as `v_n`
    /// - `IndexExpr::LoopVar(idx)`: Format as `v_i`, `v_j`, etc.
    /// - Complex expressions: Format as `v_(expr)`
    ///
    /// Note: We do NOT identify loop counters by stack_depth matching, as that
    /// would incorrectly treat regular variables at the loop entry depth as
    /// loop counters. Loop-dependent variables should have explicit LoopVar
    /// subscripts.
    pub fn fmt_var(&self, v: &Var) -> String {
        if let Some(name) = self.var_names.get(v) {
            return variable(name.clone());
        }

        // Format variable based on subscript.
        let raw = match &v.subscript {
            IndexExpr::Const(n) => {
                // Concrete subscript: v_0, v_1, etc.
                format!("v_{}", n)
            }
            IndexExpr::LoopVar(idx) => {
                // Single loop variable: v_i, v_j, etc.
                let loop_name = self.loop_var_name(*idx);
                format!("v_{}", loop_name)
            }
            expr => {
                // Complex expression: v_(2*i + 1), etc.
                format!("v_({})", self.fmt_index_expr(expr))
            }
        };
        variable(raw)
    }

    fn enter_loop(&mut self, loop_var: &LoopVar) {
        let name = loop_name_for_depth(self.loop_depth);
        self.loop_var_names.insert(loop_var.loop_depth, name);
        self.active_loop_vars.insert(loop_var.loop_depth);
        self.loop_depth += 1;
    }

    fn exit_loop(&mut self, loop_var: &LoopVar) {
        self.loop_depth = self.loop_depth.saturating_sub(1);
        self.active_loop_vars.remove(&loop_var.loop_depth);
    }

    /// Format the loop counter variable for use in the `for` header.
    ///
    /// This always uses the loop counter name (i, j, k, ...), regardless of
    /// the variable's subscript. This is separate from `fmt_var` to ensure
    /// that only the loop header uses the counter name, not other variables
    /// that happen to be at the same stack depth.
    fn fmt_loop_counter(&self, loop_var: &LoopVar) -> String {
        if let Some(name) = self.loop_var_names.get(&loop_var.loop_depth) {
            return variable(name.clone());
        }
        // Fallback (shouldn't happen if enter_loop was called)
        variable(format!("i{}", self.loop_depth))
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
                        (IndexExpr::Const(-1), rhs) => {
                            format!("{lhs} - {}", self.fmt_index_expr(rhs))
                        }
                        (IndexExpr::Const(c), rhs) if *c < 0 => {
                            format!("{lhs} - {} * {}", -c, self.fmt_index_expr(rhs))
                        }
                        (lhs_term, IndexExpr::Const(-1)) => {
                            format!("{lhs} - {}", self.fmt_index_expr(lhs_term))
                        }
                        (lhs_term, IndexExpr::Const(c)) if *c < 0 => {
                            format!("{lhs} - {} * {}", -c, self.fmt_index_expr(lhs_term))
                        }
                        _ => format!("{lhs} + {}", self.fmt_index_expr(b)),
                    },
                    _ => format!("{lhs} + {}", self.fmt_index_expr(b)),
                }
            }
            IndexExpr::Mul(a, b) => match (&**a, &**b) {
                (IndexExpr::Const(1), rhs) => self.fmt_index_expr(rhs),
                (lhs, IndexExpr::Const(1)) => self.fmt_index_expr(lhs),
                _ => format!("{} * {}", self.fmt_index_expr(a), self.fmt_index_expr(b)),
            },
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
            let v = Var::new(ValueId::from(i as u64), i);
            let ty = self
                .input_types
                .get(i)
                .copied()
                .unwrap_or(TypeRequirement::Unknown);
            args.push(format!(
                "{}: {}",
                f.fmt_var(&v),
                type_name(type_requirement_for_display(ty))
            ));
        }
        let arg_list = args.join(", ");

        // Build return type list
        let ret_list = match self.outputs {
            0 => String::new(),
            1 => {
                let ty = self
                    .output_types
                    .first()
                    .copied()
                    .unwrap_or(InferredType::Unknown);
                format!(" -> {}", type_name(inferred_type_for_display(ty)))
            }
            n => {
                let types = (0..n)
                    .map(|idx| {
                        let ty = self
                            .output_types
                            .get(idx)
                            .copied()
                            .unwrap_or(InferredType::Unknown);
                        type_name(inferred_type_for_display(ty))
                    })
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

/// Convert an input type requirement to its formatter display string.
///
/// Unknown requirements are rendered as `Felt`.
fn type_requirement_for_display(requirement: TypeRequirement) -> &'static str {
    match requirement {
        TypeRequirement::Unknown | TypeRequirement::Felt => "Felt",
        TypeRequirement::Bool => "Bool",
        TypeRequirement::U32 => "U32",
        TypeRequirement::Address => "Address",
    }
}

/// Convert an inferred output type to its formatter display string.
///
/// Unknown inferred outputs are rendered as `Felt`.
fn inferred_type_for_display(ty: InferredType) -> &'static str {
    match ty {
        InferredType::Unknown | InferredType::Felt => "Felt",
        InferredType::Bool => "Bool",
        InferredType::U32 => "U32",
        InferredType::Address => "Address",
    }
}

impl CodeDisplay for Stmt {
    fn fmt_code(&self, f: &mut CodeWriter) {
        match self {
            Stmt::Assign {
                dest: dst, expr, ..
            } => {
                let rhs = fmt_expr(f, expr, 0);
                let rhs = if is_boolean_binary_expr(expr) {
                    format!("({rhs})")
                } else {
                    rhs
                };
                f.write_line(&format!("{} = {rhs};", f.fmt_var(dst)));
            }
            Stmt::Return { values, .. } => {
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
            Stmt::MemLoad {
                load:
                    MemLoad {
                        kind,
                        address,
                        outputs,
                    },
                ..
            } => {
                let addr = address
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                let outs = outputs
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                let access = mem_access_name(*kind);
                match kind {
                    MemAccessKind::Element => {
                        f.write_line(&format!("{outs} = {access}[{addr}];"));
                    }
                    MemAccessKind::WordBe | MemAccessKind::WordLe => {
                        f.write_line(&format!("({outs}) = {access}[{addr}];"));
                    }
                }
            }
            Stmt::MemStore {
                store:
                    MemStore {
                        kind,
                        address,
                        values,
                    },
                ..
            } => {
                let addr = address
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                let vals = values
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                let access = mem_access_name(*kind);
                match kind {
                    MemAccessKind::Element => {
                        f.write_line(&format!("{access}[{addr}] = {vals};"));
                    }
                    MemAccessKind::WordBe | MemAccessKind::WordLe => {
                        f.write_line(&format!("{access}[{addr}] = ({vals});"));
                    }
                }
            }
            Stmt::AdvLoad {
                load: AdvLoad { outputs },
                ..
            } => {
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
            Stmt::AdvStore {
                store: AdvStore { values },
                ..
            } => {
                let args = values
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                f.write_line(&format!("{}({args});", function_name("adv_store")));
            }
            Stmt::LocalLoad {
                load:
                    LocalLoad {
                        kind,
                        index,
                        outputs,
                    },
                ..
            } => {
                let outs = outputs
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                let access = local_access_name(*kind);
                match kind {
                    LocalAccessKind::Element => {
                        f.write_line(&format!("{outs} = {access}[{index}];"));
                    }
                    LocalAccessKind::WordBe | LocalAccessKind::WordLe => {
                        f.write_line(&format!("({outs}) = {access}[{index}];"));
                    }
                }
            }
            Stmt::LocalStore {
                store: LocalStore { index, values },
                ..
            } => {
                let vals = values
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                f.write_line(&format!("locals[{index}] = {vals};"));
            }
            Stmt::LocalStoreW {
                store:
                    LocalStoreW {
                        kind,
                        index,
                        values,
                    },
                ..
            } => {
                let vals = values
                    .iter()
                    .map(|v| f.fmt_var(v))
                    .collect::<Vec<_>>()
                    .join(", ");
                let access = local_access_name(*kind);
                f.write_line(&format!("{access}[{index}] = ({vals});"));
            }
            Stmt::Call { call, .. } => write_call_like("call", call, f),
            Stmt::Exec { call, .. } => write_call_like("exec", call, f),
            Stmt::SysCall { call, .. } => write_call_like("syscall", call, f),
            Stmt::DynCall { args, results, .. } => {
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
            Stmt::Intrinsic {
                intrinsic:
                    Intrinsic {
                        name,
                        args,
                        results,
                    },
                ..
            } => {
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
                if args.is_empty()
                    && let Some(index) = name.strip_prefix("locaddr.")
                {
                    let call = format!("{}({index})", function_name("locaddr"));
                    if outs.is_empty() {
                        f.write_line(&format!("{call};"));
                    } else {
                        f.write_line(&format!("{outs} = {call};"));
                    }
                    return;
                }
                if outs.is_empty() {
                    f.write_line(&format!("{}({args});", function_name(name)));
                } else {
                    f.write_line(&format!("{outs} = {}({args});", function_name(name)));
                }
            }
            Stmt::If {
                cond,
                then_body,
                else_body,
                ..
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
                ..
            } => {
                f.enter_loop(loop_var);
                let counter_name = f.fmt_loop_counter(loop_var);
                f.write_line(&format!(
                    "{} {counter_name} {} {}..{} {{",
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
            Stmt::While { cond, body, .. } => {
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
        Expr::Var(v) => f.fmt_var(v),
        Expr::Constant(c) => fmt_constant(c),
        Expr::EqW { lhs, rhs } => {
            let prec = 5;
            let lhs = format!(
                "({}, {}, {}, {})",
                f.fmt_var(&lhs[0]),
                f.fmt_var(&lhs[1]),
                f.fmt_var(&lhs[2]),
                f.fmt_var(&lhs[3])
            );
            let rhs = format!(
                "({}, {}, {}, {})",
                f.fmt_var(&rhs[0]),
                f.fmt_var(&rhs[1]),
                f.fmt_var(&rhs[2]),
                f.fmt_var(&rhs[3])
            );
            let expr_str = format!("{lhs} == {rhs}");
            if prec < parent_prec {
                format!("({expr_str})")
            } else {
                expr_str
            }
        }
        Expr::Unary(op, inner) => match op {
            UnOp::Not => {
                let inner_str = fmt_expr(f, inner, 5);
                format!("!{inner_str}")
            }
            UnOp::Neg => {
                let inner_str = fmt_expr(f, inner, 5);
                format!("-{inner_str}")
            }
            UnOp::Inv => format!("inv({})", fmt_expr(f, inner, 0)),
            UnOp::U32Cast => {
                let prec = 3;
                let inner_str = fmt_expr(f, inner, 0);
                let inner_str = if is_atomic_expr(inner) {
                    inner_str
                } else {
                    format!("({inner_str})")
                };
                let expr_str = format!("{inner_str} mod 2^32");
                if prec < parent_prec {
                    format!("({expr_str})")
                } else {
                    expr_str
                }
            }
            UnOp::U32Test => format!("is_u32({})", fmt_expr(f, inner, 0)),
            UnOp::U32Not => format!("not_u32({})", fmt_expr(f, inner, 0)),
            UnOp::U32Clz => format!("clz_u32({})", fmt_expr(f, inner, 0)),
            UnOp::U32Ctz => format!("ctz_u32({})", fmt_expr(f, inner, 0)),
            UnOp::U32Clo => format!("clo_u32({})", fmt_expr(f, inner, 0)),
            UnOp::U32Cto => format!("cto_u32({})", fmt_expr(f, inner, 0)),
            UnOp::Pow2 => {
                let prec = 11;
                let inner_str = fmt_expr(f, inner, prec);
                let expr_str = format!("2 ^ {inner_str}");
                if prec < parent_prec {
                    format!("({expr_str})")
                } else {
                    expr_str
                }
            }
        },
        Expr::Ternary {
            cond,
            then_expr,
            else_expr,
        } => {
            let prec = 2;
            let cond_str = fmt_expr(f, cond, prec);
            let then_str = fmt_expr(f, then_expr, prec);
            let else_str = fmt_expr(f, else_expr, prec + 1);
            let expr_str = format!("{cond_str} ? {then_str} : {else_str}");
            if prec < parent_prec {
                format!("({expr_str})")
            } else {
                expr_str
            }
        }
        Expr::Binary(op, a, b) => {
            if matches!(op, BinOp::U32Rotr) {
                let expr_str = format!("rotr_u32({}, {})", fmt_expr(f, a, 0), fmt_expr(f, b, 0));
                return if 0 < parent_prec {
                    format!("({expr_str})")
                } else {
                    expr_str
                };
            }
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
                BinOp::And => (7, "and"),
                BinOp::Or => (6, "or"),
                BinOp::Xor => (6, "xor"),
                BinOp::Eq => (5, "=="),
                BinOp::Neq => (5, "!="),
                BinOp::Lt => (4, "<"),
                BinOp::Lte => (4, "<="),
                BinOp::Gt => (4, ">"),
                BinOp::Gte => (4, ">="),
                BinOp::U32And => (7, "and_u32"),
                BinOp::U32Or => (6, "or_u32"),
                BinOp::U32Xor => (6, "xor_u32"),
                BinOp::U32Shl => (8, "<<_u32"),
                BinOp::U32Shr => (8, ">>_u32"),
                BinOp::U32Lt => (4, "<_u32"),
                BinOp::U32Lte => (4, "<=_u32"),
                BinOp::U32Gt => (4, ">_u32"),
                BinOp::U32Gte => (4, ">=_u32"),
                BinOp::U32WrappingMul => (10, "*_u32"),
                BinOp::U32WrappingAdd => (9, "+_u32"),
                BinOp::U32WrappingSub => (9, "-_u32"),
                BinOp::U32Exp => (11, "^_u32"),
                BinOp::U32Rotr => unreachable!("handled as function-style formatting above"),
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

/// Return true if expression can be embedded without explicit grouping.
fn is_atomic_expr(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::True | Expr::False | Expr::Var(_) | Expr::Constant(_)
    )
}

/// Return true when an expression is a binary operation with boolean output.
fn is_boolean_binary_expr(expr: &Expr) -> bool {
    let Expr::Binary(op, _, _) = expr else {
        return false;
    };
    matches!(
        op,
        BinOp::Eq
            | BinOp::Neq
            | BinOp::Lt
            | BinOp::Lte
            | BinOp::Gt
            | BinOp::Gte
            | BinOp::U32Lt
            | BinOp::U32Lte
            | BinOp::U32Gt
            | BinOp::U32Gte
    )
}

/// Return the formatter access path for a memory access kind.
fn mem_access_name(kind: MemAccessKind) -> &'static str {
    match kind {
        MemAccessKind::Element => "memory",
        MemAccessKind::WordBe => "memory.be",
        MemAccessKind::WordLe => "memory.le",
    }
}

/// Return the formatter access path for a local access kind.
fn local_access_name(kind: LocalAccessKind) -> &'static str {
    match kind {
        LocalAccessKind::Element => "locals",
        LocalAccessKind::WordBe => "locals.be",
        LocalAccessKind::WordLe => "locals.le",
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
