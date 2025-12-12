//! Pretty-printing helpers that emit a readable structured view of SSA statements and DOT CFGs.

use crate::{
    cfg::{Cfg, EdgeType},
    ssa::{
        AdvLoad, AdvStore, BinOp, Call, Constant, Expr, Intrinsic, LocalLoad, LocalStore, MemLoad,
        MemStore, Stmt, UnOp, Var,
    },
};
use miden_assembly_syntax::ast::Instruction;

/// Trait for rendering IR nodes with indentation-aware `CodeWriter`.
pub trait CodeDisplay {
    fn fmt_code(&self, f: &mut CodeWriter);
}

#[derive(Default)]
pub struct CodeWriter {
    output: String,
    indent: usize,
    var_names: std::collections::HashMap<Var, String>,
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
        if let Some(name) = self.var_names.get(v) {
            return name.clone();
        }
        let base = format!("v_{}", v.index);
        if v.subscript == 0 {
            base
        } else {
            format!("{}_{}", base, v.subscript)
        }
    }
}

impl CodeDisplay for Stmt {
    fn fmt_code(&self, f: &mut CodeWriter) {
        match self {
            Stmt::Assign { dst, expr } => {
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
            Stmt::Expr(expr) => {
                f.write_line(&format!("{};", fmt_expr(f, expr, 0)));
            }
            Stmt::StackOp(op) => {
                if let Some(rendered) = render_stack_op(op, f) {
                    f.write_line(&rendered);
                } else {
                    let pops = op
                        .pops
                        .iter()
                        .map(|v| f.fmt_var(v))
                        .collect::<Vec<_>>()
                        .join(", ");
                    let pushes = op
                        .pushes
                        .iter()
                        .map(|v| f.fmt_var(v))
                        .collect::<Vec<_>>()
                        .join(", ");
                    f.write_line(&format!(
                        "/* {:?} */  // pops [{pops}] pushes [{pushes}]",
                        op.inst
                    ));
                }
            }
            Stmt::MemLoad(MemLoad { address, outputs }) => {
                let args = address.iter().map(|v| f.fmt_var(v)).collect::<Vec<_>>().join(", ");
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
                let args = values.iter().map(|v| f.fmt_var(v)).collect::<Vec<_>>().join(", ");
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
                let args = values.iter().map(|v| f.fmt_var(v)).collect::<Vec<_>>().join(", ");
                f.write_line(&format!("loc_store.{index}({args});"));
            }
            Stmt::Call(call) => write_call_like("call", call, f),
            Stmt::Exec(call) => write_call_like("exec", call, f),
            Stmt::SysCall(call) => write_call_like("syscall", call, f),
            Stmt::DynCall { args, results } => {
                let args = args.iter().map(|v| f.fmt_var(v)).collect::<Vec<_>>().join(", ");
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
            Stmt::Intrinsic(Intrinsic { name, args, results }) => {
                let args = args.iter().map(|v| f.fmt_var(v)).collect::<Vec<_>>().join(", ");
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
            Stmt::Instr(inst) => {
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
            Stmt::Switch {
                expr,
                cases,
                default,
            } => {
                f.write_line(&format!("switch ({}) {{", fmt_expr(f, expr, 0)));
                f.indent();
                for (val, body) in cases {
                    f.write_line(&format!("case {}:", fmt_constant(val)));
                    f.indent();
                    f.write_block(body);
                    f.dedent();
                }
                if !default.is_empty() {
                    f.write_line("default:");
                    f.indent();
                    f.write_block(default);
                    f.dedent();
                }
                f.dedent();
                f.write_line("}");
            }
            Stmt::For {
                init,
                cond,
                step,
                body,
            } => {
                let init_line = single_line(init, f);
                let step_line = single_line(step, f);
                let init_line = init_line.trim_end_matches(';');
                let step_line = step_line.trim_end_matches(';');
                f.write_line(&format!(
                    "for ({}; {}; {}) {{",
                    init_line,
                    fmt_expr(f, cond, 0),
                    step_line
                ));
                f.indent();
                f.write_block(body);
                f.dedent();
                f.write_line("}");
            }
            Stmt::RepeatInit { local, count } => {
                f.write_line(&format!("/* repeat init l{local} = 0..{count} */"));
            }
            Stmt::RepeatCond { local, count } => {
                f.write_line(&format!("/* repeat cond l{local} < {count} */"));
            }
            Stmt::RepeatStep { local } => {
                f.write_line(&format!("/* repeat step l{local}++ */"));
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
            Stmt::Unknown => {
                f.write_line("/* unknown */");
            }
            Stmt::Nop => {}
            Stmt::Break => {
                f.write_line("break;");
            }
            Stmt::Continue => {
                f.write_line("continue;");
            }
        }
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
            out.push_str(&format!(
                "  n{idx} -> n{} [label=\"{}\"];\n",
                edge.node, label
            ));
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
        Expr::BinOp(op, a, b) => {
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

fn single_line(stmt: &Stmt, ctx: &CodeWriter) -> String {
    let mut w = if ctx.var_names.is_empty() {
        CodeWriter::new()
    } else {
        CodeWriter::with_var_names(ctx.clone_var_names())
    };
    stmt.fmt_code(&mut w);
    w.finish().replace('\n', " ").trim().to_string()
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

fn render_stack_op(op: &crate::ssa::StackOp, f: &CodeWriter) -> Option<String> {
    let pops: Vec<String> = op.pops.iter().map(|v| f.fmt_var(v)).collect();
    let pushes: Vec<String> = op.pushes.iter().map(|v| f.fmt_var(v)).collect();
    let render_call =
        |name: &str, args: Vec<String>, pushes: &[String]| -> Option<String> {
            let args = args.join(", ");
            let args = if args.is_empty() {
                "()".to_string()
            } else {
                format!("({args})")
            };
            Some(match pushes.len() {
                0 => format!("{name}{args};"),
                1 => format!("{} = {name}{args};", pushes[0]),
                2 => format!("{}, {} = {name}{args};", pushes[0], pushes[1]),
                _ => format!("{} = {name}{args};", pushes.join(", ")),
            })
        };
    let with_imm = |name: &str, imm: String| -> Option<String> {
        let mut args = pops.clone();
        args.push(imm);
        render_call(name, args, &pushes)
    };
    let simple = |name: &str| -> Option<String> {
        render_call(name, pops.clone(), &pushes)
    };
    match &op.inst {
        Instruction::U32WrappingAdd
        | Instruction::U32OverflowingAdd
        | Instruction::U32WrappingAdd3 => {
            return simple("u32_add");
        }
        Instruction::U32WrappingSub
        | Instruction::U32OverflowingSub => {
            return simple("u32_sub");
        }
        Instruction::U32WrappingMul
        | Instruction::U32OverflowingMul
        | Instruction::U32OverflowingMadd => {
            return simple("u32_mul");
        }
        Instruction::U32Div => {
            return simple("u32_div");
        }
        Instruction::U32Mod => {
            return simple("u32_mod");
        }
        Instruction::U32And => {
            return simple("u32_and");
        }
        Instruction::U32Or => {
            return simple("u32_or");
        }
        Instruction::U32Xor => {
            return simple("u32_xor");
        }
        Instruction::U32Not => {
            return simple("u32_not");
        }
        Instruction::U32Shr | Instruction::U32ShrImm(_) => {
            return simple("u32_shr");
        }
        Instruction::U32Shl | Instruction::U32ShlImm(_) => {
            return simple("u32_shl");
        }
        Instruction::U32Rotl | Instruction::U32RotlImm(_) => {
            return simple("u32_rotl");
        }
        Instruction::U32Rotr | Instruction::U32RotrImm(_) => {
            return simple("u32_rotr");
        }
        Instruction::U32Lt => {
            return simple("u32_lt");
        }
        Instruction::U32Lte => {
            return simple("u32_lte");
        }
        Instruction::U32Gt => {
            return simple("u32_gt");
        }
        Instruction::U32Gte => {
            return simple("u32_gte");
        }
        Instruction::U32Min => {
            return simple("u32_min");
        }
        Instruction::U32Max => {
            return simple("u32_max");
        }
        Instruction::U32WrappingAddImm(imm) | Instruction::U32OverflowingAddImm(imm) => {
            return with_imm("u32_add", imm.to_string());
        }
        Instruction::U32OverflowingAdd3 => {
            return simple("u32_add3");
        }
        Instruction::U32WrappingSubImm(imm) | Instruction::U32OverflowingSubImm(imm) => {
            return with_imm("u32_sub", imm.to_string());
        }
        Instruction::U32WrappingMulImm(imm) | Instruction::U32OverflowingMulImm(imm) => {
            return with_imm("u32_mul", imm.to_string());
        }
        Instruction::U32WrappingMadd => {
            return simple("u32_madd");
        }
        Instruction::U32DivImm(imm) => {
            return with_imm("u32_div", imm.to_string());
        }
        Instruction::U32ModImm(imm) => {
            return with_imm("u32_mod", imm.to_string());
        }
        Instruction::U32DivMod => {
            return render_call("u32_divmod", pops, &pushes);
        }
        Instruction::U32DivModImm(imm) => {
            let mut args = pops.clone();
            args.push(imm.to_string());
            return render_call("u32_divmod", args, &pushes);
        }
        Instruction::U32Split => {
            return render_call("u32_split", pops, &pushes);
        }
        Instruction::U32Test | Instruction::U32TestW => {
            return simple("u32_test");
        }
        Instruction::U32Assert
        | Instruction::U32AssertWithError(_)
        | Instruction::U32Assert2
        | Instruction::U32Assert2WithError(_)
        | Instruction::U32AssertW
        | Instruction::U32AssertWWithError(_) => {
            return simple("u32_assert");
        }
        Instruction::U32Cast => {
            return simple("u32_cast");
        }
        Instruction::U32Popcnt => {
            return simple("u32_popcnt");
        }
        Instruction::U32Ctz => {
            return simple("u32_ctz");
        }
        Instruction::U32Clz => {
            return simple("u32_clz");
        }
        Instruction::U32Clo => {
            return simple("u32_clo");
        }
        Instruction::U32Cto => {
            return simple("u32_cto");
        }
        Instruction::ILog2 => {
            return simple("ilog2");
        }
        Instruction::Inv => {
            return simple("inv");
        }
        Instruction::Incr => {
            return simple("incr");
        }
        Instruction::Pow2 => {
            return simple("pow2");
        }
        Instruction::Exp => {
            return simple("exp");
        }
        Instruction::ExpImm(imm) => {
            return with_imm("exp", imm.to_string());
        }
        Instruction::ExpBitLength(bits) => {
            return with_imm("exp_bits", bits.to_string());
        }
        Instruction::IsOdd => {
            return simple("is_odd");
        }
        Instruction::Ext2Add => {
            return simple("ext2_add");
        }
        Instruction::Ext2Sub => {
            return simple("ext2_sub");
        }
        Instruction::Ext2Mul => {
            return simple("ext2_mul");
        }
        Instruction::Ext2Div => {
            return simple("ext2_div");
        }
        Instruction::Ext2Neg => {
            return simple("ext2_neg");
        }
        Instruction::Ext2Inv => {
            return simple("ext2_inv");
        }
        Instruction::Exec(target) | Instruction::Call(target) | Instruction::SysCall(target) => {
            return render_call(&format!("call {target}"), pops, &pushes);
        }
        Instruction::MemLoad => {
            return render_call("mem_load", pops, &pushes);
        }
        Instruction::MemLoadImm(imm) => {
            return with_imm("mem_load", imm.to_string());
        }
        Instruction::MemLoadWBe => {
            return render_call("mem_loadw_be", pops, &pushes);
        }
        Instruction::MemLoadWBeImm(imm) => {
            return with_imm("mem_loadw_be", imm.to_string());
        }
        Instruction::MemLoadWLe => {
            return render_call("mem_loadw_le", pops, &pushes);
        }
        Instruction::MemLoadWLeImm(imm) => {
            return with_imm("mem_loadw_le", imm.to_string());
        }
        Instruction::LocLoad(imm) => {
            return with_imm("loc_load", imm.to_string());
        }
        Instruction::LocLoadWBe(imm) => {
            return with_imm("loc_loadw_be", imm.to_string());
        }
        Instruction::LocLoadWLe(imm) => {
            return with_imm("loc_loadw_le", imm.to_string());
        }
        Instruction::MemStore => {
            return render_call("mem_store", pops, &pushes);
        }
        Instruction::MemStoreImm(imm) => {
            return with_imm("mem_store", imm.to_string());
        }
        Instruction::MemStoreWBe => {
            return render_call("mem_storew_be", pops, &pushes);
        }
        Instruction::MemStoreWBeImm(imm) => {
            return with_imm("mem_storew_be", imm.to_string());
        }
        Instruction::MemStoreWLe => {
            return render_call("mem_storew_le", pops, &pushes);
        }
        Instruction::MemStoreWLeImm(imm) => {
            return with_imm("mem_storew_le", imm.to_string());
        }
        Instruction::LocStore(imm) => {
            return with_imm("loc_store", imm.to_string());
        }
        Instruction::LocStoreWBe(imm) => {
            return with_imm("loc_storew_be", imm.to_string());
        }
        Instruction::LocStoreWLe(imm) => {
            return with_imm("loc_storew_le", imm.to_string());
        }
        Instruction::MemStream => {
            return simple("mem_stream");
        }
        Instruction::AdvPush(imm) => {
            return with_imm("adv_push", imm.to_string());
        }
        Instruction::AdvLoadW => {
            return render_call("adv_loadw", pops, &pushes);
        }
        Instruction::AdvPipe => {
            return simple("adv_pipe");
        }
        Instruction::Hash => {
            return render_call("hash", pops, &pushes);
        }
        Instruction::HMerge => {
            return render_call("hmerge", pops, &pushes);
        }
        Instruction::HPerm => {
            return render_call("hperm", pops, &pushes);
        }
        Instruction::MTreeGet => {
            return render_call("mtree_get", pops, &pushes);
        }
        Instruction::MTreeSet => {
            return render_call("mtree_set", pops, &pushes);
        }
        Instruction::MTreeMerge => {
            return render_call("mtree_merge", pops, &pushes);
        }
        Instruction::MTreeVerify => {
            return render_call("mtree_verify", pops, &pushes);
        }
        Instruction::MTreeVerifyWithError(err) => {
            return with_imm("mtree_verify", err.to_string());
        }
        Instruction::CryptoStream => {
            return simple("crypto_stream");
        }
        Instruction::FriExt2Fold4 => {
            return simple("fri_ext2fold4");
        }
        Instruction::HornerBase => {
            return simple("horner_eval_base");
        }
        Instruction::HornerExt => {
            return simple("horner_eval_ext");
        }
        Instruction::LogPrecompile => {
            return simple("log_precompile");
        }
        Instruction::EvalCircuit => {
            return simple("eval_circuit");
        }
        Instruction::Emit => {
            return render_call("emit", pops, &pushes);
        }
        Instruction::EmitImm(imm) => {
            return with_imm("emit", imm.to_string());
        }
        Instruction::Trace(kind) => {
            return with_imm("trace", kind.to_string());
        }
        Instruction::SysEvent(event) => {
            return with_imm("sys_event", format!("{event:?}"));
        }
        _ => {}
    }
    None
}
