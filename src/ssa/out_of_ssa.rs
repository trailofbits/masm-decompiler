use crate::{cfg::Cfg, ssa::{Expr, Stmt}};

/// Remove SSA-specific constructs (phi nodes, subscripts) to produce a simpler IR suitable
/// for structuring/pretty-printing.
pub fn transform_out_of_ssa(cfg: &mut Cfg) {
    for block in cfg.nodes.iter_mut() {
        // Drop nop statements but keep phi so loop-carried structure survives.
        block.code.retain(|stmt| !matches!(stmt, Stmt::Nop));

        for stmt in block.code.iter_mut() {
            strip_stmt(stmt);
        }
    }
}

fn strip_stmt(stmt: &mut Stmt) {
    match stmt {
        Stmt::Assign { dst, expr } => {
            dst.subscript = 0;
            strip_expr(expr);
        }
        Stmt::Expr(expr) | Stmt::Branch(expr) => strip_expr(expr),
        Stmt::If { cond, then_body, else_body } => {
            strip_expr(cond);
            for s in then_body.iter_mut().chain(else_body.iter_mut()) {
                strip_stmt(s);
            }
        }
        Stmt::Switch { expr, cases, default } => {
            strip_expr(expr);
            for (_, body) in cases {
                for s in body.iter_mut() {
                    strip_stmt(s);
                }
            }
            for s in default.iter_mut() {
                strip_stmt(s);
            }
        }
        Stmt::While { cond, body } => {
            strip_expr(cond);
            for s in body.iter_mut() {
                strip_stmt(s);
            }
        }
        Stmt::Phi { var, sources } => {
            var.subscript = 0;
            for s in sources.iter_mut() {
                s.subscript = 0;
            }
        }
        Stmt::Break | Stmt::Continue => {}
        Stmt::StackOp(op) => {
            for v in op.pops.iter_mut().chain(op.pushes.iter_mut()) {
                v.subscript = 0;
            }
        }
        Stmt::Instr(_) | Stmt::Unknown => {}
        Stmt::Nop => {}
    }
}

fn strip_expr(expr: &mut Expr) {
    match expr {
        Expr::Var(v) => v.subscript = 0,
        Expr::BinOp(_, a, b) => {
            strip_expr(a);
            strip_expr(b);
        }
        Expr::Unary(_, a) => strip_expr(a),
        Expr::Constant(_) | Expr::True | Expr::Unknown => {}
    }
}
