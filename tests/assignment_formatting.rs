use masm_decompiler::{
    fmt::{CodeWriter, FormattingConfig},
    ir::{BinOp, Constant, Expr, Stmt, ValueId, Var},
};
use miden_assembly_syntax::debuginfo::SourceSpan;

const TEST_SPAN: SourceSpan = SourceSpan::UNKNOWN;

fn format_stmt(stmt: Stmt) -> String {
    let mut writer = CodeWriter::with_config(FormattingConfig::new().with_color(false));
    writer.write(stmt);
    writer.finish()
}

#[test]
fn parenthesizes_boolean_binary_assignments() {
    let dest = Var::new(ValueId::new(0), 0);
    let lhs = Var::new(ValueId::new(1), 1);
    let rhs = Var::new(ValueId::new(2), 2);

    let eq_out = format_stmt(Stmt::Assign {
        span: TEST_SPAN,
        dest: dest.clone(),
        expr: Expr::Binary(
            BinOp::Eq,
            Box::new(Expr::Var(lhs.clone())),
            Box::new(Expr::Constant(Constant::Felt(0))),
        ),
    });
    assert_eq!(eq_out.trim(), "v_0 = (v_1 == 0);");

    let u32_cmp_out = format_stmt(Stmt::Assign {
        span: TEST_SPAN,
        dest,
        expr: Expr::Binary(
            BinOp::U32Lte,
            Box::new(Expr::Var(lhs)),
            Box::new(Expr::Var(rhs)),
        ),
    });
    assert_eq!(u32_cmp_out.trim(), "v_0 = (v_1 <=_u32 v_2);");
}

#[test]
fn does_not_parenthesize_boolean_literals() {
    let out = format_stmt(Stmt::Assign {
        span: TEST_SPAN,
        dest: Var::new(ValueId::new(3), 3),
        expr: Expr::True,
    });
    assert_eq!(out.trim(), "v_3 = true;");
}
