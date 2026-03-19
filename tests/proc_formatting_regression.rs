use masm_decompiler::{
    decompile::{DecompiledBody, DecompiledProc},
    fmt::FormattingConfig,
    ir::{Expr, MemAccessKind, MemLoad, Stmt, ValueId, Var},
    signature::ProcSignature,
};
use miden_assembly_syntax::debuginfo::SourceSpan;

const TEST_SPAN: SourceSpan = SourceSpan::UNKNOWN;

/// Render a decompiled procedure through the public rendering API.
fn render_proc(proc: &DecompiledProc) -> String {
    proc.render(FormattingConfig::new().with_color(false))
}

/// Build a procedure whose input names collide with later SSA values unless
/// full-procedure formatting assigns canonical names up front.
fn proc_with_colliding_names() -> DecompiledProc {
    let inputs: Vec<Var> = (0..12)
        .map(|i| Var::new(ValueId::new(i), i as usize))
        .collect();

    let first_load_outputs = vec![
        Var::new(ValueId::new(100), 7),
        Var::new(ValueId::new(101), 8),
        Var::new(ValueId::new(102), 9),
        Var::new(ValueId::new(103), 10),
    ];
    let second_load_outputs = vec![
        Var::new(ValueId::new(104), 10),
        Var::new(ValueId::new(105), 11),
        Var::new(ValueId::new(106), 12),
        Var::new(ValueId::new(107), 13),
    ];

    DecompiledProc {
        name: "test::colliding_names".to_string(),
        module_path: "test".to_string(),
        signature: Some(ProcSignature::known(12, 0, 0)),
        type_summary: None,
        body: DecompiledBody::new(vec![
            Stmt::Assign {
                span: TEST_SPAN,
                dest: Var::new(ValueId::new(200), 20),
                expr: Expr::Var(inputs[7].clone()),
            },
            Stmt::Assign {
                span: TEST_SPAN,
                dest: Var::new(ValueId::new(201), 21),
                expr: Expr::Var(inputs[8].clone()),
            },
            Stmt::Assign {
                span: TEST_SPAN,
                dest: Var::new(ValueId::new(202), 22),
                expr: Expr::Var(inputs[9].clone()),
            },
            Stmt::MemLoad {
                span: TEST_SPAN,
                load: MemLoad {
                    kind: MemAccessKind::WordBe,
                    address: vec![inputs[10].clone()],
                    outputs: first_load_outputs,
                },
            },
            Stmt::MemLoad {
                span: TEST_SPAN,
                load: MemLoad {
                    kind: MemAccessKind::WordBe,
                    address: vec![inputs[11].clone()],
                    outputs: second_load_outputs,
                },
            },
        ]),
    }
}

#[test]
fn configurable_rendering_matches_display_path() {
    let proc = proc_with_colliding_names();

    let via_writer = render_proc(&proc);
    let via_display = format!("{proc}");

    assert_eq!(via_writer, via_display);
    assert!(
        via_writer.contains("(v_7_1, v_8_1, v_9_1, v_10_1) = memory.be[v_10];"),
        "{via_writer}"
    );
    assert!(
        via_writer.contains("(v_10_2, v_11_1, v_12, v_13) = memory.be[v_11];"),
        "{via_writer}"
    );
    assert!(
        !via_writer.contains("(v_7, v_8, v_9, v_10) = memory.be[v_10];"),
        "{via_writer}"
    );
    assert!(
        !via_writer.contains("(v_10, v_11, v_12, v_13) = memory.be[v_11];"),
        "{via_writer}"
    );
}
