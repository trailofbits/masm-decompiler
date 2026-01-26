use masm_decompiler::{
    cfg::{Edge, build_cfg_for_proc},
    frontend::testing::workspace_from_modules,
};

#[test]
fn builds_linear_cfg() {
    let ws = workspace_from_modules(&[(
        "linear",
        r#"
        proc linear
            push.1
            drop
        end
        "#,
    )]);
    let proc = ws.lookup_proc("linear::linear").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    assert_eq!(cfg.nodes.len(), 1);
    assert_eq!(cfg.nodes[0].code.len(), 2);
    assert!(cfg.nodes[0].next.is_empty());
}

#[test]
fn builds_if_cfg() {
    let ws = workspace_from_modules(&[(
        "branch",
        r#"
        proc branch
            push.1
            if.true
                push.2
            else
                push.3
            end
        end
        "#,
    )]);
    let proc = ws.lookup_proc("branch::branch").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    assert_eq!(cfg.nodes.len(), 5);
    // Entry block has condition push and an unconditional edge to the header.
    assert_eq!(cfg.nodes[0].code.len(), 1);
    assert_eq!(cfg.nodes[0].next.len(), 1);
    assert!(matches!(cfg.nodes[0].next[0], Edge::Unconditional { .. }));
    // Header block has two outgoing conditional edges.
    assert_eq!(cfg.nodes[1].next.len(), 2);
    assert!(matches!(cfg.nodes[1].next[0], Edge::Conditional { .. }));
    assert!(matches!(cfg.nodes[1].next[1], Edge::Conditional { .. }));
    // Join block should have two predecessors
    assert_eq!(cfg.nodes[4].prev.len(), 2);
}

#[test]
fn builds_while_cfg() {
    let ws = workspace_from_modules(&[(
        "loop",
        r#"
        proc loop
            push.1
            while.true
                push.2
            end
        end
        "#,
    )]);
    let proc = ws.lookup_proc("loop::loop").expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    // entry, header, body, exit
    assert_eq!(cfg.nodes.len(), 4);
    // entry has one successor (loop header)
    assert_eq!(cfg.nodes[0].next.len(), 1);
    assert!(matches!(cfg.nodes[0].next[0], Edge::Unconditional { .. }));
    // header has two conditional successors
    assert_eq!(cfg.nodes[1].next.len(), 2);
    // body has back edge to header
    assert_eq!(cfg.nodes[2].next.len(), 1);
    assert!(cfg.nodes[2].next[0].back_edge());
    assert_eq!(cfg.nodes[2].next[0].node(), 1);
}
