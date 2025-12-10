use miden_decompiler::{
    callgraph::CallGraph, frontend::testing::workspace_from_modules, signature::infer_signatures,
    ssa::Stmt, ssa::lower::lower_proc_to_ssa,
};

#[test]
fn lowers_mapped_instructions_without_unknown() {
    // Exercise a curated set of mapped instructions; expect no Unknown statements.
    let ws = workspace_from_modules(&[(
        "mapped",
        r#"
        proc mapped
            # Stack operations
            push.1
            dup.1
            swap
            swap.1
            movup.2
            movup.3
            movupw.2
            movupw.3
            movdn.2
            movdn.4
            movdnw.2
            movdnw.3
            drop
            dropw
            padw
            
            # Arithmetic and logical operations
            add
            add.1
            sub
            sub.2
            mul
            mul.3
            div
            div.4
            not
            neg
            eq
            eq.0
            neq
            neq.1
            lt
            lt.2
            gt
            gt.3
            and
            or
            xor
            
            # Advice stack operations
            adv_push.1
            adv_loadw
            adv.push_mapval
            
            # Memory operations
            mem_load
            mem_load.2
            mem_loadw_be
            mem_loadw_be.3
            mem_loadw_le
            mem_loadw_le.4
            mem_store
            mem_store.1
            mem_storew_be
            mem_storew_be.2
            mem_storew_le
            mem_storew_le.3
            mem_stream
            
            # Local operations
            loc_load.1
            loc_loadw_be.2
            loc_loadw_le.3
            loc_store.1
            loc_storew_be.2
            loc_storew_le.3
            
            # Assertions
            assertz
            assert_eq
            u32assert
            u32assert2

            # U32 operations
            u32overflowing_add
            u32overflowing_sub
            u32overflowing_mul
            u32overflowing_madd
            u32split
            u32and

            # Cryptographic operations
            hash
            hperm
            hmerge
            mtree_get
            mtree_verify
            horner_eval_base
            horner_eval_ext
            log_precompile
            fri_ext2fold4
        end
        "#,
    )]);
    let cg = CallGraph::build_for_workspace(&ws);
    let sigs = infer_signatures(&ws, &cg);
    let proc = ws.lookup_proc("mapped::mapped").expect("proc");
    let res = lower_proc_to_ssa(proc, "mapped", &sigs);
    assert!(
        res.code.iter().all(|s| !matches!(s, Stmt::Unknown)),
        "unexpected unknowns: {:?}",
        res.code
    );
}
