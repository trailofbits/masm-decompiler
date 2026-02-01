#![allow(dead_code)]

pub mod strategies;

use masm_decompiler::{
    cfg::Cfg,
    decompile::{DecompilationConfig, Decompiler},
    frontend::Workspace,
    ssa::Stmt,
};

// Re-export the new API types for test convenience
pub use masm_decompiler::decompile::{DecompiledModule, DecompiledProc};

/// Decompile a procedure with the default configuration (all optimizations enabled).
pub fn decompile(ws: &Workspace, proc_name: &str, _module: &str) -> Vec<Stmt> {
    let decompiler = Decompiler::new(ws);
    decompiler
        .decompile_proc(proc_name)
        .expect("decompilation should succeed")
        .body
        .stmts
        .clone()
}

/// Decompile a procedure with custom configuration.
pub fn decompile_with_config(
    ws: &Workspace,
    proc_name: &str,
    config: DecompilationConfig,
) -> Vec<Stmt> {
    let decompiler = Decompiler::new(ws).with_config(config);
    decompiler
        .decompile_proc(proc_name)
        .expect("decompilation should succeed")
        .body
        .stmts
        .clone()
}

/// Decompile a procedure without expression propagation (for debugging).
pub fn decompile_no_propagation(ws: &Workspace, proc_name: &str, _module: &str) -> Vec<Stmt> {
    let config = DecompilationConfig::default().with_expression_propagation(false);
    let decompiler = Decompiler::new(ws).with_config(config);
    decompiler
        .decompile_proc(proc_name)
        .expect("decompilation should succeed")
        .body
        .stmts
        .clone()
}

/// Decompile with no optimizations at all.
pub fn decompile_no_optimizations(ws: &Workspace, proc_name: &str) -> Vec<Stmt> {
    let decompiler = Decompiler::new(ws).with_config(DecompilationConfig::no_optimizations());
    decompiler
        .decompile_proc(proc_name)
        .expect("decompilation should succeed")
        .body
        .stmts
        .clone()
}

/// Decompile a procedure and print debug info about var_depths and loop_contexts.
pub fn run_structure_debug(ws: &Workspace, proc_name: &str, _module: &str) -> Vec<Stmt> {
    // For debug purposes, we need access to the raw CFG
    // Use the low-level API to print debug info
    use masm_decompiler::{
        analysis::{build_def_use_map, eliminate_dead_code, propagate_expressions},
        callgraph::CallGraph,
        cfg::build_cfg_for_proc,
        signature::infer_signatures,
        ssa::lift::lift_cfg_to_ssa,
        structuring::structure,
    };

    let cg = CallGraph::from(ws);
    let sigs = infer_signatures(ws, &cg);
    let proc = ws.lookup_proc(proc_name).expect("lookup should succeed");
    let cfg = build_cfg_for_proc(proc).expect("cfg build should succeed");
    let module_path = proc_name.rsplit_once("::").map(|(m, _)| m).unwrap_or("");
    let mut ssa =
        lift_cfg_to_ssa(cfg, module_path, proc_name, &sigs).expect("ssa lift should succeed");

    eprintln!("var_depths: {:?}", ssa.var_depths);
    eprintln!("loop_contexts: {:?}", ssa.loop_contexts);

    let mut def_use = build_def_use_map(&ssa);
    propagate_expressions(&mut ssa, &mut def_use);
    eliminate_dead_code(&mut ssa, &mut def_use);
    structure(ssa, true).stmts
}

// Legacy aliases for backward compatibility
pub fn run_structure(ws: &Workspace, proc_name: &str, module: &str) -> Vec<Stmt> {
    decompile(ws, proc_name, module)
}

/// Get raw SSA CFG for debugging (low-level API).
pub fn get_raw_ssa_cfg(ws: &Workspace, proc_name: &str, _module: &str) -> Cfg {
    use masm_decompiler::{
        callgraph::CallGraph, cfg::build_cfg_for_proc, signature::infer_signatures,
        ssa::lift::lift_cfg_to_ssa,
    };

    let cg = CallGraph::from(ws);
    let sigs = infer_signatures(ws, &cg);
    let proc = ws.lookup_proc(proc_name).expect("lookup should succeed");
    let cfg = build_cfg_for_proc(proc).expect("cfg build should succeed");
    let module_path = proc_name.rsplit_once("::").map(|(m, _)| m).unwrap_or("");
    lift_cfg_to_ssa(cfg, module_path, proc_name, &sigs).expect("ssa lift should succeed")
}
