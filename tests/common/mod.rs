#![allow(dead_code)]

pub mod strategies;

use masm_decompiler::{
    analysis::{build_def_use_map, eliminate_dead_code, propagate_expressions},
    callgraph::CallGraph,
    cfg::{Cfg, build_cfg_for_proc},
    frontend::Workspace,
    signature::infer_signatures,
    ssa::{Stmt, lift::lift_cfg_to_ssa},
    structuring::structure,
};

pub fn lift_to_ssa(ws: &Workspace, proc_name: &str, module: &str) -> Cfg {
    let cg = CallGraph::from(ws);
    let sigs = infer_signatures(ws, &cg);
    let proc = ws.lookup_proc(proc_name).expect("lookup should succeed");
    let cfg = build_cfg_for_proc(proc).expect("cfg build should succeed");
    lift_cfg_to_ssa(cfg, module, proc_name, &sigs).expect("ssa lift should succeed")
}

pub fn run_structure(ws: &Workspace, proc_name: &str, module: &str) -> Vec<Stmt> {
    let mut cfg = lift_to_ssa(ws, proc_name, module);
    let mut def_use = build_def_use_map(&cfg);
    propagate_expressions(&mut cfg, &mut def_use);
    eliminate_dead_code(&mut cfg, &mut def_use);
    structure(cfg)
}

pub fn decompile(ws: &Workspace, proc_name: &str, module: &str) -> Vec<Stmt> {
    run_structure(ws, proc_name, module)
}
