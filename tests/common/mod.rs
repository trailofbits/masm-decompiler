#![allow(dead_code)]

use masm_decompiler::{
    analysis::{build_def_use_map, eliminate_dead_code, propagate_expressions},
    callgraph::CallGraph,
    cfg::{Cfg, build_cfg_for_proc},
    frontend::Workspace,
    signature::infer_signatures,
    ssa::{Stmt, lower::lower_cfg_to_ssa, out_of_ssa::transform_out_of_ssa},
    structuring::structure,
};

pub fn lower_to_ssa(ws: &Workspace, proc_name: &str, module: &str) -> Cfg {
    let cg = CallGraph::build_for_workspace(ws);
    let sigs = infer_signatures(ws, &cg);
    let proc = ws.lookup_proc(proc_name).expect("proc");
    let cfg = build_cfg_for_proc(proc).expect("cfg");
    lower_cfg_to_ssa(cfg, module, proc_name, &sigs).cfg
}

pub fn run_structure(ws: &Workspace, proc_name: &str, module: &str) -> Vec<Stmt> {
    let mut cfg = lower_to_ssa(ws, proc_name, module);
    let mut def_use = build_def_use_map(&cfg);
    propagate_expressions(&mut cfg, &mut def_use);
    eliminate_dead_code(&mut cfg, &mut def_use);
    transform_out_of_ssa(&mut cfg);
    structure(cfg)
}

pub fn decompile(ws: &Workspace, proc_name: &str, module: &str) -> Vec<Stmt> {
    run_structure(ws, proc_name, module)
}
