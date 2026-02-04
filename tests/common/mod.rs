#![allow(dead_code)]

pub mod strategies;

use masm_decompiler::{
    decompile::{DecompilationConfig, Decompiler},
    frontend::Workspace,
    ir::Stmt,
};

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

// Legacy aliases for backward compatibility
pub fn run_structure(ws: &Workspace, proc_name: &str, module: &str) -> Vec<Stmt> {
    decompile(ws, proc_name, module)
}
