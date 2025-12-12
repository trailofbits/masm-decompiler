use std::path::PathBuf;

use clap::Parser;
use masm_decompiler::{
    analysis::{
        IndexExpr, build_def_use_map, compute_loop_indices, eliminate_dead_code,
        propagate_expressions,
    },
    callgraph::CallGraph,
    cfg::build_cfg_for_proc,
    fmt::CodeWriter,
    frontend::{LibraryRoot, Workspace},
    signature::infer_signatures,
    ssa::{lower::lower_cfg_to_ssa, out_of_ssa::transform_out_of_ssa},
    structuring::structure,
};

#[derive(Parser, Debug)]
#[command(
    name = "miden-decompiler",
    version,
    about = "Decompile Miden Assembly modules"
)]
struct Cli {
    /// Path to a MASM source file
    input: PathBuf,

    /// Only decompile a single procedure by name
    #[arg(long)]
    procedure: Option<String>,

    /// Emit the CFG in DOT format before structuring
    #[arg(long)]
    show_graph: bool,

    /// Register an additional library root: <namespace>:<path>
    #[arg(long = "library", value_parser = parse_library_spec)]
    libraries: Vec<LibraryRoot>,
}

fn main() {
    let cli = Cli::parse();
    if let Err(err) = run(cli) {
        eprintln!("{err}");
        std::process::exit(1);
    }
}

fn run(cli: Cli) -> Result<(), String> {
    let mut roots = cli.libraries.clone();
    // Always include the workspace root (empty namespace)
    let cwd = std::env::current_dir().map_err(|e| e.to_string())?;
    roots.push(LibraryRoot::new("", cwd));

    let mut workspace = Workspace::new(roots);
    workspace.load_entry(&cli.input)?;
    workspace.load_dependencies();
    let proc_count: usize = workspace.modules().map(|m| m.procedures().count()).sum();

    let callgraph = CallGraph::build_for_workspace(&workspace);
    let signatures = infer_signatures(&workspace, &callgraph);
    let target_proc = cli.procedure.as_deref();

    println!(
        "Loaded {proc_count} procedures from {}",
        cli.input.to_string_lossy()
    );
    println!("Call graph nodes: {}", callgraph.nodes.len());
    println!("Signatures inferred: {}", signatures.signatures.len());

    // TODO: wire proc selection; for now lower all
    for module in workspace.modules() {
        for proc in module.procedures() {
            if let Some(target) = target_proc {
                if proc.name().to_string() != target {
                    continue;
                }
            }
            let cfg = build_cfg_for_proc(proc).map_err(|e| format!("{e:?}"))?;
            let proc_name = proc.name().to_string();
            let fq = format!("{}::{}", module.module_path(), proc.name());
            let lowered =
                lower_cfg_to_ssa(cfg, &module.module_path().to_string(), &fq, &signatures);
            let mut cfg = lowered.cfg;
            let mut def_use = build_def_use_map(&cfg);
            propagate_expressions(&mut cfg, &mut def_use);
            eliminate_dead_code(&mut cfg, &mut def_use);
            transform_out_of_ssa(&mut cfg);
            let mut structured = structure(cfg);
            append_return(&mut structured, lowered.outputs);
            if cli.show_graph {
                println!("CFG for {}::{}", module.module_path(), proc.name());
                let name_map = build_var_name_map(&structured);
                let mut writer = if name_map.is_empty() {
                    CodeWriter::new()
                } else {
                    CodeWriter::with_var_names(name_map)
                };
                let ret_vars = find_return_vars(&structured);
                let header = build_header(
                    proc_name,
                    lowered.inputs,
                    ret_vars.as_deref(),
                    lowered.outputs,
                    &writer,
                );
                writer.write_line(&header);
                writer.indent();
                for stmt in &structured {
                    writer.write(stmt.clone());
                }
                writer.dedent();
                writer.write_line("}");
                println!("{}", writer.finish());
            }
        }
    }

    Ok(())
}

fn parse_library_spec(spec: &str) -> Result<LibraryRoot, String> {
    let (ns, path) = spec
        .split_once(':')
        .ok_or_else(|| "library spec must be <namespace>:<path>".to_string())?;
    if path.is_empty() {
        return Err("library path cannot be empty".to_string());
    }
    let pb = PathBuf::from(path);
    Ok(LibraryRoot::new(ns, pb))
}

fn build_header(
    proc_name: String,
    inputs: u32,
    outputs: Option<&[masm_decompiler::ssa::Var]>,
    inferred: Option<u32>,
    names: &CodeWriter,
) -> String {
    let mut args = Vec::new();
    for i in 0..inputs {
        let v = masm_decompiler::ssa::Var::no_sub(i);
        args.push(names.fmt_var(&v));
    }
    let arg_list = args.join(", ");
    let ret_list = match outputs {
        None => {
            if let Some(n) = inferred {
                if n == 0 {
                    String::new()
                } else if n == 1 {
                    let v = masm_decompiler::ssa::Var::no_sub(0);
                    format!(" -> {}", names.fmt_var(&v))
                } else {
                    let mut parts = Vec::new();
                    for i in 0..n {
                        let v = masm_decompiler::ssa::Var::no_sub(i);
                        parts.push(names.fmt_var(&v));
                    }
                    format!(" -> ({})", parts.join(", "))
                }
            } else {
                String::new()
            }
        }
        Some(vars) if vars.is_empty() => String::new(),
        Some(vars) if vars.len() == 1 => format!(" -> {}", names.fmt_var(&vars[0])),
        Some(vars) => {
            let parts = vars
                .iter()
                .map(|v| names.fmt_var(v))
                .collect::<Vec<_>>()
                .join(", ");
            format!(" -> ({parts})")
        }
    };
    format!("proc {}({}){} {{", proc_name, arg_list, ret_list)
}

fn build_loop_var_names(
    structured: &[masm_decompiler::ssa::Stmt],
) -> std::collections::HashMap<masm_decompiler::ssa::Var, String> {
    let mut map = std::collections::HashMap::new();
    let idx_map = compute_loop_indices(structured);
    for (var, idx) in idx_map {
        if let IndexExpr::Affine {
            base,
            stride,
            counter,
        } = idx
        {
            let counter_name = CodeWriter::new().fmt_var(&counter);
            let stride_part = if stride == 1 {
                counter_name.clone()
            } else {
                format!("{stride}*{counter_name}")
            };
            let name = if base == 0 {
                format!("v_({stride_part})")
            } else if base > 0 {
                format!("v_({stride_part} + {base})")
            } else {
                format!("v_({stride_part} - {})", -base)
            };
            map.insert(var, name);
        }
    }
    map
}

fn build_var_name_map(
    structured: &[masm_decompiler::ssa::Stmt],
) -> std::collections::HashMap<masm_decompiler::ssa::Var, String> {
    let mut map = std::collections::HashMap::new();
    map.extend(build_loop_var_names(structured));
    map
}

fn append_return(code: &mut Vec<masm_decompiler::ssa::Stmt>, outputs: Option<u32>) {
    let Some(count) = outputs else { return };
    if let Some(outs) = simulate_linear_stack(code, count) {
        code.push(masm_decompiler::ssa::Stmt::Return(outs));
    }
}

fn simulate_linear_stack(
    code: &[masm_decompiler::ssa::Stmt],
    outputs: u32,
) -> Option<Vec<masm_decompiler::ssa::Var>> {
    use masm_decompiler::ssa::Stmt::*;
    let mut stack: Vec<masm_decompiler::ssa::Var> = Vec::new();
    for stmt in code {
        match stmt {
            StackOp(op) => {
                if op.pops.len() > stack.len() {
                    return None;
                }
                for _ in 0..op.pops.len() {
                    stack.pop();
                }
                for v in &op.pushes {
                    stack.push(*v);
                }
            }
            Return(vals) => return Some(vals.clone()),
            If { .. }
            | Switch { .. }
            | While { .. }
            | For { .. }
            | RepeatInit { .. }
            | RepeatCond { .. }
            | RepeatStep { .. } => return None,
            _ => {}
        }
    }
    if stack.len() < outputs as usize {
        return None;
    }
    let outs = stack.split_off(stack.len() - outputs as usize);
    Some(outs)
}

fn find_return_vars(code: &[masm_decompiler::ssa::Stmt]) -> Option<Vec<masm_decompiler::ssa::Var>> {
    for stmt in code {
        if let masm_decompiler::ssa::Stmt::Return(vals) = stmt {
            return Some(vals.clone());
        }
    }
    None
}
