use std::path::PathBuf;

use clap::Parser;
use masm_decompiler::{
    analysis::{build_def_use_map, eliminate_dead_code, propagate_expressions},
    callgraph::CallGraph,
    cfg::build_cfg_for_proc,
    fmt::CodeWriter,
    frontend::{LibraryRoot, Workspace},
    signature::{infer_signatures, ProcSignature},
    ssa::lift::lift_cfg_to_ssa,
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

    let callgraph = CallGraph::from(&workspace);
    let signatures = infer_signatures(&workspace, &callgraph);
    let target_proc = cli.procedure.as_deref();

    println!(
        "Loaded {proc_count} procedures from {}",
        cli.input.to_string_lossy()
    );
    println!("Call graph nodes: {}", callgraph.nodes.len());
    println!("Signatures inferred: {}", signatures.len());

    // TODO: wire proc selection; for now lift all
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
            let (sig_inputs, sig_outputs) = match signatures.get(&fq) {
                Some(ProcSignature::Known { inputs, outputs, .. }) => (*inputs, Some(*outputs)),
                _ => (0, None),
            };
            let mut ssa = lift_cfg_to_ssa(cfg, &module.module_path().to_string(), &fq, &signatures)
                .map_err(|e| format!("{e:?}"))?;
            let mut def_use = build_def_use_map(&ssa);
            propagate_expressions(&mut ssa, &mut def_use);
            eliminate_dead_code(&mut ssa, &mut def_use);
            let mut structured = structure(ssa);
            append_return(&mut structured, sig_outputs);
            if cli.show_graph {
                println!("CFG for {}::{}", module.module_path(), proc.name());
                let mut writer = CodeWriter::new();
                let ret_vars = find_return_vars(&structured);
                let header = build_header(
                    proc_name,
                    sig_inputs,
                    ret_vars.as_deref(),
                    sig_outputs,
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
    inputs: usize,
    outputs: Option<&[masm_decompiler::ssa::Var]>,
    inferred: Option<usize>,
    names: &CodeWriter,
) -> String {
    let mut args = Vec::new();
    for i in 0..inputs {
        let v = masm_decompiler::ssa::Var::new(i);
        args.push(names.fmt_var(&v));
    }
    let arg_list = args.join(", ");
    let ret_list = match outputs {
        None => {
            if let Some(n) = inferred {
                if n == 0 {
                    String::new()
                } else if n == 1 {
                    let v = masm_decompiler::ssa::Var::new(0);
                    format!(" -> {}", names.fmt_var(&v))
                } else {
                    let mut parts = Vec::new();
                    for i in 0..n {
                        let v = masm_decompiler::ssa::Var::new(i);
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

fn append_return(code: &mut Vec<masm_decompiler::ssa::Stmt>, outputs: Option<usize>) {
    let Some(count) = outputs else { return };
    if let Some(outs) = simulate_linear_stack(code, count) {
        code.push(masm_decompiler::ssa::Stmt::Return(outs));
    }
}

fn simulate_linear_stack(
    code: &[masm_decompiler::ssa::Stmt],
    outputs: usize,
) -> Option<Vec<masm_decompiler::ssa::Var>> {
    use masm_decompiler::ssa::Stmt::*;
    let mut stack: Vec<masm_decompiler::ssa::Var> = Vec::new();
    for stmt in code {
        match stmt {
            MemLoad(load) => {
                if load.address.len() > stack.len() {
                    return None;
                }
                for _ in 0..load.address.len() {
                    stack.pop();
                }
                for v in &load.outputs {
                    stack.push(v.clone());
                }
            }
            MemStore(store) => {
                let pops = store.address.len() + store.values.len();
                if pops > stack.len() {
                    return None;
                }
                for _ in 0..pops {
                    stack.pop();
                }
            }
            AdvLoad(load) => {
                for v in &load.outputs {
                    stack.push(v.clone());
                }
            }
            AdvStore(store) => {
                if store.values.len() > stack.len() {
                    return None;
                }
                for _ in 0..store.values.len() {
                    stack.pop();
                }
            }
            LocalLoad(load) => {
                for v in &load.outputs {
                    stack.push(v.clone());
                }
            }
            LocalStore(store) => {
                if store.values.len() > stack.len() {
                    return None;
                }
                for _ in 0..store.values.len() {
                    stack.pop();
                }
            }
            Call(call) | Exec(call) | SysCall(call) => {
                if call.args.len() > stack.len() {
                    return None;
                }
                for _ in 0..call.args.len() {
                    stack.pop();
                }
                for v in &call.results {
                    stack.push(v.clone());
                }
            }
            DynCall { args, results } => {
                if args.len() > stack.len() {
                    return None;
                }
                for _ in 0..args.len() {
                    stack.pop();
                }
                for v in results {
                    stack.push(v.clone());
                }
            }
            Intrinsic(intr) => {
                if intr.args.len() > stack.len() {
                    return None;
                }
                for _ in 0..intr.args.len() {
                    stack.pop();
                }
                for v in &intr.results {
                    stack.push(v.clone());
                }
            }
            Return(vals) => return Some(vals.clone()),
            If { .. }
            | While { .. }
            | Repeat { .. }
            | Phi { .. }
            | Branch(_)
            | Break
            | Continue
            | Inst(_)
            | Nop
            => return None,
            Assign { .. } => {}
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
