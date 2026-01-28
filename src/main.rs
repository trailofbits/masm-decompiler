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
            let structured = structure(ssa);
            if cli.show_graph {
                println!("CFG for {}::{}", module.module_path(), proc.name());
                let mut writer = CodeWriter::new();
                // Pre-register loop variables so subscripts format correctly.
                writer.register_loop_vars(structured.stmts());
                let ret_vars = find_return_vars(structured.stmts());
                let header = build_header(
                    proc_name,
                    sig_inputs,
                    ret_vars.as_deref(),
                    sig_outputs,
                    &writer,
                );
                writer.write_line(&header);
                writer.indent();
                for stmt in structured.stmts() {
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

    // Build return type list using types (Felt) instead of variable names.
    let output_count = match outputs {
        Some(vars) => vars.len(),
        None => inferred.unwrap_or(0),
    };

    let ret_list = match output_count {
        0 => String::new(),
        1 => " -> Felt".to_string(),
        n => {
            let types = (0..n).map(|_| "Felt").collect::<Vec<_>>().join(", ");
            format!(" -> ({})", types)
        }
    };

    format!("proc {}({}){} {{", proc_name, arg_list, ret_list)
}

fn find_return_vars(code: &[masm_decompiler::ssa::Stmt]) -> Option<Vec<masm_decompiler::ssa::Var>> {
    for stmt in code {
        if let masm_decompiler::ssa::Stmt::Return(vals) = stmt {
            return Some(vals.clone());
        }
    }
    None
}
