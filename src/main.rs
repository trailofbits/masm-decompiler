use std::path::PathBuf;

use clap::Parser;
use miden_decompiler::{
    analysis::{build_def_use_map, eliminate_dead_code, propagate_expressions},
    callgraph::CallGraph,
    cfg::build_cfg_for_proc,
    frontend::{LibraryRoot, Workspace},
    signature::infer_signatures,
    ssa::{lower::lower_cfg_to_ssa, out_of_ssa::transform_out_of_ssa},
    structuring::structure,
    fmt::CodeWriter,
};

#[derive(Parser, Debug)]
#[command(name = "miden-decompiler", version, about = "Decompile Miden Assembly modules")]
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

    println!("Loaded {proc_count} procedures from {}", cli.input.to_string_lossy());
    println!("Call graph nodes: {}", callgraph.nodes.len());
    println!("Signatures inferred: {}", signatures.signatures.len());

    // TODO: wire proc selection; for now lower all
    for module in workspace.modules() {
        for proc in module.procedures() {
            let cfg = build_cfg_for_proc(proc).map_err(|e| format!("{e:?}"))?;
            let lowered = lower_cfg_to_ssa(cfg, &module.module_path().to_string(), &signatures);
            let mut cfg = lowered.cfg;
            let mut def_use = build_def_use_map(&cfg);
            propagate_expressions(&mut cfg, &mut def_use);
            eliminate_dead_code(&mut cfg, &mut def_use);
            transform_out_of_ssa(&mut cfg);
            let structured = structure(cfg);
            if cli.show_graph {
                println!("CFG for {}::{}", module.module_path(), proc.name());
                let mut writer = CodeWriter::new();
                for stmt in &structured {
                    writer.write_stmt(stmt);
                }
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
