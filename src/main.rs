use std::path::PathBuf;

use clap::Parser;
use log::{error, info};
use masm_decompiler::{
    decompile::{DecompilationConfig, Decompiler},
    frontend::{LibraryRoot, Workspace},
};

#[derive(Parser, Debug)]
#[command(
    name = "masm-decompiler",
    version,
    about = "Decompile a Miden assembly module"
)]
struct Cli {
    /// Path to a MASM source file
    input: PathBuf,

    /// Only decompile a single procedure by name
    #[arg(long)]
    procedure: Option<String>,

    /// Disable expression propagation optimization
    #[arg(long)]
    no_propagation: bool,

    /// Disable dead code elimination optimization
    #[arg(long)]
    no_dce: bool,

    /// Disable simplification passes
    #[arg(long)]
    no_simplification: bool,

    /// Register an additional library root: <namespace>:<path>
    #[arg(long = "library", value_parser = parse_library_spec)]
    libraries: Vec<LibraryRoot>,

    /// Disable colored output for decompiled code
    #[arg(long)]
    no_color: bool,
}

fn main() {
    lovely_env_logger::init_default();

    let cli = Cli::parse();

    // Configure syntax highlighting (separate from log coloring)
    if cli.no_color {
        yansi::disable();
    }

    if let Err(err) = run(cli) {
        error!("Error: {}", err);
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

    // Build config from CLI flags
    let config = DecompilationConfig::default()
        .with_expression_propagation(!cli.no_propagation)
        .with_dead_code_elimination(!cli.no_dce)
        .with_simplification(!cli.no_simplification);

    // Create decompiler with config
    let decompiler = Decompiler::new(&workspace).with_config(config);

    info!(
        "Loaded {proc_count} procedures from `{}`",
        cli.input.to_string_lossy()
    );
    info!(
        "{}-node call graph generated",
        decompiler.callgraph().nodes.len()
    );
    info!(
        "{} procedure signatures inferred",
        decompiler.signatures().len()
    );

    let target_proc = cli.procedure.as_deref();

    for module in workspace.modules() {
        for proc in module.procedures() {
            let proc_name = proc.name().to_string();
            if let Some(target) = target_proc {
                if proc_name != target {
                    continue;
                }
            }

            let fq = format!("{}::{}", module.module_path(), proc.name());
            match decompiler.decompile_proc(&fq) {
                Ok(decompiled) => println!("{decompiled}"),
                Err(error) => error!("Error: {error}"),
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
