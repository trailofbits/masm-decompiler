use std::collections::HashSet;
use std::path::{Path, PathBuf};

use clap::Parser;
use log::{error, info, warn};
use masm_decompiler::{
    decompile::{DecompilationConfig, Decompiler},
    fmt::FormattingConfig,
    frontend::{LibraryRoot, Workspace},
    symbol::path::SymbolPath,
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

    /// Register an additional library root: <namespace>=<path>
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
    let cwd = std::env::current_dir().map_err(|e| e.to_string())?;
    let entry_path = normalize_cli_path(&cli.input, &cwd);

    let mut roots = normalize_library_roots(&cli.libraries, &cwd);
    // Always include the workspace root (empty namespace).
    roots.push(LibraryRoot::new("", normalize_cli_path(&cwd, &cwd)));

    let mut workspace = Workspace::new(roots);
    workspace.load_entry(&entry_path)?;
    workspace.load_dependencies();
    emit_unresolved_dependency_warnings(&workspace);
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
        entry_path.to_string_lossy()
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
            if let Some(target) = target_proc
                && proc_name != target
            {
                continue;
            }

            let fq = format!("{}::{}", module.module_path(), proc.name());
            match decompiler.decompile_proc(&fq) {
                Ok(decompiled) => print!(
                    "{}",
                    decompiled.render(FormattingConfig::default().with_color(!cli.no_color))
                ),
                Err(error) => error!("Error: {error}"),
            }
        }
    }

    Ok(())
}

fn parse_library_spec(spec: &str) -> Result<LibraryRoot, String> {
    let (ns, path) = spec
        .split_once('=')
        .ok_or_else(|| "library spec must be <namespace>=<path>".to_string())?;
    if ns.is_empty() {
        return Err("library namespace cannot be empty".to_string());
    }
    if path.is_empty() {
        return Err("library path cannot be empty".to_string());
    }
    let pb = PathBuf::from(path);
    Ok(LibraryRoot::new(ns, pb))
}

/// Normalize a CLI path for stable path matching.
///
/// Relative paths are made absolute against `cwd`; existing paths are
/// canonicalized to remove redundant components and symlink indirections.
fn normalize_cli_path(path: &Path, cwd: &Path) -> PathBuf {
    let abs = if path.is_absolute() {
        path.to_path_buf()
    } else {
        cwd.join(path)
    };
    std::fs::canonicalize(&abs).unwrap_or(abs)
}

/// Normalize user-provided library roots.
fn normalize_library_roots(roots: &[LibraryRoot], cwd: &Path) -> Vec<LibraryRoot> {
    roots
        .iter()
        .map(|root| LibraryRoot::new(&root.namespace, normalize_cli_path(&root.path, cwd)))
        .collect()
}

/// Emit warnings for external modules that were referenced but could not be loaded.
fn emit_unresolved_dependency_warnings(workspace: &Workspace) {
    let unresolved = workspace.unresolved_module_paths();
    if unresolved.is_empty() {
        return;
    }

    let rendered_modules = unresolved
        .iter()
        .map(|module| module.as_str().to_string())
        .collect::<Vec<_>>()
        .join(", ");
    warn!(
        "Unable to load {} referenced module(s): {rendered_modules}",
        unresolved.len()
    );

    let rendered_roots = workspace
        .roots()
        .iter()
        .map(format_library_root)
        .collect::<Vec<_>>()
        .join(", ");
    warn!("Configured library roots: {rendered_roots}");

    let mut seen_configured_namespaces = HashSet::new();
    let mut seen_unconfigured_modules = HashSet::new();
    for module in unresolved {
        if let Some(namespace) = configured_namespace_for_module(&module, workspace.roots()) {
            if !seen_configured_namespaces.insert(namespace.to_string()) {
                continue;
            }
            warn!(
                "Namespace `{namespace}` is configured, but some referenced modules were not found under its roots"
            );
        } else {
            if !seen_unconfigured_modules.insert(module.as_str().to_string()) {
                continue;
            }
            warn!(
                "No library root configured for referenced module `{module}`. Add `--library <namespace>=<path>` using the exact MASM path prefix for that module tree"
            );
        }
    }
}

/// Return the longest configured namespace that matches `module`.
fn configured_namespace_for_module<'a>(
    module: &SymbolPath,
    roots: &'a [LibraryRoot],
) -> Option<&'a str> {
    roots
        .iter()
        .filter(|root| !root.namespace.is_empty())
        .filter(|root| root.matches_module_path(module.as_str()))
        .map(|root| root.namespace.as_str())
        .max_by_key(|namespace| namespace.len())
}

/// Render a library root for diagnostics.
fn format_library_root(root: &LibraryRoot) -> String {
    if root.namespace.is_empty() {
        format!("<default>={}", root.path.display())
    } else {
        format!("{}={}", root.namespace, root.path.display())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Ensure CLI parsing accepts multi-segment namespaces with `=` separators.
    #[test]
    fn parse_library_spec_supports_multi_segment_namespaces() {
        let root = parse_library_spec("miden::core=../path/to/miden/core").expect("library root");
        assert_eq!(root.namespace, "miden::core");
        assert_eq!(root.path, PathBuf::from("../path/to/miden/core"));
    }

    /// Ensure legacy `:` separators are rejected because they are ambiguous with `::`.
    #[test]
    fn parse_library_spec_rejects_colon_separator() {
        let err = parse_library_spec("miden::core:../path/to/miden/core")
            .expect_err("legacy separator should be rejected");
        assert_eq!(err, "library spec must be <namespace>=<path>");
    }

    /// Ensure diagnostics prefer the longest configured namespace prefix.
    #[test]
    fn configured_namespace_for_module_prefers_longest_match() {
        let roots = vec![
            LibraryRoot::new("miden", PathBuf::from("/tmp/miden")),
            LibraryRoot::new("miden::core", PathBuf::from("/tmp/miden-core")),
        ];
        let module = SymbolPath::new("miden::core::stark::random_coin");

        assert_eq!(
            configured_namespace_for_module(&module, &roots),
            Some("miden::core")
        );
    }
}
