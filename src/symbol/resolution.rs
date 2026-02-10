//! Unified symbol resolution for Miden assembly.

use std::sync::Arc;

use miden_assembly_syntax::{
    Path,
    ast::{InvocationTarget, LocalSymbolResolver, Module, SymbolResolution},
    debuginfo::{SourceManager, SourceSpan, Span, Spanned},
};

use crate::frontend::Workspace;
use crate::symbol::path::SymbolPath;

// -----------------------------------------------------------------------------
// Module-level resolution
// -----------------------------------------------------------------------------

/// Resolve an invocation target to its fully-qualified symbol path.
///
/// This is the single source of truth for symbol resolution across the codebase.
pub fn resolve_target(
    module: &Module,
    source_manager: Arc<dyn SourceManager>,
    target: &InvocationTarget,
) -> Option<SymbolPath> {
    create_resolver(module, source_manager).resolve_target(target)
}

/// Resolve a simple symbol name to its fully-qualified path.
///
/// Handles local definitions and imported procedures via `use` statements.
pub fn resolve_symbol(
    module: &Module,
    source_manager: Arc<dyn SourceManager>,
    name: &str,
) -> SymbolPath {
    create_resolver(module, source_manager).resolve_symbol(name)
}

/// Resolve a qualified path (e.g., `base_field::square`) to its fully-qualified path.
///
/// Handles:
/// - Module aliases from `use` statements
/// - Absolute paths (starting with `::`)
/// - Relative paths within the module hierarchy
pub fn resolve_path(
    module: &Module,
    source_manager: Arc<dyn SourceManager>,
    path_str: &str,
) -> SymbolPath {
    create_resolver(module, source_manager).resolve_path(path_str)
}

/// Create a resolver that can be reused for multiple resolutions within the same module.
///
/// This is more efficient when resolving many symbols from the same module.
pub fn create_resolver(
    module: &Module,
    source_manager: Arc<dyn SourceManager>,
) -> SymbolResolver<'_> {
    SymbolResolver {
        module,
        resolver: LocalSymbolResolver::new(module, source_manager),
    }
}

/// A reusable symbol resolver for a specific module.
///
/// More efficient than calling `resolve_target` repeatedly, as it caches
/// the `LocalSymbolResolver`.
pub struct SymbolResolver<'a> {
    module: &'a Module,
    resolver: LocalSymbolResolver,
}

impl std::fmt::Debug for SymbolResolver<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SymbolResolver")
            .field("module_path", &self.module.path())
            .finish_non_exhaustive()
    }
}

impl<'a> SymbolResolver<'a> {
    /// Resolve an invocation target to its fully-qualified path.
    pub fn resolve_target(&self, target: &InvocationTarget) -> Option<SymbolPath> {
        match target {
            InvocationTarget::MastRoot(_) => None,
            InvocationTarget::Symbol(ident) => Some(resolve_symbol_span(
                self.module,
                &self.resolver,
                Span::new(ident.span(), ident.as_str()),
            )),
            InvocationTarget::Path(path) => Some(resolve_path_span(
                self.module,
                &self.resolver,
                path.as_deref(),
            )),
        }
    }

    /// Resolve a simple symbol name.
    pub fn resolve_symbol(&self, name: &str) -> SymbolPath {
        resolve_symbol_span(
            self.module,
            &self.resolver,
            Span::new(SourceSpan::UNKNOWN, name),
        )
    }

    /// Resolve a qualified path.
    pub fn resolve_path(&self, path_str: &str) -> SymbolPath {
        let path = Path::new(path_str);
        resolve_path_span(
            self.module,
            &self.resolver,
            Span::new(SourceSpan::UNKNOWN, path),
        )
    }

    /// Get the underlying module.
    pub fn module(&self) -> &'a Module {
        self.module
    }
}

// -----------------------------------------------------------------------------
// Workspace-level resolution
// -----------------------------------------------------------------------------

/// Workspace-level symbol resolution trait.
///
/// Implementations should use the provided module path to resolve symbols using
/// the module's import context.
pub trait WorkspaceSymbolResolver {
    fn resolve_target(&self, module: &SymbolPath, target: &InvocationTarget) -> Option<SymbolPath>;
    fn resolve_symbol(&self, module: &SymbolPath, name: &str) -> SymbolPath;
    fn resolve_path(&self, module: &SymbolPath, path: &str) -> SymbolPath;
}

impl WorkspaceSymbolResolver for Workspace {
    fn resolve_target(&self, module: &SymbolPath, target: &InvocationTarget) -> Option<SymbolPath> {
        let program = self.lookup_module(module)?;
        let resolver = create_resolver(program.module(), self.source_manager());
        resolver.resolve_target(target)
    }

    fn resolve_symbol(&self, module: &SymbolPath, name: &str) -> SymbolPath {
        if let Some(program) = self.lookup_module(module) {
            let resolver = create_resolver(program.module(), self.source_manager());
            return resolver.resolve_symbol(name);
        }
        SymbolPath::from_module_path_and_name(module.as_str(), name)
    }

    fn resolve_path(&self, module: &SymbolPath, path: &str) -> SymbolPath {
        if let Some(program) = self.lookup_module(module) {
            let resolver = create_resolver(program.module(), self.source_manager());
            return resolver.resolve_path(path);
        }
        SymbolPath::new(path)
    }
}

// -----------------------------------------------------------------------------
// Internal helpers
// -----------------------------------------------------------------------------

fn resolve_symbol_span(
    module: &Module,
    resolver: &LocalSymbolResolver,
    name: Span<&str>,
) -> SymbolPath {
    if let Ok(resolution) = resolver.resolve(name) {
        if let Some(path) = resolution_to_path(module, resolution) {
            return path;
        }
    }

    SymbolPath::from_module_and_name(module, *name.inner())
}

fn resolve_path_span(
    module: &Module,
    resolver: &LocalSymbolResolver,
    path: Span<&Path>,
) -> SymbolPath {
    if path.inner().is_absolute() {
        return SymbolPath::new(path.as_str());
    }

    if let Ok(resolution) = resolver.resolve_path(path) {
        if let Some(path) = resolution_to_path(module, resolution) {
            return path;
        }
    }

    SymbolPath::new(path.as_str())
}

/// Convert a `SymbolResolution` to a `SymbolPath`.
fn resolution_to_path(module: &Module, resolution: SymbolResolution) -> Option<SymbolPath> {
    match resolution {
        SymbolResolution::Local(idx) => {
            let item = module.get(idx.into_inner())?;
            Some(SymbolPath::from_module_and_name(
                module,
                item.name().as_str(),
            ))
        }
        SymbolResolution::External(path) => Some(SymbolPath::new(path.as_str())),
        SymbolResolution::Module { path, .. } => Some(SymbolPath::new(path.as_str())),
        SymbolResolution::Exact { path, .. } => Some(SymbolPath::new(path.as_str())),
        SymbolResolution::MastRoot(_) => None,
    }
}
