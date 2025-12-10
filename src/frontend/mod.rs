//! Frontend: parse MASM source into an AST module plus lightweight metadata.

use std::path::{Path as FsPath, PathBuf as FsPathBuf};

use miden_assembly_syntax::{
    ast::{path::PathBuf as MasmPathBuf, Module, ModuleKind, Procedure},
    debuginfo::DefaultSourceManager,
    ModuleParser, Report,
};
use std::sync::Arc;

/// A library root maps a namespace (e.g. "std") to a filesystem directory.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LibraryRoot {
    pub namespace: String,
    pub path: FsPathBuf,
}

impl LibraryRoot {
    pub fn new(namespace: impl Into<String>, path: FsPathBuf) -> Self {
        Self {
            namespace: namespace.into(),
            path,
        }
    }
}

/// Parsed MASM module plus its filesystem origin.
#[derive(Debug)]
pub struct Program {
    module: Box<Module>,
    source_path: FsPathBuf,
    module_path: MasmPathBuf,
}

impl Program {
    pub fn from_path(path: impl AsRef<FsPath>, roots: &[LibraryRoot]) -> Result<Self, Report> {
        let path = path.as_ref();
        let mut parser = ModuleParser::new(ModuleKind::Executable);

        let module_name = derive_module_path(path, roots)
            .unwrap_or_else(|_| MasmPathBuf::absolute(Module::ROOT));

        let source_manager: Arc<dyn miden_assembly_syntax::debuginfo::SourceManager> =
            Arc::new(DefaultSourceManager::default());
        let module = parser.parse_file(&module_name, path, source_manager)?;

        Ok(Self {
            module,
            source_path: path.to_path_buf(),
            module_path: module_name,
        })
    }

    /// Construct a program from an already-parsed module and explicit metadata.
    pub fn from_parts(module: Box<Module>, source_path: FsPathBuf, module_path: MasmPathBuf) -> Self {
        Self {
            module,
            source_path,
            module_path,
        }
    }

    pub fn module(&self) -> &Module {
        &self.module
    }

    pub fn source_path(&self) -> &FsPathBuf {
        &self.source_path
    }

    pub fn module_path(&self) -> &MasmPathBuf {
        &self.module_path
    }

    pub fn procedures(&self) -> impl Iterator<Item = &Procedure> {
        self.module.procedures()
    }
}

mod workspace;
pub use workspace::Workspace;
pub mod testing;

/// Derive a MASM module path (e.g. `std::math::u64`) from a filesystem path and library roots.
///
/// Roots are searched in order; the first that contains `file_path` is used. If no root matches,
/// returns an error.
pub fn derive_module_path(
    file_path: &FsPath,
    roots: &[LibraryRoot],
) -> Result<MasmPathBuf, String> {
    let file_name = file_path
        .file_name()
        .and_then(|f| f.to_str())
        .ok_or_else(|| "module path derivation failed: missing file name".to_string())?;
    let is_mod = file_name == "mod.masm";

    for root in roots {
        if let Ok(rel) = file_path.strip_prefix(&root.path) {
            let mut comps: Vec<String> = Vec::new();
            if !root.namespace.is_empty() {
                comps.push(root.namespace.clone());
            }

            let mut parts: Vec<String> = rel
                .components()
                .map(|c| c.as_os_str().to_string_lossy().into_owned())
                .collect();
            if parts.is_empty() {
                continue;
            }

            let file_part = parts.pop().unwrap();
            let stem = if is_mod {
                parts.pop().unwrap_or_else(|| "mod".to_string())
            } else {
                FsPath::new(&file_part)
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .map(|s| s.to_string())
                    .ok_or_else(|| "invalid file stem".to_string())?
            };

            comps.extend(parts);
            comps.push(stem);

            let path_str = comps.join("::");
            return MasmPathBuf::new(&path_str)
                .map_err(|e| format!("invalid module path {path_str}: {e}"));
        }
    }

    Err("module path derivation failed: file not under any library root".to_string())
}
