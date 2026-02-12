//! Frontend: parse MASM source into an AST module plus lightweight metadata.

use std::path::{Path as FsPath, PathBuf as FsPathBuf};

use miden_assembly_syntax::{
    ModuleParser, Report,
    ast::{Constant, Module, ModuleKind, Procedure, path::PathBuf as MasmPathBuf},
    debuginfo::SourceManager,
};
use std::sync::Arc;

mod workspace;
pub use workspace::Workspace;
pub mod testing;

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
    pub fn from_path(
        path: impl AsRef<FsPath>,
        roots: &[LibraryRoot],
        source_manager: Arc<dyn SourceManager>,
    ) -> Result<Self, Report> {
        let path = path.as_ref();
        // Most MASM files we decompile are library-style modules (no `begin/end` wrapper).
        // Prefer the library parser; fall back to executable if needed.
        let mut parser = ModuleParser::new(ModuleKind::Library);

        let module_name =
            derive_module_path(path, roots).unwrap_or_else(|_| MasmPathBuf::absolute(Module::ROOT));

        let module = match parser.parse_file(&module_name, path, source_manager.clone()) {
            Ok(m) => m,
            Err(_e) => {
                // Retry as executable for files that use `begin/end` wrappers.
                let mut exec_parser = ModuleParser::new(ModuleKind::Executable);
                exec_parser.parse_file(&module_name, path, source_manager)?
            }
        };

        Ok(Self {
            module,
            source_path: path.to_path_buf(),
            module_path: module_name,
        })
    }

    /// Construct a program from an already-parsed module and explicit metadata.
    pub fn from_parts(
        module: Box<Module>,
        source_path: FsPathBuf,
        module_path: MasmPathBuf,
    ) -> Self {
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

    /// Iterate over constant definitions in this module.
    pub fn constants(&self) -> impl Iterator<Item = &Constant> {
        self.module.constants()
    }
}

/// Derive a MASM module path (e.g. `std::math::u64`) from a filesystem path and library roots.
///
/// Roots are searched in order; the first that contains `file_path` is used. If no root matches,
/// returns an error.
pub fn derive_module_path(
    file_path: &FsPath,
    roots: &[LibraryRoot],
) -> Result<MasmPathBuf, String> {
    let normalized_file_path = normalize_path_for_matching(file_path)?;
    let file_name = normalized_file_path
        .file_name()
        .and_then(|f| f.to_str())
        .ok_or_else(|| "module path derivation failed: missing file name".to_string())?;
    let is_mod = file_name == "mod.masm";

    for root in roots {
        let normalized_root_path = normalize_path_for_matching(&root.path)?;
        if let Ok(rel) = normalized_file_path.strip_prefix(&normalized_root_path) {
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

/// Normalize a filesystem path for prefix matching during module-path derivation.
///
/// Relative paths are made absolute against the process working directory.
fn normalize_path_for_matching(path: &FsPath) -> Result<FsPathBuf, String> {
    if path.is_absolute() {
        return Ok(path.to_path_buf());
    }
    let cwd = std::env::current_dir().map_err(|e| e.to_string())?;
    Ok(cwd.join(path))
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Ensure module-path derivation works when the file path is relative and root is absolute.
    #[test]
    fn derive_module_path_relative_file_absolute_root() {
        let cwd = std::env::current_dir().expect("current dir");
        let roots = vec![LibraryRoot::new("", cwd)];
        let path = FsPath::new("examples/stdlib/pcs/fri/helper.masm");
        let module_path = derive_module_path(path, &roots).expect("module path");
        assert_eq!(
            module_path.to_string(),
            "examples::stdlib::pcs::fri::helper"
        );
    }

    /// Ensure module-path derivation works when the file path is absolute and root is relative.
    #[test]
    fn derive_module_path_absolute_file_relative_root() {
        let cwd = std::env::current_dir().expect("current dir");
        let roots = vec![LibraryRoot::new("", FsPathBuf::from("."))];
        let path = cwd.join("examples/stdlib/pcs/fri/helper.masm");
        let module_path = derive_module_path(path.as_path(), &roots).expect("module path");
        assert_eq!(
            module_path.to_string(),
            "examples::stdlib::pcs::fri::helper"
        );
    }
}
