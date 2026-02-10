use std::collections::HashMap;
use std::path::{Path as FsPath, PathBuf as FsPathBuf};
use std::sync::Arc;

use miden_assembly_syntax::ast::path::PathBuf as MasmPathBuf;
use miden_assembly_syntax::debuginfo::{DefaultSourceManager, SourceManager};

use super::{LibraryRoot, Program};

/// In-memory collection of parsed modules plus the search roots used to resolve them.
#[derive(Debug)]
pub struct Workspace {
    roots: Vec<LibraryRoot>,
    source_manager: Arc<dyn SourceManager>,
    modules: Vec<Program>,
    index: HashMap<String, usize>,
    pub(crate) proc_index: HashMap<String, (usize, usize)>,
}

impl Workspace {
    pub fn new(roots: Vec<LibraryRoot>) -> Self {
        let source_manager: Arc<dyn SourceManager> = Arc::new(DefaultSourceManager::default());
        Self::with_source_manager(roots, source_manager)
    }

    pub fn with_source_manager(
        roots: Vec<LibraryRoot>,
        source_manager: Arc<dyn SourceManager>,
    ) -> Self {
        Self {
            roots,
            source_manager,
            modules: Vec::new(),
            index: HashMap::new(),
            proc_index: HashMap::new(),
        }
    }

    /// Load the entry module from a file path. If already loaded, returns its index.
    pub fn load_entry(&mut self, path: &FsPath) -> Result<usize, String> {
        let prog = Program::from_path(path, &self.roots, self.source_manager.clone())
            .map_err(|e| e.to_string())?;
        let key = as_str(prog.module_path()).to_string();
        if let Some(idx) = self.index.get(&key).copied() {
            return Ok(idx);
        }
        let idx = self.modules.len();
        self.modules.push(prog);
        self.index.insert(key, idx);
        self.reindex_procs(idx);
        Ok(idx)
    }

    /// Insert a program directly (useful for in-memory tests).
    ///
    /// Note: `program` should be parsed using this workspace's source manager to
    /// ensure SourceSpan lookups resolve correctly.
    pub fn add_program(&mut self, program: Program) -> usize {
        let key = as_str(program.module_path()).to_string();
        if let Some(idx) = self.index.get(&key).copied() {
            return idx;
        }
        let idx = self.modules.len();
        self.modules.push(program);
        self.index.insert(key, idx);
        self.reindex_procs(idx);
        idx
    }

    /// Iteratively load modules referenced by path-based invocations until no new modules can be found.
    pub fn load_dependencies(&mut self) {
        let mut changed = true;
        while changed {
            changed = false;
            let mut to_load = Vec::new();
            for prog in self.modules.iter() {
                let current_module = as_str(prog.module_path()).to_string();
                for proc in prog.procedures() {
                    for invoke in proc.invoked() {
                        if let Some(module_path) =
                            invocation_module_path(&invoke.target, &current_module)
                        {
                            if !self.index.contains_key(&module_path) {
                                to_load.push(module_path);
                            }
                        }
                    }
                }
            }
            for module_path in to_load {
                if self.index.contains_key(&module_path) {
                    continue;
                }
                if let Some(idx) = self.load_module_by_path(&module_path) {
                    let _ = idx;
                    changed = true;
                }
            }
        }
    }

    /// Load a module by its absolute MASM path (e.g., `std::math::u64`) if it exists on disk.
    /// Returns `None` if no matching file could be found.
    pub fn load_module_by_path(&mut self, module_path: &str) -> Option<usize> {
        if let Some(idx) = self.index.get(module_path).copied() {
            return Some(idx);
        }
        let file = find_module_file(module_path, &self.roots)?;
        let prog = Program::from_path(&file, &self.roots, self.source_manager.clone()).ok()?;
        let key = as_str(prog.module_path()).to_string();
        let idx = self.modules.len();
        self.modules.push(prog);
        self.index.insert(key, idx);
        self.reindex_procs(idx);
        Some(idx)
    }

    pub fn modules(&self) -> impl Iterator<Item = &Program> {
        self.modules.iter()
    }

    pub fn lookup_proc(&self, name: &str) -> Option<&miden_assembly_syntax::ast::Procedure> {
        let (m_idx, p_idx) = self.proc_index.get(name).copied()?;
        self.modules
            .get(m_idx)
            .and_then(|m| m.procedures().nth(p_idx))
    }

    pub fn roots(&self) -> &[LibraryRoot] {
        &self.roots
    }

    pub fn source_manager(&self) -> Arc<dyn SourceManager> {
        self.source_manager.clone()
    }
}

fn as_str(path: &MasmPathBuf) -> &str {
    <MasmPathBuf as AsRef<str>>::as_ref(path)
}

/// Given a fully-qualified module path and library roots, locate the corresponding file on disk.
/// Tries `<root>/<components>.masm` and `<root>/<components>/<name>/mod.masm`.
pub fn find_module_file(module_path: &str, roots: &[LibraryRoot]) -> Option<FsPathBuf> {
    let comps: Vec<&str> = module_path.split("::").filter(|c| !c.is_empty()).collect();
    if comps.is_empty() {
        return None;
    }
    for root in roots {
        let (ns_match, rest) = if !root.namespace.is_empty() {
            if comps.first()? != &root.namespace {
                continue;
            }
            (true, &comps[1..])
        } else {
            (true, comps.as_slice())
        };
        if !ns_match {
            continue;
        }
        if rest.is_empty() {
            continue;
        }
        let name = rest.last().unwrap();
        let dir_parts = &rest[..rest.len() - 1];

        let mut direct = FsPathBuf::from(&root.path);
        for part in dir_parts {
            direct.push(part);
        }
        direct.push(format!("{name}.masm"));
        if direct.is_file() {
            return Some(direct);
        }

        let mut mod_path = FsPathBuf::from(&root.path);
        for part in rest {
            mod_path.push(part);
        }
        mod_path.push("mod.masm");
        if mod_path.is_file() {
            return Some(mod_path);
        }
    }
    None
}

fn invocation_module_path(
    target: &miden_assembly_syntax::ast::InvocationTarget,
    current: &str,
) -> Option<String> {
    use miden_assembly_syntax::ast::InvocationTarget::*;
    match target {
        MastRoot(_) => None,
        Symbol(_) => None, // local to current module
        Path(path) => {
            let parent = path.parent()?;
            let module = parent.to_string();
            if module == current {
                None
            } else {
                Some(module)
            }
        }
    }
}

fn proc_fq_name(module_path: &str, proc_name: &str) -> String {
    format!("{module_path}::{proc_name}")
}

impl Workspace {
    fn reindex_procs(&mut self, module_idx: usize) {
        if let Some(prog) = self.modules.get(module_idx) {
            let module_path = as_str(prog.module_path());
            for (proc_idx, proc) in prog.procedures().enumerate() {
                let name = proc_fq_name(module_path, proc.name().as_str());
                self.proc_index.insert(name, (module_idx, proc_idx));
            }
        }
    }
}
