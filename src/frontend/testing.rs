use std::path::PathBuf;

use miden_assembly_syntax::{
    ModuleParser,
    ast::{Module, ModuleKind, path::PathBuf as MasmPathBuf},
    debuginfo::{DefaultSourceManager, SourceManager},
};
use std::sync::Arc;

use super::{LibraryRoot, Program, Workspace};

/// Build a workspace from in-memory modules specified as (module_path, source).
pub fn workspace_from_modules(mods: &[(&str, &str)]) -> Workspace {
    let mut ws = Workspace::new(vec![LibraryRoot::new("", PathBuf::from("."))]);
    for (path, source) in mods {
        let module_path =
            MasmPathBuf::new(path).unwrap_or_else(|_| MasmPathBuf::absolute(Module::ROOT));
        let mut parser = ModuleParser::new(ModuleKind::Library);
        let source_manager: Arc<dyn SourceManager> = Arc::new(DefaultSourceManager::default());
        let module = parser
            .parse_str(module_path.clone(), *source, source_manager)
            .expect("parse");
        let program =
            Program::from_parts(module, PathBuf::from(format!("{path}.masm")), module_path);
        ws.add_program(program);
    }
    ws
}
