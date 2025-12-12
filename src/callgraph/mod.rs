use std::collections::HashMap;

use miden_assembly_syntax::ast::{
    InvocationTarget, Invoke, InvokeKind, path::PathBuf as MasmPathBuf,
};

use crate::frontend::{Program, Workspace};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CallTarget {
    Direct(String),
    Opaque,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CallEdge {
    pub kind: InvokeKind,
    pub target: CallTarget,
}

#[derive(Debug, Clone)]
pub struct ProcNode {
    pub name: String,
    pub module_path: MasmPathBuf,
    pub edges: Vec<CallEdge>,
}

#[derive(Debug, Default)]
pub struct CallGraph {
    pub nodes: Vec<ProcNode>,
    pub name_to_id: HashMap<String, usize>,
}

impl CallGraph {
    pub fn build(program: &Program) -> Self {
        let mut graph = CallGraph::default();
        for (idx, proc) in program.procedures().enumerate() {
            let module_path = program.module_path().clone();
            let module_path_str = <MasmPathBuf as AsRef<str>>::as_ref(&module_path);
            let name = format!("{}::{}", module_path_str, proc.name().as_str());
            let edges = proc
                .invoked()
                .map(|invoke| edge_from_invoke(invoke, program))
                .collect();
            graph.name_to_id.insert(name.clone(), idx);
            graph.nodes.push(ProcNode {
                name,
                module_path,
                edges,
            });
        }
        graph
    }

    pub fn build_for_workspace(ws: &Workspace) -> Self {
        let mut graph = CallGraph::default();
        for prog in ws.modules() {
            let module_path = prog.module_path().clone();
            let module_path_str = <MasmPathBuf as AsRef<str>>::as_ref(&module_path);
            for proc in prog.procedures() {
                let name = format!("{}::{}", module_path_str, proc.name().as_str());
                let idx = graph.nodes.len();
                graph.name_to_id.insert(name.clone(), idx);
                let edges = proc
                    .invoked()
                    .map(|invoke| edge_from_invoke(invoke, prog))
                    .collect();
                graph.nodes.push(ProcNode {
                    name,
                    module_path: module_path.clone(),
                    edges,
                });
            }
        }
        graph
    }
}

fn edge_from_invoke(invoke: &Invoke, program: &Program) -> CallEdge {
    CallEdge {
        kind: invoke.kind,
        target: match &invoke.target {
            InvocationTarget::Symbol(name) => CallTarget::Direct(format!(
                "{}::{}",
                <MasmPathBuf as AsRef<str>>::as_ref(program.module_path()),
                name.as_str()
            )),
            InvocationTarget::Path(path) => CallTarget::Direct(path.to_string()),
            InvocationTarget::MastRoot(_) => CallTarget::Opaque,
        },
    }
}

pub trait EdgeTargetString {
    fn target_string(&self) -> String;
}

impl EdgeTargetString for CallEdge {
    fn target_string(&self) -> String {
        match &self.target {
            CallTarget::Direct(s) => s.clone(),
            CallTarget::Opaque => "__opaque__".to_string(),
        }
    }
}
