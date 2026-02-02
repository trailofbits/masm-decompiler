//! High-level decompilation API.
//!
//! This module provides a structured API for decompiling MASM procedures and modules.

use log::debug;
use std::collections::HashMap;

use crate::{
    callgraph::CallGraph,
    fmt::CodeWriter,
    frontend::Workspace,
    ir::{Stmt, Var},
    lift::{self, LiftingError},
    signature::{ProcSignature, SignatureMap, infer_signatures},
    simplify,
};

/// Configuration for the decompilation pipeline.
///
/// Controls which optimization passes are enabled during decompilation.
#[derive(Debug, Clone)]
pub struct DecompilationConfig {
    /// Enable expression propagation (constant folding and inlining).
    ///
    /// Default: `true`
    pub expression_propagation: bool,

    /// Enable dead code elimination.
    ///
    /// Default: `true`
    pub dead_code_elimination: bool,

    /// Enable statement and expression simplification passes
    ///
    /// Default: `true`
    pub simplification: bool,
}

impl Default for DecompilationConfig {
    fn default() -> Self {
        Self {
            expression_propagation: true,
            dead_code_elimination: true,
            simplification: true,
        }
    }
}

impl DecompilationConfig {
    /// Create a new config with all optimizations enabled.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a config with no optimizations enabled.
    pub fn no_optimizations() -> Self {
        Self {
            expression_propagation: false,
            dead_code_elimination: false,
            simplification: false,
        }
    }

    /// Set whether expression propagation is enabled.
    pub fn with_expression_propagation(mut self, enabled: bool) -> Self {
        self.expression_propagation = enabled;
        self
    }

    /// Set whether dead code elimination is enabled.
    pub fn with_dead_code_elimination(mut self, enabled: bool) -> Self {
        self.dead_code_elimination = enabled;
        self
    }

    pub fn with_simplification(mut self, enabled: bool) -> Self {
        self.simplification = enabled;
        self
    }
}

/// Error type for decompilation failures.
#[derive(Debug)]
pub enum DecompilationError {
    /// Procedure not found in the workspace.
    ProcedureNotFound(String),
    /// Module not found in the workspace.
    ModuleNotFound(String),
    /// Error during lifting.
    Lifting(LiftingError),
}

impl std::fmt::Display for DecompilationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            DecompilationError::ProcedureNotFound(name) => {
                write!(f, "procedure `{name}` not found")
            }
            DecompilationError::ModuleNotFound(name) => {
                write!(f, "module `{name}` not found")
            }
            DecompilationError::Lifting(e) => write!(f, "{e}"),
        }
    }
}

impl std::error::Error for DecompilationError {}

impl From<LiftingError> for DecompilationError {
    fn from(e: LiftingError) -> Self {
        DecompilationError::Lifting(e)
    }
}

/// Result type for decompilation operations.
pub type DecompilationResult<T> = Result<T, DecompilationError>;

/// Header information for a decompiled procedure.
#[derive(Debug, Clone)]
pub struct DecompiledHeader {
    /// Procedure name (without module path).
    pub name: String,
    /// Number of input parameters.
    pub inputs: usize,
    /// Number of output values.
    pub outputs: usize,
}

/// A structured procedure body.
#[derive(Debug, Clone)]
pub struct DecompiledBody {
    /// The statements in the procedure body.
    pub stmts: Vec<Stmt>,
}

impl DecompiledBody {
    /// Create a new structured body from a sequence of statements.
    pub fn new(stmts: Vec<Stmt>) -> Self {
        Self { stmts }
    }

    /// Returns a reference to the statements.
    pub fn stmts(&self) -> &[Stmt] {
        &self.stmts
    }

    /// Returns a mutable reference to the statements.
    pub fn stmts_mut(&mut self) -> &mut Vec<Stmt> {
        &mut self.stmts
    }
}

/// Result of decompiling a single procedure.
#[derive(Debug, Clone)]
pub struct DecompiledProc {
    /// Fully-qualified procedure name (e.g., "module::proc_name").
    pub name: String,
    /// Module path containing this procedure.
    pub module_path: String,
    /// Inferred procedure signature, if available.
    pub signature: Option<ProcSignature>,
    /// The decompiled procedure body.
    pub body: DecompiledBody,
}

impl DecompiledProc {
    /// Returns the statements in the procedure body.
    pub fn stmts(&self) -> &[Stmt] {
        self.body.stmts()
    }

    /// Returns the number of input parameters, if known.
    pub fn inputs(&self) -> Option<usize> {
        match &self.signature {
            Some(ProcSignature::Known { inputs, .. }) => Some(*inputs),
            _ => None,
        }
    }

    /// Returns the number of output values, if known.
    pub fn outputs(&self) -> Option<usize> {
        match &self.signature {
            Some(ProcSignature::Known { outputs, .. }) => Some(*outputs),
            _ => None,
        }
    }

    /// Find the return statement variables, if present.
    pub fn return_vars(&self) -> Option<Vec<Var>> {
        for stmt in self.body.stmts() {
            if let Stmt::Return(vals) = stmt {
                return Some(vals.clone());
            }
        }
        None
    }

    /// Returns the procedure header containing name and signature info.
    pub fn header(&self) -> DecompiledHeader {
        let name = self
            .name
            .rsplit_once("::")
            .map(|(_, n)| n)
            .unwrap_or(&self.name)
            .to_string();

        DecompiledHeader {
            name,
            inputs: self.inputs().unwrap_or(0),
            outputs: self.outputs().unwrap_or(0),
        }
    }
}

impl std::fmt::Display for DecompiledProc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut writer = CodeWriter::new();
        writer.write(self);
        write!(f, "{}", writer.finish())
    }
}

/// Result of decompiling a module (collection of procedures).
#[derive(Debug, Clone)]
pub struct DecompiledModule {
    /// Module path (e.g., "std::math").
    pub module_path: String,
    /// Decompiled procedures in this module.
    pub procedures: Vec<DecompiledProc>,
}

impl DecompiledModule {
    /// Returns an iterator over the decompiled procedures.
    pub fn iter(&self) -> impl Iterator<Item = &DecompiledProc> {
        self.procedures.iter()
    }

    /// Find a procedure by name (without module path prefix).
    pub fn get_proc(&self, name: &str) -> Option<&DecompiledProc> {
        self.procedures
            .iter()
            .find(|p| p.name.ends_with(&format!("::{}", name)))
    }
}

/// High-level decompiler interface.
pub struct Decompiler<'a> {
    workspace: &'a Workspace,
    callgraph: CallGraph,
    signatures: SignatureMap,
    config: DecompilationConfig,
}

impl<'a> Decompiler<'a> {
    /// Create a new decompiler for the given workspace.
    pub fn new(workspace: &'a Workspace) -> Self {
        let callgraph = CallGraph::from(workspace);
        let signatures = infer_signatures(workspace, &callgraph);
        Self {
            workspace,
            callgraph,
            signatures,
            config: DecompilationConfig::default(),
        }
    }

    /// Set the decompilation configuration.
    pub fn with_config(mut self, config: DecompilationConfig) -> Self {
        self.config = config;
        self
    }

    /// Returns a reference to the current configuration.
    pub fn config(&self) -> &DecompilationConfig {
        &self.config
    }

    /// Returns a reference to the underlying workspace.
    pub fn workspace(&self) -> &Workspace {
        self.workspace
    }

    /// Returns a reference to the call graph.
    pub fn callgraph(&self) -> &CallGraph {
        &self.callgraph
    }

    /// Returns a reference to the inferred signatures.
    pub fn signatures(&self) -> &SignatureMap {
        &self.signatures
    }

    /// Decompile a single procedure by fully-qualified name.
    pub fn decompile_proc(&self, fq_name: &str) -> DecompilationResult<DecompiledProc> {
        // Find the procedure in the workspace
        let proc = self
            .workspace
            .lookup_proc(fq_name)
            .ok_or_else(|| DecompilationError::ProcedureNotFound(fq_name.to_string()))?;

        // Extract module path from fq_name
        let module_path = fq_name
            .rsplit_once("::")
            .map(|(m, _)| m.to_string())
            .unwrap_or_default();

        // Lift directly from AST to structured IR
        debug!("lifting procedure `{}`", fq_name);
        let mut stmts = lift::lift_proc(proc, fq_name, &module_path, &self.signatures)?;

        if self.config.expression_propagation {
            debug!("propagating expressions in `{}`", fq_name);
            simplify::propagate_expressions(&mut stmts);
        }
        if self.config.dead_code_elimination {
            debug!("applying dead-code elimination on `{}`", fq_name);
            simplify::eliminate_dead_code(&mut stmts);
        }
        if self.config.simplification {
            debug!("simplifying statements in `{}`", fq_name);
            simplify::simplify_statements(&mut stmts);
        }

        let signature = self.signatures.get(fq_name).cloned();
        let body = DecompiledBody::new(stmts);

        Ok(DecompiledProc {
            name: fq_name.to_string(),
            module_path,
            signature,
            body,
        })
    }

    /// Decompile all procedures in a module.
    pub fn decompile_module(&self, module_path: &str) -> DecompilationResult<DecompiledModule> {
        let module = self
            .workspace
            .modules()
            .find(|m| m.module_path().to_string() == module_path)
            .ok_or_else(|| DecompilationError::ModuleNotFound(module_path.to_string()))?;

        let mut procedures = Vec::new();

        for proc in module.procedures() {
            let fq_name = format!("{}::{}", module_path, proc.name());
            let decompiled = self.decompile_proc(&fq_name)?;
            procedures.push(decompiled);
        }

        Ok(DecompiledModule {
            module_path: module_path.to_string(),
            procedures,
        })
    }

    /// Decompile all procedures in the workspace.
    pub fn decompile_all(&self) -> DecompilationResult<HashMap<String, DecompiledModule>> {
        let mut result = HashMap::new();

        for module in self.workspace.modules() {
            let module_path = module.module_path().to_string();
            let decompiled = self.decompile_module(&module_path)?;
            result.insert(module_path, decompiled);
        }

        Ok(result)
    }
}
