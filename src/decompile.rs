//! High-level decompilation API.
//!
//! This module provides a structured API for decompiling MASM procedures and modules.

use log::debug;
use std::collections::HashMap;

use crate::{
    callgraph::CallGraph,
    fmt::{CodeWriter, FormattingConfig},
    frontend::Workspace,
    ir::{Stmt, Var},
    lift::{self, LiftingError},
    signature::{ProcSignature, SignatureMap, infer_signatures},
    simplify,
    symbol::path::SymbolPath,
    symbol::resolution::create_resolver,
    types::{
        InferredType, TypeDiagnosticsMap, TypeRequirement, TypeSummary, TypeSummaryMap,
        infer_type_summaries,
    },
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
    /// Procedure exists, but no inferred signature entry was recorded for it.
    MissingProcedureSignature(String),
    /// Procedure exists, but signature inference marked it as unknown.
    UnknownProcedureSignature(String),
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
            DecompilationError::MissingProcedureSignature(name) => {
                write!(f, "procedure `{name}` is missing an inferred signature")
            }
            DecompilationError::UnknownProcedureSignature(name) => {
                write!(f, "procedure `{name}` has unknown inferred signature")
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
    /// Input parameter types by position.
    pub input_types: Vec<TypeRequirement>,
    /// Return value types by position.
    pub output_types: Vec<InferredType>,
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
    /// Inferred procedure type summary, if available.
    pub type_summary: Option<TypeSummary>,
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
            if let Stmt::Return { values, .. } = stmt {
                return Some(values.clone());
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

        let inputs = self.inputs().unwrap_or(0);
        let outputs = self.outputs().unwrap_or(0);
        let (input_types, output_types) = self
            .type_summary
            .as_ref()
            .map(|summary| {
                (
                    normalized_input_types(&summary.inputs, inputs),
                    normalized_output_types(&summary.outputs, outputs),
                )
            })
            .unwrap_or_else(|| {
                (
                    vec![TypeRequirement::Felt; inputs],
                    vec![InferredType::Felt; outputs],
                )
            });

        DecompiledHeader {
            name,
            inputs,
            outputs,
            input_types,
            output_types,
        }
    }

    /// Render this procedure using the provided formatting configuration.
    pub fn render(&self, config: FormattingConfig) -> String {
        let mut writer = CodeWriter::with_config(config);
        writer.write(self);
        writer.finish()
    }
}

/// Normalize inferred input types to exactly match the known input arity.
fn normalized_input_types(types: &[TypeRequirement], expected_len: usize) -> Vec<TypeRequirement> {
    let mut normalized = vec![TypeRequirement::Felt; expected_len];
    for (display_idx, slot) in normalized.iter_mut().enumerate() {
        let summary_idx = expected_len.saturating_sub(1).saturating_sub(display_idx);
        if let Some(ty) = types.get(summary_idx) {
            *slot = *ty;
        }
    }
    normalized
}

/// Normalize inferred output types to exactly match the known output arity.
fn normalized_output_types(types: &[InferredType], expected_len: usize) -> Vec<InferredType> {
    let mut normalized = vec![InferredType::Felt; expected_len];
    for (display_idx, slot) in normalized.iter_mut().enumerate() {
        let summary_idx = expected_len.saturating_sub(1).saturating_sub(display_idx);
        if let Some(ty) = types.get(summary_idx) {
            *slot = *ty;
        }
    }
    normalized
}

impl std::fmt::Display for DecompiledProc {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.render(FormattingConfig::default()))
    }
}

/// Result of decompiling a module (collection of procedures).
#[derive(Debug, Clone)]
pub struct DecompiledModule {
    /// Module path (e.g., "miden::core::math").
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
    type_summaries: TypeSummaryMap,
    type_diagnostics: TypeDiagnosticsMap,
    config: DecompilationConfig,
}

impl<'a> Decompiler<'a> {
    /// Create a new decompiler for the given workspace.
    pub fn new(workspace: &'a Workspace) -> Self {
        let callgraph = CallGraph::from(workspace);
        let signatures = infer_signatures(workspace, &callgraph);
        let (type_summaries, type_diagnostics) =
            infer_type_summaries(workspace, &callgraph, &signatures);
        Self {
            workspace,
            callgraph,
            signatures,
            type_summaries,
            type_diagnostics,
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

    /// Returns a reference to inferred procedure type summaries.
    pub fn type_summaries(&self) -> &TypeSummaryMap {
        &self.type_summaries
    }

    /// Returns a reference to type diagnostics grouped by procedure.
    pub fn type_diagnostics(&self) -> &TypeDiagnosticsMap {
        &self.type_diagnostics
    }

    /// Decompile a single procedure by fully-qualified name.
    pub fn decompile_proc(&self, fq_name: &str) -> DecompilationResult<DecompiledProc> {
        let proc_path = SymbolPath::new(fq_name);
        // Find the procedure in the workspace
        let (program, proc) = self
            .workspace
            .lookup_proc_entry(&proc_path)
            .ok_or_else(|| DecompilationError::ProcedureNotFound(fq_name.to_string()))?;

        // Extract module path from fq_name
        let module_path = proc_path.module_path().unwrap_or("").to_string();

        match self.signatures.get(&proc_path) {
            Some(ProcSignature::Known { .. }) => {}
            Some(ProcSignature::Unknown) => {
                return Err(DecompilationError::UnknownProcedureSignature(
                    fq_name.to_string(),
                ));
            }
            None => {
                return Err(DecompilationError::MissingProcedureSignature(
                    fq_name.to_string(),
                ));
            }
        }

        // Lift directly from AST to structured IR
        debug!("lifting procedure `{}`", fq_name);
        let resolver = create_resolver(program.module(), self.workspace.source_manager());
        let mut stmts = lift::lift_proc(proc, &proc_path, &resolver, &self.signatures)?;

        if self.config.expression_propagation {
            debug!("propagating expressions in `{}`", fq_name);
            simplify::propagate_expressions(&mut stmts);
            debug!("propagating copies in `{}`", fq_name);
            simplify::propagate_copies(&mut stmts);
        }
        if self.config.dead_code_elimination {
            debug!("applying dead-code elimination on `{}`", fq_name);
            simplify::eliminate_dead_code(&mut stmts);
        }
        if self.config.simplification {
            debug!("simplifying statements in `{}`", fq_name);
            simplify::simplify_statements(&mut stmts);
            simplify::shorten_call_targets(&mut stmts, &resolver);
        }

        let signature = self.signatures.get(&proc_path).cloned();
        let type_summary = self.type_summaries.get(&proc_path).cloned();
        let body = DecompiledBody::new(stmts);

        Ok(DecompiledProc {
            name: fq_name.to_string(),
            module_path,
            signature,
            type_summary,
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
