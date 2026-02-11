//! Interprocedural type-summary inference.

use crate::callgraph::CallGraph;
use crate::decompile::DecompilationError;
use crate::frontend::Workspace;
use crate::lift;
use crate::signature::{ProcSignature, SignatureMap};
use crate::symbol::resolution::create_resolver;

use super::intra::analyze_proc_types;
use super::summary::{TypeDiagnosticsMap, TypeSummary, TypeSummaryMap};

/// Infer type summaries for all procedures in a workspace.
///
/// Procedures are processed in callgraph bottom-up order. Unknown signatures or
/// unsupported lifting patterns produce opaque summaries.
pub fn infer_type_summaries(
    workspace: &Workspace,
    callgraph: &CallGraph,
    signatures: &SignatureMap,
) -> (TypeSummaryMap, TypeDiagnosticsMap) {
    let mut summaries = TypeSummaryMap::default();
    let mut diagnostics = TypeDiagnosticsMap::default();

    for node in callgraph.iter() {
        let summary = infer_summary_for_node(
            workspace,
            node.name.as_str(),
            callgraph,
            signatures,
            &summaries,
            &mut diagnostics,
        );
        summaries.insert(node.name.clone(), summary);
    }

    (summaries, diagnostics)
}

/// Infer a summary for a single procedure.
fn infer_summary_for_node(
    workspace: &Workspace,
    fq_name: &str,
    _callgraph: &CallGraph,
    signatures: &SignatureMap,
    callee_summaries: &TypeSummaryMap,
    diagnostics: &mut TypeDiagnosticsMap,
) -> TypeSummary {
    let proc_path = crate::symbol::path::SymbolPath::new(fq_name.to_string());
    let Some(signature) = signatures.get(&proc_path) else {
        return TypeSummary::unknown();
    };

    let (inputs, outputs) = match signature {
        ProcSignature::Known {
            inputs, outputs, ..
        } => (*inputs, *outputs),
        ProcSignature::Unknown => return TypeSummary::unknown(),
    };

    let Some((program, proc)) = workspace.lookup_proc_entry(&proc_path) else {
        return TypeSummary::unknown_with_arity(inputs, outputs);
    };
    let resolver = create_resolver(program.module(), workspace.source_manager());
    let stmts = match lift::lift_proc(proc, &proc_path, &resolver, signatures) {
        Ok(stmts) => stmts,
        Err(_err) => return TypeSummary::unknown_with_arity(inputs, outputs),
    };

    let analysis = analyze_proc_types(&proc_path, inputs, outputs, &stmts, callee_summaries);
    if !analysis.diagnostics.is_empty() {
        diagnostics.insert(proc_path.clone(), analysis.diagnostics.clone());
    }
    analysis.summary
}

/// Convert type-analysis failures to decompilation failures when needed.
#[allow(dead_code)]
fn _map_error(err: lift::LiftingError) -> DecompilationError {
    DecompilationError::Lifting(err)
}
