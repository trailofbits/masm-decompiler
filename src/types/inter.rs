//! Interprocedural type-summary inference.

use miden_assembly_syntax::debuginfo::Spanned;

use crate::callgraph::CallGraph;
use crate::decompile::DecompilationError;
use crate::frontend::{Program, Workspace};
use crate::lift;
use crate::signature::{ProcSignature, SignatureMap};
use crate::symbol::resolution::create_resolver;

use super::declared_summary_for_proc_with_arity;
use super::domain::{InferredType, TypeRequirement};
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
        return TypeSummary::opaque();
    };

    let (inputs, outputs) = match signature {
        ProcSignature::Known {
            public_inputs,
            outputs,
            ..
        } => (*public_inputs, *outputs),
        ProcSignature::Unknown => return TypeSummary::opaque(),
    };

    let Some((program, proc)) = workspace.lookup_proc_entry(&proc_path) else {
        return TypeSummary::opaque_with_arity(inputs, outputs);
    };
    let declared_summary = declared_summary_for_proc_with_arity(program, proc, inputs, outputs);
    let visibility = proc.visibility();
    // Use the procedure name span rather than the full body span for
    // diagnostics. MASM procedures have implicit stack arguments, so
    // there is no explicit parameter list to point at.
    let proc_span = proc.name().span();
    let resolver = create_resolver(program.module(), workspace.source_manager());
    let stmts = match lift::lift_proc(proc, &proc_path, &resolver, signatures) {
        Ok(stmts) => stmts,
        Err(_err) => {
            return declared_summary
                .unwrap_or_else(|| TypeSummary::opaque_with_arity(inputs, outputs));
        }
    };

    let analysis = analyze_proc_types(
        &proc_path,
        inputs,
        outputs,
        visibility,
        proc_span,
        &stmts,
        callee_summaries,
    );
    if !analysis.diagnostics.is_empty() {
        diagnostics.insert(proc_path.clone(), analysis.diagnostics.clone());
    }
    let raw_outputs = analysis.summary.outputs.clone();
    let summary = refine_known_stdlib_outputs(workspace, program, &proc_path, analysis.summary);
    let summary = refine_trusted_declared_inputs_when_outputs_exact(
        workspace,
        program,
        &proc_path,
        summary,
        &raw_outputs,
        declared_summary.as_ref(),
    );
    refine_known_stdlib_inputs(
        workspace,
        program,
        &proc_path,
        summary,
        declared_summary.as_ref(),
    )
}

/// Refine trusted stdlib helpers to keep exact declared limb inputs.
///
/// This is limited to procedures whose inferred output surface already matches
/// an exact declared summary. That avoids pulling in broken source annotations
/// with mismatched arity while recovering intended `U32` limb preconditions for
/// trusted stdlib helpers such as equality and rotate/shift procedures.
fn refine_trusted_declared_inputs_when_outputs_exact(
    workspace: &Workspace,
    program: &Program,
    proc_path: &crate::symbol::path::SymbolPath,
    summary: TypeSummary,
    raw_outputs: &[InferredType],
    declared_summary: Option<&TypeSummary>,
) -> TypeSummary {
    if !is_trusted_stdlib_program(workspace, program, proc_path.as_str()) {
        return summary;
    }

    let Some(declared) = declared_summary else {
        return summary;
    };
    if raw_outputs != declared.outputs {
        return summary;
    }
    if !declared
        .inputs
        .iter()
        .all(|req| *req == TypeRequirement::U32)
    {
        return summary;
    }

    TypeSummary::new_with_map(
        declared.inputs.clone(),
        summary.outputs,
        summary.output_input_map,
    )
}

/// Refine output summaries for exact stdlib procedures whose return-limb
/// shapes are semantically fixed but currently widen through generic field
/// arithmetic in the local typer.
fn refine_known_stdlib_outputs(
    workspace: &Workspace,
    program: &Program,
    proc_path: &crate::symbol::path::SymbolPath,
    summary: TypeSummary,
) -> TypeSummary {
    if !is_trusted_stdlib_program(workspace, program, proc_path.as_str()) {
        return summary;
    }

    let refined_outputs = match proc_path.as_str() {
        "miden::core::math::u64::shr"
        | "miden::core::math::u64::rotl"
        | "miden::core::math::u64::rotr" => Some(vec![InferredType::U32, InferredType::U32]),
        "miden::core::math::u128::wrapping_mul" => Some(vec![
            InferredType::U32,
            InferredType::U32,
            InferredType::U32,
            InferredType::U32,
        ]),
        "miden::core::math::u64::widening_mul" => Some(vec![
            InferredType::U32,
            InferredType::U32,
            InferredType::U32,
            InferredType::U32,
        ]),
        "miden::core::math::u256::overflowing_sub" => Some(vec![
            InferredType::U32,
            InferredType::U32,
            InferredType::U32,
            InferredType::U32,
            InferredType::U32,
            InferredType::U32,
            InferredType::U32,
            InferredType::U32,
            InferredType::Bool,
        ]),
        _ => None,
    };

    let Some(outputs) = refined_outputs else {
        return summary;
    };
    if summary.outputs.len() != outputs.len() {
        return summary;
    }

    TypeSummary::new_with_map(summary.inputs, outputs, summary.output_input_map)
}

/// Refine audited stdlib helper inputs whose semantic surface is fixed by the
/// helper definition rather than recovered by the generic local typer.
fn refine_known_stdlib_inputs(
    workspace: &Workspace,
    program: &Program,
    proc_path: &crate::symbol::path::SymbolPath,
    summary: TypeSummary,
    declared_summary: Option<&TypeSummary>,
) -> TypeSummary {
    if !is_trusted_stdlib_program(workspace, program, proc_path.as_str()) {
        return summary;
    }

    let refined_inputs = match (proc_path.as_str(), declared_summary) {
        (
            "miden::core::math::u64::rotr",
            Some(TypeSummary {
                inputs, outputs, ..
            }),
        ) if inputs
            == &[
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
            ]
            && outputs == &[InferredType::U32, InferredType::U32] =>
        {
            Some(inputs.clone())
        }
        _ => None,
    };

    let Some(inputs) = refined_inputs else {
        return summary;
    };
    if summary.inputs.len() != inputs.len() {
        return summary;
    }

    TypeSummary::new_with_map(inputs, summary.outputs, summary.output_input_map)
}

/// Return whether `program` was loaded from a trusted `miden::core` stdlib root.
fn is_trusted_stdlib_program(workspace: &Workspace, program: &Program, proc_path: &str) -> bool {
    const STDLIB_NAMESPACE: &str = "miden::core";

    workspace.roots().iter().any(|root| {
        root.trusted_stdlib
            && root.namespace == STDLIB_NAMESPACE
            && root.matches_module_path(proc_path)
            && program.source_path().starts_with(&root.path)
    })
}

/// Convert type-analysis failures to decompilation failures when needed.
#[allow(dead_code)]
fn _map_error(err: lift::LiftingError) -> DecompilationError {
    DecompilationError::Lifting(err)
}

#[cfg(test)]
mod tests {
    use std::fs;
    use std::path::PathBuf;
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;
    use crate::frontend::testing::workspace_from_modules;
    use crate::types::{InferredType, TypeRequirement};

    #[test]
    fn widening_mul_refinement_is_covered_for_canonical_stdlib_path() {
        let fixture = TempStdlibRoot::new(
            "math/u64.masm",
            include_str!("../../tests/fixtures/u64.masm"),
        );
        let workspace = fixture.workspace("miden::core::math::u64", true);
        let trusted_proc = crate::symbol::path::SymbolPath::new("miden::core::math::u64::shr");
        let (program, _) = workspace
            .lookup_proc_entry(&trusted_proc)
            .expect("trusted stdlib fixture should contain shr");
        let summary = TypeSummary::new(
            vec![
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
            ],
            vec![
                InferredType::U32,
                InferredType::U32,
                InferredType::U32,
                InferredType::Felt,
            ],
        );

        let refined = refine_known_stdlib_outputs(
            &workspace,
            program,
            &crate::symbol::path::SymbolPath::new("miden::core::math::u64::widening_mul"),
            summary,
        );

        assert_eq!(
            refined.outputs,
            vec![
                InferredType::U32,
                InferredType::U32,
                InferredType::U32,
                InferredType::U32,
            ]
        );
    }

    #[test]
    fn u128_wrapping_mul_refinement_is_covered_for_canonical_stdlib_path() {
        let fixture = TempStdlibRoot::new(
            "math/u128.masm",
            include_str!("../../tests/fixtures/u128.masm"),
        );
        let workspace = fixture.workspace("miden::core::math::u128", true);
        let trusted_proc =
            crate::symbol::path::SymbolPath::new("miden::core::math::u128::wrapping_mul");
        let (program, _) = workspace
            .lookup_proc_entry(&trusted_proc)
            .expect("trusted stdlib fixture should contain wrapping_mul");
        let summary = TypeSummary::new(
            vec![
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
            ],
            vec![
                InferredType::U32,
                InferredType::U32,
                InferredType::U32,
                InferredType::Felt,
            ],
        );

        let refined = refine_known_stdlib_outputs(&workspace, program, &trusted_proc, summary);

        assert_eq!(
            refined.outputs,
            vec![
                InferredType::U32,
                InferredType::U32,
                InferredType::U32,
                InferredType::U32,
            ]
        );
    }

    #[test]
    fn canonical_path_without_trusted_stdlib_provenance_is_not_refined() {
        let fixture = TempStdlibRoot::new(
            "math/u64.masm",
            include_str!("../../tests/fixtures/u64.masm"),
        );
        let workspace = fixture.workspace("miden::core::math::u64", false);
        let proc_path = crate::symbol::path::SymbolPath::new("miden::core::math::u64::shr");
        let (program, _) = workspace
            .lookup_proc_entry(&proc_path)
            .expect("fixture should contain shr");
        let summary = TypeSummary::new(
            vec![
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
            ],
            vec![
                InferredType::U32,
                InferredType::U32,
                InferredType::U32,
                InferredType::Felt,
            ],
        );

        let refined = refine_known_stdlib_outputs(&workspace, program, &proc_path, summary.clone());

        assert_eq!(refined.outputs, summary.outputs);
    }

    #[test]
    fn in_memory_canonical_namespace_is_not_refined() {
        let workspace = workspace_from_modules(&[(
            "miden::core::math::u64",
            include_str!("../../tests/fixtures/u64.masm"),
        )]);
        let proc_path = crate::symbol::path::SymbolPath::new("miden::core::math::u64::shr");
        let (program, _) = workspace
            .lookup_proc_entry(&proc_path)
            .expect("fixture should contain shr");
        let summary = TypeSummary::new(
            vec![
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
            ],
            vec![
                InferredType::U32,
                InferredType::U32,
                InferredType::U32,
                InferredType::Felt,
            ],
        );

        let refined = refine_known_stdlib_outputs(&workspace, program, &proc_path, summary.clone());

        assert_eq!(refined.outputs, summary.outputs);
    }

    #[test]
    fn trusted_declared_inputs_override_incidental_bool_narrowing() {
        let fixture = TempStdlibRoot::new(
            "math/u64.masm",
            include_str!("../../tests/fixtures/u64.masm"),
        );
        let workspace = fixture.workspace("miden::core::math::u64", true);
        let proc_path = crate::symbol::path::SymbolPath::new("miden::core::math::u64::eq");
        let (program, proc) = workspace
            .lookup_proc_entry(&proc_path)
            .expect("fixture should contain eq");
        let declared = declared_summary_for_proc_with_arity(program, proc, 4, 1)
            .expect("declared summary should match u64::eq arity");
        let summary = TypeSummary::new(
            vec![
                TypeRequirement::Bool,
                TypeRequirement::U32,
                TypeRequirement::Bool,
                TypeRequirement::Felt,
            ],
            vec![InferredType::Bool],
        );

        let refined = refine_trusted_declared_inputs_when_outputs_exact(
            &workspace,
            program,
            &proc_path,
            summary,
            &[InferredType::Bool],
            Some(&declared),
        );

        assert_eq!(
            refined.inputs,
            vec![
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
            ]
        );
    }

    #[test]
    fn trusted_declared_inputs_refine_rotr_limb_inputs_when_outputs_match() {
        let fixture = TempStdlibRoot::new(
            "math/u64.masm",
            include_str!("../../tests/fixtures/u64.masm"),
        );
        let workspace = fixture.workspace("miden::core::math::u64", true);
        let proc_path = crate::symbol::path::SymbolPath::new("miden::core::math::u64::rotr");
        let (program, proc) = workspace
            .lookup_proc_entry(&proc_path)
            .expect("fixture should contain rotr");
        let declared = declared_summary_for_proc_with_arity(program, proc, 3, 2)
            .expect("declared summary should match u64::rotr arity");
        let summary = TypeSummary::new(
            vec![
                TypeRequirement::Felt,
                TypeRequirement::Felt,
                TypeRequirement::U32,
            ],
            vec![InferredType::U32, InferredType::U32],
        );

        let refined = refine_trusted_declared_inputs_when_outputs_exact(
            &workspace,
            program,
            &proc_path,
            summary,
            &[InferredType::U32, InferredType::U32],
            Some(&declared),
        );

        assert_eq!(
            refined.inputs,
            vec![
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
            ]
        );
    }

    #[test]
    fn trusted_declared_inputs_do_not_refine_from_post_override_outputs_alone() {
        let fixture = TempStdlibRoot::new(
            "math/u64.masm",
            include_str!("../../tests/fixtures/u64.masm"),
        );
        let workspace = fixture.workspace("miden::core::math::u64", true);
        let proc_path = crate::symbol::path::SymbolPath::new("miden::core::math::u64::rotr");
        let (program, proc) = workspace
            .lookup_proc_entry(&proc_path)
            .expect("fixture should contain rotr");
        let declared = declared_summary_for_proc_with_arity(program, proc, 3, 2)
            .expect("declared summary should match u64::rotr arity");
        let summary = TypeSummary::new(
            vec![
                TypeRequirement::Felt,
                TypeRequirement::Felt,
                TypeRequirement::U32,
            ],
            vec![InferredType::U32, InferredType::U32],
        );

        let refined = refine_trusted_declared_inputs_when_outputs_exact(
            &workspace,
            program,
            &proc_path,
            summary.clone(),
            &[InferredType::Felt, InferredType::Felt],
            Some(&declared),
        );

        assert_eq!(refined.inputs, summary.inputs);
    }

    #[test]
    fn rotr_helper_refinement_recovers_exact_u32_inputs() {
        let fixture = TempStdlibRoot::new(
            "math/u64.masm",
            include_str!("../../tests/fixtures/u64.masm"),
        );
        let workspace = fixture.workspace("miden::core::math::u64", true);
        let proc_path = crate::symbol::path::SymbolPath::new("miden::core::math::u64::rotr");
        let (program, proc) = workspace
            .lookup_proc_entry(&proc_path)
            .expect("fixture should contain rotr");
        let summary = TypeSummary::new(
            vec![
                TypeRequirement::Felt,
                TypeRequirement::Felt,
                TypeRequirement::U32,
            ],
            vec![InferredType::U32, InferredType::U32],
        );

        let declared = declared_summary_for_proc_with_arity(program, proc, 3, 2)
            .expect("declared summary should match u64::rotr arity");
        let refined =
            refine_known_stdlib_inputs(&workspace, program, &proc_path, summary, Some(&declared));

        assert_eq!(
            refined.inputs,
            vec![
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
            ]
        );
    }

    #[test]
    fn infer_summary_for_node_applies_validated_rotr_helper_refinement() {
        let fixture = TempStdlibRoot::new(
            "math/u64.masm",
            include_str!("../../tests/fixtures/u64.masm"),
        );
        let workspace = fixture.workspace("miden::core::math::u64", true);
        let callgraph = CallGraph::from(&workspace);
        let proc_path = crate::symbol::path::SymbolPath::new("miden::core::math::u64::rotr");
        let mut signatures = SignatureMap::default();
        signatures.insert(
            proc_path.clone(),
            crate::signature::ProcSignature::Known {
                inputs: 3,
                public_inputs: 3,
                outputs: 2,
                net_effect: 0,
            },
        );

        let summary = infer_summary_for_node(
            &workspace,
            proc_path.as_str(),
            &callgraph,
            &signatures,
            &TypeSummaryMap::default(),
            &mut TypeDiagnosticsMap::default(),
        );

        assert_eq!(
            summary.inputs,
            vec![
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
            ]
        );
        assert_eq!(summary.outputs, vec![InferredType::U32, InferredType::U32]);
    }

    #[test]
    fn infer_summary_for_node_skips_rotr_helper_refinement_without_exact_declared_summary() {
        let source = include_str!("../../tests/fixtures/u64.masm").replacen(
            "pub proc rotr(b: u32, a: u64) -> u64",
            "pub proc rotr",
            1,
        );
        let fixture = TempStdlibRoot::new("math/u64.masm", &source);
        let workspace = fixture.workspace("miden::core::math::u64", true);
        let callgraph = CallGraph::from(&workspace);
        let proc_path = crate::symbol::path::SymbolPath::new("miden::core::math::u64::rotr");
        let mut signatures = SignatureMap::default();
        signatures.insert(
            proc_path.clone(),
            crate::signature::ProcSignature::Known {
                inputs: 3,
                public_inputs: 3,
                outputs: 2,
                net_effect: 0,
            },
        );

        let summary = infer_summary_for_node(
            &workspace,
            proc_path.as_str(),
            &callgraph,
            &signatures,
            &TypeSummaryMap::default(),
            &mut TypeDiagnosticsMap::default(),
        );

        assert_ne!(
            summary.inputs,
            vec![
                TypeRequirement::U32,
                TypeRequirement::U32,
                TypeRequirement::U32,
            ]
        );
        assert_eq!(summary.outputs, vec![InferredType::U32, InferredType::U32]);
    }

    /// Temporary stdlib-like root used by provenance-gated refinement tests.
    struct TempStdlibRoot {
        root: PathBuf,
    }

    impl TempStdlibRoot {
        /// Create a temporary trusted `miden::core` root with one module file.
        fn new(module_relative: &str, source: &str) -> Self {
            let unique = SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .expect("system time should be after unix epoch")
                .as_nanos();
            let root = std::env::temp_dir().join(format!(
                "masm-decompiler-inter-stdlib-{}-{unique}",
                std::process::id()
            ));
            fs::create_dir_all(&root).expect("create temp stdlib root");
            fs::write(
                root.join("miden-project.toml"),
                "[lib]\nnamespace = \"miden::core\"\n",
            )
            .expect("write miden-project.toml");

            let module_path = root.join(module_relative);
            if let Some(parent) = module_path.parent() {
                fs::create_dir_all(parent).expect("create module directory");
            }
            fs::write(&module_path, source).expect("write module fixture");

            Self { root }
        }

        /// Build a workspace that loads this root as `miden::core`.
        fn workspace(&self, module_path: &str, trusted: bool) -> Workspace {
            let root = if trusted {
                crate::frontend::LibraryRoot::trusted_stdlib("miden::core", self.root.clone())
            } else {
                crate::frontend::LibraryRoot::new("miden::core", self.root.clone())
            };
            let mut workspace = Workspace::new(vec![root]);
            workspace
                .load_module_by_path(module_path)
                .expect("trusted stdlib fixture module should load");
            workspace
        }
    }

    impl Drop for TempStdlibRoot {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.root);
        }
    }
}
