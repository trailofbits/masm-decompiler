//! Procedure type summaries and diagnostics.

use std::collections::HashMap;

use miden_assembly_syntax::debuginfo::SourceSpan;

use crate::symbol::path::SymbolPath;

use super::domain::{InferredType, TypeRequirement};

/// Type summary inferred for a single procedure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeSummary {
    /// Required input types by call-argument position.
    ///
    /// Position `0` corresponds to the top-of-stack argument (first popped).
    pub inputs: Vec<TypeRequirement>,
    /// Guaranteed output types by call-result position.
    ///
    /// Position `0` corresponds to the first pushed result (deepest of the
    /// new return values on the stack).
    pub outputs: Vec<InferredType>,
    /// Indicates the summary is opaque and should not be used for mismatch checks.
    pub opaque: bool,
}

impl TypeSummary {
    /// Create a known summary.
    pub fn new(inputs: Vec<TypeRequirement>, outputs: Vec<InferredType>) -> Self {
        Self {
            inputs,
            outputs,
            opaque: false,
        }
    }

    /// Create an opaque summary with explicit input/output arity.
    pub fn opaque_with_arity(inputs: usize, outputs: usize) -> Self {
        Self {
            inputs: vec![TypeRequirement::Felt; inputs],
            outputs: vec![InferredType::Felt; outputs],
            opaque: true,
        }
    }

    /// Create a fully opaque summary without arity information.
    pub fn opaque() -> Self {
        Self::opaque_with_arity(0, 0)
    }

    /// Returns true if this summary is opaque.
    pub const fn is_opaque(&self) -> bool {
        self.opaque
    }
}

impl Default for TypeSummary {
    fn default() -> Self {
        Self::opaque()
    }
}

/// Diagnostic emitted by type analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDiagnostic {
    /// Procedure in which the diagnostic was emitted.
    pub procedure: SymbolPath,
    /// Source span associated with the mismatch.
    pub span: SourceSpan,
    /// Human-readable message.
    pub message: String,
    /// Optional callee (for call-argument diagnostics).
    pub callee: Option<SymbolPath>,
    /// Optional argument index (for call-argument diagnostics).
    pub arg_index: Option<usize>,
    /// Expected type requirement.
    pub expected: Option<TypeRequirement>,
    /// Actual inferred type.
    pub actual: Option<InferredType>,
}

impl TypeDiagnostic {
    /// Create a new diagnostic with the given message.
    pub fn new(procedure: SymbolPath, span: SourceSpan, message: impl Into<String>) -> Self {
        Self {
            procedure,
            span,
            message: message.into(),
            callee: None,
            arg_index: None,
            expected: None,
            actual: None,
        }
    }
}

/// Map of inferred type summaries by procedure.
pub type TypeSummaryMap = HashMap<SymbolPath, TypeSummary>;

/// Map of diagnostics by procedure.
pub type TypeDiagnosticsMap = HashMap<SymbolPath, Vec<TypeDiagnostic>>;
