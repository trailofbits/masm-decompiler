//! Interprocedural type inference for decompiled IR.
//!
//! This module infers conservative type summaries for procedures and emits
//! mismatch diagnostics that can be consumed by tools such as an LSP server.

mod domain;
mod inter;
mod intra;
mod summary;

pub use domain::{InferredType, TypeRequirement, VarBaseKey, VarKey};
pub use inter::infer_type_summaries;
pub use intra::{ProcTypeAnalysisResult, analyze_proc_types};
pub use summary::{TypeDiagnostic, TypeDiagnosticsMap, TypeSummary, TypeSummaryMap};
