use masm_decompiler::frontend::testing::workspace_from_modules;
use miden_assembly_syntax::debuginfo::{SourceManager, Spanned};

#[test]
fn source_manager_resolves_spans() {
    let ws = workspace_from_modules(&[
        (
            "mod_a",
            r#"
            pub proc a
                push.1
            end
            "#,
        ),
        (
            "mod_b",
            r#"
            pub proc b
                push.2
            end
            "#,
        ),
    ]);

    let source_manager = ws.source_manager();
    for module in ws.modules() {
        for proc in module.procedures() {
            for op in proc.body().iter() {
                let span = op.span();
                assert!(
                    !span.is_unknown(),
                    "expected op span for {}::{} to be known",
                    module.module_path(),
                    proc.name()
                );
                assert!(
                    source_manager.get(span.source_id()).is_ok(),
                    "expected SourceId to resolve for {}::{}",
                    module.module_path(),
                    proc.name()
                );
            }
        }
    }
}
