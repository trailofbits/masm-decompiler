//! Tests for the high-level decompilation API.

use masm_decompiler::{
    decompile::{DecompilationConfig, Decompiler},
    fmt::{CodeWriter, FormattingConfig},
    frontend::testing::workspace_from_modules,
    ir::Stmt,
};

#[test]
fn decompile_single_procedure() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc add_one
            push.1
            add
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let result = decompiler.decompile_proc("test::add_one").unwrap();

    assert_eq!(result.name, "test::add_one");
    assert_eq!(result.module_path, "test");
    assert!(result.inputs().is_some());
    assert!(result.outputs().is_some());
    assert!(!result.stmts().is_empty());
}

#[test]
fn decompile_with_custom_config() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc example
            push.1.2
            add
            drop
        end
        "#,
    )]);

    // With all optimizations (default)
    let with_opts = Decompiler::new(&ws)
        .decompile_proc("test::example")
        .unwrap();

    // Without expression propagation
    let no_prop = Decompiler::new(&ws)
        .with_config(DecompilationConfig::default().with_expression_propagation(false))
        .decompile_proc("test::example")
        .unwrap();

    // Without any optimizations
    let no_opts = Decompiler::new(&ws)
        .with_config(DecompilationConfig::no_optimizations())
        .decompile_proc("test::example")
        .unwrap();

    // All should produce valid output
    assert!(!with_opts.stmts().is_empty());
    assert!(!no_prop.stmts().is_empty());
    assert!(!no_opts.stmts().is_empty());
}

#[test]
fn decompile_module() {
    let ws = workspace_from_modules(&[(
        "mod",
        r#"
        pub proc foo
            push.1
        end

        pub proc bar
            push.2
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let module = decompiler.decompile_module("mod").unwrap();

    assert_eq!(module.module_path, "mod");
    assert_eq!(module.procedures.len(), 2);

    // Check we can find procedures by name
    assert!(module.get_proc("foo").is_some());
    assert!(module.get_proc("bar").is_some());
    assert!(module.get_proc("nonexistent").is_none());
}

#[test]
fn decompile_all_modules() {
    let ws = workspace_from_modules(&[
        (
            "mod_a",
            r#"
            pub proc proc_a
                push.1
            end
            "#,
        ),
        (
            "mod_b",
            r#"
            pub proc proc_b
                push.2
            end
            "#,
        ),
    ]);

    let decompiler = Decompiler::new(&ws);
    let all = decompiler.decompile_all().unwrap();

    assert_eq!(all.len(), 2);
    assert!(all.contains_key("mod_a"));
    assert!(all.contains_key("mod_b"));
}

#[test]
fn decompile_error_procedure_not_found() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc exists
            push.1
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let result = decompiler.decompile_proc("test::nonexistent");

    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.to_string().contains("not found"));
}

#[test]
fn decompile_error_module_not_found() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc exists
            push.1
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let result = decompiler.decompile_module("nonexistent");

    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(err.to_string().contains("not found"));
}

#[test]
fn config_builder_pattern() {
    // Test the builder pattern for config
    let config = DecompilationConfig::new()
        .with_expression_propagation(false)
        .with_dead_code_elimination(true);

    assert!(!config.expression_propagation);
    assert!(config.dead_code_elimination);

    let no_opts = DecompilationConfig::no_optimizations();
    assert!(!no_opts.expression_propagation);
    assert!(!no_opts.dead_code_elimination);
}

#[test]
fn decompiled_proc_return_vars() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc returns_two
            push.1.2
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let result = decompiler.decompile_proc("test::returns_two").unwrap();

    // Should have a Return statement with 2 variables
    let has_return = result
        .stmts()
        .iter()
        .any(|s| matches!(s, Stmt::Return { .. }));
    assert!(has_return, "should have a return statement");

    let return_vars = result.return_vars();
    assert!(return_vars.is_some(), "should find return vars");
    assert_eq!(return_vars.unwrap().len(), 2, "should return 2 values");
}

#[test]
fn decompiler_accessors() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc foo
            push.1
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);

    // Test that accessors work
    assert!(!decompiler.callgraph().nodes.is_empty());
    assert!(!decompiler.signatures().is_empty());
    assert!(!decompiler.type_summaries().is_empty());
    assert!(decompiler.workspace().modules().next().is_some());

    // Default config has all optimizations enabled
    assert!(decompiler.config().expression_propagation);
    assert!(decompiler.config().dead_code_elimination);
}

#[test]
fn decompiler_with_config() {
    let ws = workspace_from_modules(&[(
        "test",
        r#"
        pub proc foo
            push.1
        end
        "#,
    )]);

    // Test with_config builder pattern
    let decompiler = Decompiler::new(&ws).with_config(DecompilationConfig::no_optimizations());

    // Config should reflect what we set
    assert!(!decompiler.config().expression_propagation);
    assert!(!decompiler.config().dead_code_elimination);

    // Should still be able to decompile
    let result = decompiler.decompile_proc("test::foo").unwrap();
    assert!(!result.stmts().is_empty());
}

#[test]
fn formatter_prints_typed_signatures() {
    let ws = workspace_from_modules(&[(
        "typed",
        r#"
        pub proc typed_header
            dup.2
            if.true
                nop
            else
                nop
            end
            mem_load
            drop
            dup.0
            push.1
            add
            swap.1
            drop
            dup.1
            push.1
            eq
            swap.2
            drop
            swap.1
        end

        pub proc sink
            drop
        end

        pub proc unknown_out
            adv_push.1
        end
        "#,
    )]);

    let decompiler = Decompiler::new(&ws);
    let typed_header = decompiler.decompile_proc("typed::typed_header").unwrap();
    let sink = decompiler.decompile_proc("typed::sink").unwrap();
    let unknown_out = decompiler.decompile_proc("typed::unknown_out").unwrap();

    let mut writer = CodeWriter::with_config(FormattingConfig::new().with_color(false));
    writer.write(&typed_header);
    let typed_output = writer.finish();
    let typed_first_line = typed_output.lines().next().unwrap_or_default();
    assert_eq!(
        typed_first_line,
        "proc typed_header(v_0: Bool, v_1: Felt, v_2: Address) -> (Bool, Felt) {"
    );

    let mut writer = CodeWriter::with_config(FormattingConfig::new().with_color(false));
    writer.write(&sink);
    let sink_output = writer.finish();
    let sink_first_line = sink_output.lines().next().unwrap_or_default();
    assert_eq!(sink_first_line, "proc sink(v_0: Felt) {");

    let mut writer = CodeWriter::with_config(FormattingConfig::new().with_color(false));
    writer.write(&unknown_out);
    let unknown_out_output = writer.finish();
    let unknown_out_first_line = unknown_out_output.lines().next().unwrap_or_default();
    assert_eq!(unknown_out_first_line, "proc unknown_out() -> Felt {");
}
