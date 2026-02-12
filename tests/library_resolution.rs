use std::collections::HashSet;

use masm_decompiler::{frontend::testing::workspace_from_modules, SymbolPath};

/// Ensure unresolved dependency reporting captures missing `std` modules.
#[test]
fn unresolved_module_paths_report_missing_import_modules() {
    let ws = workspace_from_modules(&[(
        "examples::stdlib::pcs::fri::helper",
        include_str!("fixtures/library_resolution.masm"),
    )]);
    let unresolved = ws
        .unresolved_module_paths()
        .into_iter()
        .collect::<HashSet<_>>();
    assert_eq!(
        unresolved,
        HashSet::from([
            SymbolPath::new("std::stark::constants"),
            SymbolPath::new("std::stark::random_coin"),
        ])
    );
}

/// Ensure unresolved dependency reporting clears once dependency modules are loaded.
#[test]
fn unresolved_module_paths_empty_when_import_modules_are_loaded() {
    let ws = workspace_from_modules(&[
        (
            "examples::stdlib::pcs::fri::helper",
            include_str!("fixtures/library_resolution.masm"),
        ),
        (
            "std::stark::constants",
            r#"
            proc get_lde_domain_info_word
                push.0
            end
            "#,
        ),
        (
            "std::stark::random_coin",
            r#"
            proc reseed
                dropw
            end
            "#,
        ),
    ]);

    assert!(ws.unresolved_module_paths().is_empty());
}
