//! Regression tests for the stdlib header oracle CLI.

use std::{
    fs,
    io::ErrorKind,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};

fn repo_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn ensure_python3() -> bool {
    match Command::new("python3").arg("--version").output() {
        Ok(_) => true,
        Err(err) if err.kind() == ErrorKind::NotFound => false,
        Err(err) => panic!("failed to probe python3 availability: {err}"),
    }
}

fn skip_without_python3(test_name: &str) -> bool {
    if ensure_python3() {
        return false;
    }
    if std::env::var_os("CI").is_some() {
        panic!("python3 is required in CI for {test_name}");
    }
    eprintln!("skipping {test_name}: python3 not available on PATH");
    true
}

fn run_oracle_with_limit(limit: &str) -> std::process::Output {
    Command::new("python3")
        .arg("scripts/stdlib_header_oracle.py")
        .arg("--stdlib-root")
        .arg(repo_root())
        .arg("--limit")
        .arg(limit)
        .current_dir(repo_root())
        .output()
        .expect("python3 should run stdlib_header_oracle.py")
}

fn run_oracle(stdlib_root: &std::path::Path) -> std::process::Output {
    Command::new("python3")
        .arg("scripts/stdlib_header_oracle.py")
        .arg("--repo-root")
        .arg(repo_root())
        .arg("--stdlib-root")
        .arg(stdlib_root)
        .current_dir(repo_root())
        .output()
        .expect("python3 should run stdlib_header_oracle.py")
}

fn temp_stdlib_root(test_name: &str) -> PathBuf {
    let unique = format!(
        "masm-decompiler-{test_name}-{}-{}",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock before unix epoch")
            .as_nanos()
    );
    let path = std::env::temp_dir().join(unique);
    fs::create_dir_all(&path).expect("create temporary stdlib root");
    path
}

#[test]
fn stdlib_header_oracle_rejects_zero_limit() {
    if skip_without_python3("stdlib_header_oracle_rejects_zero_limit") {
        return;
    }
    let output = run_oracle_with_limit("0");

    assert!(
        !output.status.success(),
        "expected parser failure for --limit 0"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("value must be a positive integer"),
        "expected positive-integer parser error, got stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn stdlib_header_oracle_rejects_negative_limit() {
    if skip_without_python3("stdlib_header_oracle_rejects_negative_limit") {
        return;
    }
    let output = run_oracle_with_limit("-1");

    assert!(
        !output.status.success(),
        "expected parser failure for --limit -1"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("value must be a positive integer"),
        "expected positive-integer parser error, got stderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
fn stdlib_header_oracle_disambiguates_duplicate_proc_names() {
    if skip_without_python3("stdlib_header_oracle_disambiguates_duplicate_proc_names") {
        return;
    }

    let temp = temp_stdlib_root("stdlib-header-oracle-duplicate-proc-names");
    fs::write(
        temp.join("miden-project.toml"),
        "[lib]\nnamespace = \"test\"\n",
    )
    .expect("write miden-project.toml");
    fs::write(
        temp.join("alpha.masm"),
        r#"
        pub proc shared() -> u32
            push.2
        end
        "#,
    )
    .expect("write alpha module");
    fs::write(
        temp.join("beta.masm"),
        r#"
        pub proc shared() -> i1
            push.1
            push.1
            eq
        end
        "#,
    )
    .expect("write beta module");

    let output = run_oracle(&temp);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    assert!(
        output.status.success(),
        "expected oracle success, got status {:?}\nstdout:\n{}\nstderr:\n{}",
        output.status.code(),
        stdout,
        stderr
    );
    assert!(stdout.contains("annotated_cases: 2"), "stdout:\n{stdout}");
    assert!(stdout.contains("matches: 2"), "stdout:\n{stdout}");
    assert!(stdout.contains("mismatches: 0"), "stdout:\n{stdout}");

    fs::remove_dir_all(&temp).expect("remove temporary stdlib root");
}
