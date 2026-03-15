# High-level Guidelines

- Do not write code before stating assumptions.
- Do not claim correctness you haven't verified.
- Do not handle only the happy path.
- Always state under what conditions the implementation works.
- Do not commit or push code unless explicitly asked to.

# Design Constraints

The only thing the end user sees is the final textual output from the
decompiler. If this does not 100% reflect the semantics of the corresponding
assembly, it is worse than useless, as it may be misleading. _Always_ strive to
ensure that the textual output accurately reflects the semantics of the
procedure being decompiled.

You must review the `ARCHITECTURE.md` file to understand the overall design and
design constraints of the decompiler.

New analysis passes and bug fixes in existing code must always preserve the
semantics of the procedure being analyzed. It is never sufficient that the code
does the right thing in "most" cases.

When encountering unsupported patterns, return an error or `Unknown` result
variant (e.g. `ProcSignature::Unknown`) rather than producing incorrect output.

# Development guidelines

- Prefer Rust idioms and best practices. Implement standard traits for types
  (e.g. `From`, `TryFrom`, and `Display`) rather than custom methods or functions.
- Maintain modularity and separation of concerns. Avoid large functions, types,
  and modules that do too many things.
- Keep the main `lib.rs` and `main.rs` minimal. Implement functionality in their own
  submodules.
- Write unit tests for all new functionality. Use property-based testing with
  `proptest` where applicable. Take care to design tests that will detect any
  potential issues and fail if the implementation is incorrect.
- Use documentation comments (`///`) for _all_ types and functions. Documentation
  should be brief and to the point.
- Do not add or remove variants from the `Stmt` enum unless explicitly asked to.
- If an instruction variants or code pattern is not supported, return an error or
  `Unknown` result variant (e.g. `ProcSignature::Unknown`) rather than producing
  a best-effort output.
- Errors and `Unknown` results should be explicit and informative, and must
  indicate what pattern was unsupported and the location (typically an instruction
  span) where it occurred.

# Testing

- Tests fixtures are defined in `tests/fixtures` and test harnesses (e.g. for
  property testing) are defined in `tests/common`.
- Whenever the user provides an example MASM procedure that is handled
  incorrectly by the decompilation pipeline, ensure that the example is recorded
  in one of the files under `tests/fixtures`. If it is not there, add it to an
  existing file, or create a new file and add it there. Then analyze the output
  from the decompiler carefully to understand how the issue manifests itself.
  Review the implementation carefully to understand why decompilation fails. Add a
  targeted test that tests for the correct behavior. This test should initially
  fail, because the underlying issue is not fixed yet. Finally, describe your
  findings to the user, including the root cause and a suggestion for addressing
  it.

# Debugging

The decompiler supports logging that can be enabled using the `RUST_LOG`
environment variable. To run the decompiler on a file, use the command:

```sh
cargo run -- --no-color path/to/file.masm
```

Note the `--no-color` flag which can be used to disable color output. To
decompile individual procedures, use the `--procedure` argument.

```sh
cargo run -- --no-color --procedure proc_name path/to/file.masm
```

To decompile files that import modules from other libraries, use the `--library`
flag to specify the path to the library root. For example, to decompile files
inside the examples folder that import other modules from the Miden stdlib, use
the following command:

```sh
cargo run -- --no-color --library miden::core=examples/core examples/core/path/to/file.masm
```

Finally, use the `--no-dce`, `--no-propagation`, and `--no-simplification` to
disable individual optimization passes. This can be useful to see the initial
output from the decompiler, before optimizations are applied.
