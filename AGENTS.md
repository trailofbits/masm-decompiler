# High-level Guidelines

- Do not write code before stating assumptions.
- Do not claim correctness you haven't verified.
- Do not handle only the happy path.
- Always state under what conditions the implementation works.
- Do not commit or push code unless explicitly asked to.

# Design Constraints

You must review the `ARCHITECTURE.md` file to understand the overall design and
design constraints of the decompiler.

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
