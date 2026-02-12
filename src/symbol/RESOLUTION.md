# Symbol Resolution

This document describes how symbol resolution works in `src/symbol/resolution.rs`,
including strict error semantics and constant-resolution support.

## Goals

- Resolve MASM symbols in module context to fully-qualified paths (`SymbolPath`).
- Return explicit errors for unresolved/invalid references.
- Avoid producing misleading synthetic targets.
- Support constant-specific resolution for LSP hover/peek workflows.

## Non-goals

- This layer does not auto-load missing modules into `Workspace`.
- This layer does not return AST definition nodes directly (only resolved paths).
- This layer does not validate dynamic/MAST-root targets as callable procedures.

## Important Types

- `SymbolPath` (`src/symbol/path.rs`):
  - Normalized fully-qualified path wrapper.
  - Used for modules, procedures, and constants.

- `ResolutionError` (`src/symbol/resolution.rs`):
  - `ModuleNotLoaded { module }`:
    - Workspace context module (or resolved target module during constant checking) is not loaded.
  - `SymbolResolution { module, reference, source }`:
    - Underlying `LocalSymbolResolver` failed to resolve the reference.
  - `NonPathResolution { module, reference }`:
    - Resolved target is not representable as a path (e.g. `MastRoot`).
  - `NonConstantSymbol { module, reference, resolved }`:
    - Constant resolution succeeded to a symbol path, but that symbol is not a constant definition.

- `SymbolResolver<'a>`:
  - Reusable module-local resolver wrapping `LocalSymbolResolver`.

- `WorkspaceSymbolResolver`:
  - Workspace-scoped resolution trait used by analyses (e.g. signature inference).

## Public APIs

- Module-level:
  - `resolve_target(module, source_manager, target) -> Result<Option<SymbolPath>, ResolutionError>`
  - `resolve_symbol(module, source_manager, name) -> Result<SymbolPath, ResolutionError>`
  - `resolve_path(module, source_manager, path) -> Result<SymbolPath, ResolutionError>`

- Workspace-level:
  - `WorkspaceSymbolResolver::{resolve_target, resolve_symbol, resolve_path}` with strict `Result` returns.

- Constant-specific:
  - `resolve_constant_symbol(workspace, module, name) -> Result<SymbolPath, ResolutionError>`
  - `resolve_constant_path(workspace, module, path) -> Result<SymbolPath, ResolutionError>`
  - Both APIs require resolved symbols to exist in `Workspace` constant index.

## Resolution Flow

### 1) Invocation Target Resolution

`resolve_target` behavior:

- `InvocationTarget::MastRoot(_)`:
  - Returns `Ok(None)`.
- `InvocationTarget::Symbol(name)`:
  - Resolves through `LocalSymbolResolver::resolve`.
  - Converts resolved item to `SymbolPath`.
- `InvocationTarget::Path(path)`:
  - Resolves through `LocalSymbolResolver::resolve_path`.
  - Converts resolved item to `SymbolPath`.

Callers that require a concrete callable target typically treat:

- `Ok(Some(path))` as direct call target.
- `Ok(None)` or `Err(_)` as unknown/opaque target.

### 2) Symbol Name Resolution

`resolve_symbol`:

- Uses `LocalSymbolResolver::resolve`.
- On success, converts `SymbolResolution` to `SymbolPath`.
- On failure, returns `ResolutionError::SymbolResolution`.
- No fallback synthesis is used.

### 3) Path Resolution

`resolve_path`:

- Absolute paths (`::...`) are accepted directly.
- Otherwise uses `LocalSymbolResolver::resolve_path`.
- Special case:
  - If resolver returns `UndefinedSymbol` and the input is a qualified non-absolute path
    (e.g. `leaf::callee`), the path is treated as an explicit external path and returned as-is.
  - This is not a generic fallback; it only applies to this exact unresolved qualified-path case.
- Other failures return `ResolutionError::SymbolResolution`.

Rationale:

- MASM allows explicit external qualified invoke targets even without a local alias/import match.

### 4) Constant Resolution

`resolve_constant_symbol` and `resolve_constant_path`:

1. Resolve the reference to a `SymbolPath` using strict workspace APIs.
2. Validate the resolved path via `ensure_constant_target`:
   - If `Workspace::lookup_constant_entry(resolved)` succeeds, return resolved path.
   - Else if target module is missing, return `ModuleNotLoaded`.
   - Else return `NonConstantSymbol`.

## Workspace Integration

`Workspace` maintains:

- `proc_index: HashMap<SymbolPath, (module_idx, proc_idx)>`
- `const_index: HashMap<SymbolPath, (module_idx, const_idx)>`

Indexing occurs when programs are added/loaded. Constant lookup APIs:

- `lookup_constant_entry(&SymbolPath) -> Option<(&Program, &Constant)>`
- `lookup_constant(&str) -> Option<&Constant>`

## Error Semantics

Strictness policy:

- Unqualified unresolved names are errors.
- Invalid subpaths/type mismatches from underlying resolver are errors.
- Non-path targets are explicit errors (`NonPathResolution`) for symbol/path resolution.
- Constant APIs reject non-constant symbols (`NonConstantSymbol`).

Notably, callers may intentionally downgrade resolver errors to conservative outcomes (`Unknown`/`Opaque`),
but resolution itself is strict and does not fabricate local/module-relative paths.

## Typical LSP Constant Hover/Peek Flow

Given `(workspace, current_module_path, hovered_token)`:

1. Resolve constant:
   - `resolve_constant_symbol(...)` for bare name.
   - `resolve_constant_path(...)` for qualified path token.
2. Fetch definition:
   - `workspace.lookup_constant_entry(&resolved_path)`.
3. Use returned `Constant` span/docs/value for hover or definition target.

If resolution fails, return no result and surface the specific `ResolutionError` for diagnostics/logging.

## Missing Functionality / Known Limitations

- No dedicated procedure-only resolution API:
  - There is constant-specific validation, but no symmetric `resolve_procedure_*` helper.

- No unified definition-object API:
  - Resolution returns paths; callers still need `Workspace` lookups to obtain AST nodes.

- No module auto-loading during resolution:
  - If a target module is not loaded, callers get `ModuleNotLoaded`.

- External qualified paths may be unresolved against loaded workspace content:
  - `resolve_path` can return an explicit external path for valid MASM syntax even if the module/item
    is not present locally. Consumers that require existence must validate via workspace lookup.

- Callers frequently downgrade errors:
  - Some analyses intentionally collapse resolver errors to `Unknown`/`Opaque` behavior. This is safe,
    but loses diagnostic detail unless explicitly logged or propagated.
