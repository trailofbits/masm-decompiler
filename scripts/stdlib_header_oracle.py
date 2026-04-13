#!/usr/bin/env python3
"""Compare decompiled headers against annotated stdlib procedure signatures.

This is a corpus oracle for the local type inference rewrite. It walks MASM
files under a stdlib root, finds annotated `pub proc` declarations, expands
source-level aliases such as `u64` and `word` into primitive stack shapes, runs
the decompiler CLI for each procedure, and compares the rendered header shape.

The script is intentionally conservative:
- only annotated public procedures are considered oracle cases
- unsupported rendered shapes are reported as mismatches
- variable names are ignored; only type shapes are compared
"""

from __future__ import annotations

import argparse
import dataclasses
import re
import subprocess
import sys
from pathlib import Path
from typing import Iterable


PUB_PROC_RE = re.compile(
    r"^\s*pub proc\s+(?P<name>[A-Za-z0-9_]+)\((?P<inputs>.*?)\)\s*(?:->\s*(?P<outputs>.*))?$"
)
RENDERED_HEADER_RE = re.compile(
    r"^(?:pub\s+)?proc\s+(?P<name>[A-Za-z0-9_]+)\((?P<inputs>.*?)\)\s*(?:->\s*(?P<outputs>.*?))?\s*\{?$"
)


class OracleError(RuntimeError):
    """Raised when the oracle cannot parse an expected or rendered header."""


@dataclasses.dataclass(frozen=True)
class RawOracleCase:
    """One annotated public procedure from the stdlib before type expansion."""

    file_path: Path
    module_path: str
    fq_proc_name: str
    proc_name: str
    raw_inputs: str
    raw_outputs: str
    source_header: str


@dataclasses.dataclass(frozen=True)
class OracleCase:
    """One annotated public procedure from the stdlib after type expansion."""

    file_path: Path
    module_path: str
    fq_proc_name: str
    proc_name: str
    expected_inputs: tuple[str, ...]
    expected_outputs: tuple[str, ...]
    source_header: str


@dataclasses.dataclass(frozen=True)
class OracleResult:
    """Result of running one oracle case."""

    case: OracleCase
    actual_inputs: tuple[str, ...] | None
    actual_outputs: tuple[str, ...] | None
    rendered_header: str | None
    error: str | None

    @property
    def matches(self) -> bool:
        return (
            self.error is None
            and self.actual_inputs == self.case.expected_inputs
            and self.actual_outputs == self.case.expected_outputs
        )


def split_top_level_csv(text: str) -> list[str]:
    """Split a comma-separated list while respecting nested delimiters."""

    items: list[str] = []
    depth = 0
    start = 0
    for index, ch in enumerate(text):
        if ch in "(<[":
            depth += 1
        elif ch in ")>]":
            depth = max(0, depth - 1)
        elif ch == "," and depth == 0:
            items.append(text[start:index].strip())
            start = index + 1
    tail = text[start:].strip()
    if tail:
        items.append(tail)
    return items


def primitive_alias_tokens(type_name: str) -> tuple[str, ...]:
    """Expand one source-level stdlib alias into primitive header tokens."""

    mapping: dict[str, tuple[str, ...]] = {
        "i1": ("Bool",),
        "u8": ("U32",),
        "u32": ("U32",),
        "u64": ("U32", "U32"),
        "u128": ("U32", "U32", "U32", "U32"),
        "u256": (
            "U32",
            "U32",
            "U32",
            "U32",
            "U32",
            "U32",
            "U32",
            "U32",
        ),
        "word": ("Felt", "Felt", "Felt", "Felt"),
        "felt": ("Felt",),
    }
    try:
        return mapping[type_name]
    except KeyError as exc:
        raise OracleError(f"unsupported source annotation `{type_name}`") from exc


def normalize_source_signature(portion: str) -> tuple[str, ...]:
    """Normalize a source MASM signature portion to primitive type tokens."""

    text = portion.strip()
    if not text:
        return ()
    if text.startswith("(") and text.endswith(")"):
        text = text[1:-1].strip()
    if not text:
        return ()

    normalized: list[str] = []
    for item in split_top_level_csv(text):
        annotation = item
        if ":" in item:
            _, annotation = item.split(":", 1)
        normalized.extend(primitive_alias_tokens(annotation.strip()))
    return tuple(normalized)


def normalize_rendered_signature(portion: str) -> tuple[str, ...]:
    """Normalize one rendered decompiler header portion to primitive tokens."""

    text = portion.strip()
    if not text:
        return ()
    if text.startswith("(") and text.endswith(")"):
        text = text[1:-1].strip()
    if not text:
        return ()

    normalized: list[str] = []
    for item in split_top_level_csv(text):
        token = item.strip()
        if ":" in token:
            _, token = token.split(":", 1)
            token = token.strip()
        if token.startswith("Word<") and token.endswith(">"):
            inner = token[5:-1]
            normalized.extend(normalize_rendered_signature(inner))
            continue
        if token in {"Felt", "U32", "Bool", "Unknown"}:
            normalized.append(token)
            continue
        if token.startswith("Unknown(") and token.endswith(")"):
            normalized.append("Unknown")
            continue
        raise OracleError(f"unsupported rendered type token `{token}`")
    return tuple(normalized)


def positive_int_arg(value: str) -> int:
    """Parse a strictly positive integer CLI argument."""

    parsed = int(value)
    if parsed <= 0:
        raise argparse.ArgumentTypeError("value must be a positive integer")
    return parsed


def derive_module_path(stdlib_root: Path, file_path: Path, namespace: str) -> str:
    """Derive a fully-qualified MASM module path from a stdlib source file."""

    relative = file_path.relative_to(stdlib_root)
    parts = list(relative.parts)
    if not parts:
        raise OracleError(f"could not derive module path for `{file_path}`")
    file_name = parts.pop()
    if file_name == "mod.masm":
        stem = parts.pop() if parts else "mod"
    else:
        stem = Path(file_name).stem
    module_parts = [namespace] if namespace else []
    module_parts.extend(parts)
    module_parts.append(stem)
    return "::".join(module_parts)


def iter_oracle_cases(
    stdlib_root: Path, namespace: str, limit: int | None = None
) -> Iterable[RawOracleCase]:
    """Yield annotated public procedure headers from a stdlib root."""

    yielded = 0
    for file_path in sorted(stdlib_root.rglob("*.masm")):
        module_path = derive_module_path(stdlib_root, file_path, namespace)
        for line in file_path.read_text().splitlines():
            match = PUB_PROC_RE.match(line)
            if not match:
                continue
            if ":" not in line and "->" not in line:
                continue
            yield RawOracleCase(
                file_path=file_path,
                module_path=module_path,
                fq_proc_name=f"{module_path}::{match.group('name')}",
                proc_name=match.group("name"),
                raw_inputs=match.group("inputs"),
                raw_outputs=match.group("outputs") or "",
                source_header=line.strip(),
            )
            yielded += 1
            if limit is not None and yielded >= limit:
                return


def build_oracle_case(raw_case: RawOracleCase) -> OracleCase:
    """Expand a raw annotated stdlib case into primitive expected shapes."""

    return OracleCase(
        file_path=raw_case.file_path,
        module_path=raw_case.module_path,
        fq_proc_name=raw_case.fq_proc_name,
        proc_name=raw_case.proc_name,
        expected_inputs=normalize_source_signature(raw_case.raw_inputs),
        expected_outputs=normalize_source_signature(raw_case.raw_outputs),
        source_header=raw_case.source_header,
    )


def infer_namespace(stdlib_root: Path) -> str:
    """Infer the MASM namespace for a stdlib `asm` tree."""

    project_file = stdlib_root / "miden-project.toml"
    if project_file.exists():
        for line in project_file.read_text().splitlines():
            if line.strip().startswith("namespace"):
                _, value = line.split("=", 1)
                return value.strip().strip('"')
    parent_project = stdlib_root.parent / "miden-project.toml"
    if parent_project.exists():
        for line in parent_project.read_text().splitlines():
            if line.strip().startswith("namespace"):
                _, value = line.split("=", 1)
                return value.strip().strip('"')
    raise OracleError(f"could not infer namespace from `{stdlib_root}`")


def run_decompiler(
    repo_root: Path, stdlib_root: Path, namespace: str, case: OracleCase
) -> OracleResult:
    """Run the decompiler CLI for one procedure and capture its rendered header."""

    command = [
        "cargo",
        "run",
        "--",
        "--no-color",
        "--trusted-library",
        f"{namespace}={stdlib_root}",
        "--procedure",
        case.fq_proc_name,
        str(case.file_path),
    ]
    proc = subprocess.run(
        command,
        cwd=repo_root,
        text=True,
        capture_output=True,
        check=False,
    )
    if proc.returncode != 0:
        return OracleResult(case, None, None, None, proc.stderr.strip() or proc.stdout.strip())

    header = None
    for line in proc.stdout.splitlines():
        stripped = line.strip()
        if stripped.startswith("proc ") or stripped.startswith("pub proc "):
            header = stripped
            break
    if header is None:
        return OracleResult(case, None, None, None, "missing rendered procedure header")

    match = RENDERED_HEADER_RE.match(header)
    if not match:
        return OracleResult(case, None, None, header, f"unparsed rendered header: {header}")

    try:
        inputs = normalize_rendered_signature(match.group("inputs"))
        outputs = normalize_rendered_signature(match.group("outputs") or "")
    except OracleError as exc:
        return OracleResult(case, None, None, header, str(exc))
    return OracleResult(case, inputs, outputs, header, None)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path("."),
        help="Path to the masm-decompiler checkout to evaluate (default: current directory).",
    )
    parser.add_argument(
        "--stdlib-root",
        type=Path,
        required=True,
        help="Path to the stdlib asm root, e.g. /path/to/miden-vm/crates/lib/core/asm.",
    )
    parser.add_argument(
        "--limit",
        type=positive_int_arg,
        default=None,
        help="Only evaluate the first N annotated procedures.",
    )
    parser.add_argument(
        "--show-passes",
        action="store_true",
        help="Print matching cases as well as mismatches.",
    )
    args = parser.parse_args()

    repo_root = args.repo_root.resolve()
    stdlib_root = args.stdlib_root.resolve()
    namespace = infer_namespace(stdlib_root)

    raw_cases = list(iter_oracle_cases(stdlib_root, namespace, args.limit))
    if not raw_cases:
        raise SystemExit("no annotated public procedures found")

    results: list[OracleResult] = []
    for raw_case in raw_cases:
        try:
            case = build_oracle_case(raw_case)
        except OracleError as exc:
            results.append(
                OracleResult(
                    case=OracleCase(
                        file_path=raw_case.file_path,
                        module_path=raw_case.module_path,
                        fq_proc_name=raw_case.fq_proc_name,
                        proc_name=raw_case.proc_name,
                        expected_inputs=(),
                        expected_outputs=(),
                        source_header=raw_case.source_header,
                    ),
                    actual_inputs=None,
                    actual_outputs=None,
                    rendered_header=None,
                    error=str(exc),
                )
            )
            continue
        results.append(run_decompiler(repo_root, stdlib_root, namespace, case))
    failures = [result for result in results if not result.matches]

    print(f"repo: {repo_root}")
    print(f"stdlib: {stdlib_root}")
    print(f"namespace: {namespace}")
    print(f"annotated_cases: {len(results)}")
    print(f"matches: {len(results) - len(failures)}")
    print(f"mismatches: {len(failures)}")
    print()

    for result in results:
        if result.matches and not args.show_passes:
            continue
        print(f"{result.case.file_path.relative_to(stdlib_root)}::{result.case.proc_name}")
        print(f"  source:   {result.case.source_header}")
        if result.rendered_header is not None:
            print(f"  rendered: {result.rendered_header}")
        if result.error is not None:
            print(f"  error:    {result.error}")
        else:
            print(f"  expected: {result.case.expected_inputs} -> {result.case.expected_outputs}")
            print(f"  actual:   {result.actual_inputs} -> {result.actual_outputs}")
        print()

    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
