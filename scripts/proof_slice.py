#!/usr/bin/env python3
"""Compile selected Lean dependencies and check exact proof suppliers.

Run as ``python3 -B -m scripts.proof_slice --help``. This development check
does not replace the complete-library census or integration build.
"""

import argparse
import fcntl
import json
import re
import tempfile
import time
from collections.abc import Sequence
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Literal

from scripts import build_private as build
from scripts import field_census as census

ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class ModuleAction:
    """Describe a module's required action against the current source graph."""

    name: str
    fingerprint: str
    action: Literal["reuse-output", "reuse-backend", "build"]


def select_modules(
    modules: dict[str, build.Module], roots: Sequence[str]
) -> list[build.Module]:
    """Select complete local dependency closures in build order."""
    chosen: set[str] = set()

    def visit(name: str) -> None:
        if name in chosen:
            return
        if name not in modules:
            raise build.BuildError(f"unknown selected module: {name}")
        chosen.add(name)
        for dependency in modules[name].imports:
            if dependency in modules:
                visit(dependency)

    for root in roots:
        visit(root)
    return [
        module for module in build.topological_order(modules) if module.name in chosen
    ]


def plan_modules(
    selected: Sequence[build.Module],
    fingerprints: dict[str, str],
    backend: Path,
    output: Path,
) -> list[ModuleAction]:
    """Reuse an object only when its complete source fingerprint matches."""
    cached = build.load_manifest(backend / build.MANIFEST_NAME)
    local = build.load_manifest(output / build.MANIFEST_NAME)
    result = []
    for module in selected:
        fingerprint = fingerprints[module.name]
        action: Literal["reuse-output", "reuse-backend", "build"] = "build"
        if (
            local.get(module.name) == fingerprint
            and build.output_path(output, module).is_file()
        ):
            action = "reuse-output"
        elif (
            cached.get(module.name) == fingerprint
            and build.output_path(backend, module).is_file()
        ):
            action = "reuse-backend"
        result.append(ModuleAction(module.name, fingerprint, action))
    return result


def audit_axioms(transcript: str, expected: Sequence[str]) -> dict[str, list[str]]:
    """Require exactly one standard-axiom report per requested declaration.

    >>> audit_axioms("'N.t' does not depend on any axioms", ['N.t'])
    {'N.t': []}
    """
    if census.unsafe_diagnostics(transcript) or re.search(
        r"^.*?error:", transcript, re.MULTILINE
    ):
        raise ValueError("unsafe proof diagnostics")
    if len(set(expected)) != len(expected):
        raise ValueError("duplicate requested audit declaration")
    pattern = (
        r"^'(.+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    )
    result = {}
    for match in re.finditer(pattern, transcript, re.MULTILINE):
        name = match.group(1)
        if name in result:
            raise ValueError(f"duplicate axiom report: {name}")
        axioms = [
            item.strip() for item in (match.group(2) or "").split(",") if item.strip()
        ]
        if not set(axioms) <= census.ALLOWED_AXIOMS:
            raise ValueError(f"nonstandard axioms for {name}: {axioms}")
        result[name] = axioms
    if set(result) != set(expected):
        raise ValueError("missing or unexpected axiom reports")
    return result


def audit_source(
    imports: Sequence[str],
    declarations: Sequence[str],
    field: str | None,
    supplier: str | None,
) -> str:
    """Use the existing census elaborator for explicit residual type checks."""
    source = "".join(f"import {name}\n" for name in sorted(set(imports)))
    if field is not None:
        if supplier is None:
            raise ValueError("field check requires a supplier")
        source += census.SUPPORT.read_text() + "\n"
        source += f"census_probe {census.STRUCTURE} {field} at {census.LAYOUT} using {supplier}\n"
    source += "".join(f"#print axioms {name}\n" for name in declarations)
    return source


def check_roots(repo: Path, backend: Path, output: Path) -> tuple[Path, Path]:
    """Keep the writable overlay outside the repository and source backend."""
    backend = backend.expanduser().resolve()
    output = build.validate_output_root(repo, output)
    if backend == output or backend in output.parents or output in backend.parents:
        raise build.BuildError("backend and output must be disjoint directories")
    if not (backend / build.MANIFEST_NAME).is_file():
        raise build.BuildError("backend has no build manifest")
    return backend, output


def execute(
    repo: Path,
    backend: Path,
    output: Path,
    imports: list[str],
    declarations: list[str],
    field: str | None,
    supplier: str | None,
    plan_only: bool,
) -> Path | None:
    """Build the selected closure, check proofs, and retain scoped evidence."""
    backend, output = check_roots(repo, backend, output)
    modules = build.discover_modules(repo, include_executable=True)
    order = build.topological_order(modules)
    fingerprints = build.module_fingerprints(repo, order, build.input_context(repo))
    selected = select_modules(modules, imports)
    actions = plan_modules(selected, fingerprints, backend, output)
    counts = {
        action: sum(item.action == action for item in actions)
        for action in ("reuse-output", "reuse-backend", "build")
    }
    print(json.dumps({"selected_modules": len(selected), **counts}), flush=True)
    if plan_only:
        for item in actions:
            if item.action == "build":
                print(f"build {item.name}")
        return None

    output.mkdir(parents=True, exist_ok=True)
    with (output / "proof-slice.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        # Another invocation may have completed between planning and locking.
        actions = plan_modules(selected, fingerprints, backend, output)
        run = Path(tempfile.mkdtemp(prefix="run-", dir=output))
        tool_inputs = [Path(__file__), census.SUPPORT, Path(census.__file__)]
        tool_hashes = {str(path): build.hash_file(path) for path in tool_inputs}
        manifest_path = output / build.MANIFEST_NAME
        manifest = build.load_manifest(manifest_path)
        objects: dict[str, str] = {}
        timings: dict[str, float] = {}
        for item in actions:
            module = modules[item.name]
            target = build.output_path(output, module)
            if item.action == "reuse-backend":
                target.parent.mkdir(parents=True, exist_ok=True)
                target.unlink(missing_ok=True)
                target.symlink_to(build.output_path(backend, module))
            elif item.action == "build":
                manifest.pop(item.name, None)
                build.write_manifest(manifest_path, manifest)
                print(f"build {item.name}", flush=True)
                started = time.monotonic()
                build.compile_module(repo, output, module)
                timings[item.name] = time.monotonic() - started
            manifest[item.name] = item.fingerprint
            build.write_manifest(manifest_path, manifest)
            objects[item.name] = build.hash_file(target)

        source = run / "Check.lean"
        source.write_text(audit_source(imports, declarations, field, supplier))
        result = census.run_lean(repo, output, source)
        if result.returncode != 0 or not source.with_suffix(".olean").is_file():
            raise build.BuildError(
                f"proof check failed; inspect {source.with_suffix('.log')}"
            )
        axioms = audit_axioms(result.output, declarations)
        field_result = None
        if field is not None:
            field_result = census.classify(census.Field(field, ""), result, True)
            if field_result.verdict != "FOUND":
                raise build.BuildError(f"invalid field evidence: {field_result}")

        current_modules = build.discover_modules(repo, include_executable=True)
        current = build.module_fingerprints(
            repo, build.topological_order(current_modules), build.input_context(repo)
        )
        for item in actions:
            if current.get(item.name) != item.fingerprint:
                raise build.BuildError(
                    f"source changed during proof check: {item.name}"
                )
            if (
                build.hash_file(build.output_path(output, modules[item.name]))
                != objects[item.name]
            ):
                raise build.BuildError(
                    f"object changed during proof check: {item.name}"
                )
        if any(
            build.hash_file(Path(path)) != digest
            for path, digest in tool_hashes.items()
        ):
            raise build.BuildError("proof-check tooling changed during run")
        report = {
            "scope": "selected dependency closure",
            "full_library_checked": False,
            "full_residual_coverage_checked": False,
            "imports": imports,
            "modules": [asdict(item) for item in actions],
            "objects_sha256": objects,
            "build_seconds": timings,
            "axioms": axioms,
            "field": asdict(field_result) if field_result is not None else None,
            "supplier": supplier,
            "tool_sha256": tool_hashes,
            "artifacts_sha256": {
                path.name: build.hash_file(path) for path in run.iterdir()
            },
        }
        receipt = run / "receipt.json"
        receipt.write_text(json.dumps(report, indent=2) + "\n")
        print(f"Checked slice: {receipt}", flush=True)
        return receipt


def main(argv: list[str] | None = None) -> int:
    """Run the scoped development check without changing the source backend."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--module", action="append", required=True, type=census.lean_identifier
    )
    parser.add_argument(
        "--audit", action="append", default=[], type=census.lean_identifier
    )
    parser.add_argument("--field", type=census.lean_identifier)
    parser.add_argument("--supplier", type=census.lean_identifier)
    parser.add_argument("--plan-only", action="store_true")
    args = parser.parse_args(argv)
    if (args.field is None) != (args.supplier is None):
        parser.error("--field and --supplier must be supplied together")
    if not args.plan_only and not args.audit and args.field is None:
        parser.error("request --audit or --field, or use --plan-only")
    if len(set(args.audit)) != len(args.audit):
        parser.error("duplicate --audit declaration")
    imports = list(args.module)
    if args.field is not None:
        imports += ["Vsa.Sim.TermAssembly", "Vsa.Sim.LayoutInstance"]
    try:
        execute(
            ROOT,
            args.backend,
            args.output,
            imports,
            args.audit,
            args.field,
            args.supplier,
            args.plan_only,
        )
    except (build.BuildError, OSError, ValueError) as error:
        print(f"proof slice failed: {error}")
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
