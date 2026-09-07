#!/usr/bin/env python3
"""Build current Lean sources serially into a private olean tree."""

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path


TOOL_VERSION = "1"
MANIFEST_NAME = "build-private-manifest.json"


class BuildError(Exception):
    """Report an invalid graph, configuration, or Lean compilation."""


@dataclass(frozen=True)
class Module:
    """Describe one local Lean module and its local imports."""

    name: str
    source: Path
    imports: tuple[str, ...]


def strip_comments(text: str) -> str:
    r"""Remove nested Lean block comments and line comments.

    >>> strip_comments('import A /- outer /- inner -/ end -/\nimport B -- note')
    'import A \nimport B '
    """
    result: list[str] = []
    index = 0
    depth = 0
    while index < len(text):
        pair = text[index : index + 2]
        if pair == "/-":
            depth += 1
            index += 2
        elif pair == "-/" and depth:
            depth -= 1
            index += 2
        elif depth:
            if text[index] == "\n":
                result.append("\n")
            index += 1
        elif pair == "--":
            newline = text.find("\n", index)
            if newline == -1:
                break
            result.append("\n")
            index = newline + 1
        else:
            result.append(text[index])
            index += 1
    if depth:
        raise BuildError("unterminated Lean block comment")
    return "".join(result)


def parse_header_imports(text: str) -> tuple[str, ...]:
    r"""Parse imports before the first non-import Lean command.

    >>> parse_header_imports('import A.B Vsa.Code.«__divdi3»\n/- x -/\nnamespace N')
    ('A.B', 'Vsa.Code.__divdi3')
    """
    imports: list[str] = []
    for line in strip_comments(text).splitlines():
        words = line.split()
        if not words:
            continue
        if words[0] != "import":
            break
        imports.extend(word.replace("«", "").replace("»", "") for word in words[1:])
    return tuple(imports)


def module_name(source: Path) -> str:
    """Convert a repository-relative Lean source path to a module name."""
    return ".".join(source.with_suffix("").parts)


def discover_modules(repo: Path, include_executable: bool = False) -> dict[str, Module]:
    """Discover current Vsa library modules and parse their imports."""
    sources = sorted((repo / "Vsa").rglob("*.lean")) + [repo / "Vsa.lean"]
    if include_executable:
        sources.append(repo / "VsaRun.lean")
    modules: dict[str, Module] = {}
    for source in sources:
        relative = source.relative_to(repo)
        name = module_name(relative)
        imports = parse_header_imports(source.read_text(encoding="utf-8"))
        modules[name] = Module(name, relative, imports)
    for module in modules.values():
        for dependency in module.imports:
            if dependency.startswith("Vsa") and dependency not in modules:
                raise BuildError(
                    f"{module.source}: unknown internal import {dependency}"
                )
    return modules


def topological_order(modules: dict[str, Module]) -> list[Module]:
    """Return a stable dependency-first order and reject import cycles."""
    order: list[Module] = []
    state: dict[str, int] = {}

    def visit(name: str, trail: tuple[str, ...]) -> None:
        match state.get(name, 0):
            case 2:
                return
            case 1:
                cycle = " -> ".join((*trail, name))
                raise BuildError(f"internal import cycle: {cycle}")
        state[name] = 1
        module = modules[name]
        for dependency in sorted(module.imports):
            if dependency in modules:
                visit(dependency, (*trail, name))
        state[name] = 2
        order.append(module)

    for name in sorted(modules):
        visit(name, ())
    return order


def validate_output_root(repo: Path, output_root: Path) -> Path:
    """Resolve and require an output directory outside the repository."""
    resolved_repo = repo.resolve()
    resolved_output = output_root.expanduser().resolve()
    if resolved_output == resolved_repo or resolved_repo in resolved_output.parents:
        raise BuildError(f"output root must be outside repository: {resolved_output}")
    return resolved_output


def hash_file(path: Path) -> str:
    """Return the SHA-256 digest of a file, or a stable missing marker."""
    if not path.exists():
        return "missing"
    return hashlib.sha256(path.read_bytes()).hexdigest()


def input_context(repo: Path) -> str:
    """Fingerprint project and tool inputs outside the Lean import graph."""
    inputs = [
        Path(__file__),
        repo / "lakefile.toml",
        repo / "lake-manifest.json",
        repo / "lean-toolchain",
    ]
    payload = "\n".join(f"{path.name}:{hash_file(path)}" for path in inputs)
    return hashlib.sha256(f"{TOOL_VERSION}\n{payload}".encode()).hexdigest()


def module_fingerprints(
    repo: Path, order: list[Module], context: str
) -> dict[str, str]:
    """Fingerprint each source and its complete local dependency state."""
    fingerprints: dict[str, str] = {}
    for module in order:
        dependencies = [
            f"{name}:{fingerprints[name]}"
            for name in sorted(module.imports)
            if name in fingerprints
        ]
        payload = "\n".join([context, hash_file(repo / module.source), *dependencies])
        fingerprints[module.name] = hashlib.sha256(payload.encode()).hexdigest()
    return fingerprints


def load_manifest(path: Path) -> dict[str, str]:
    """Parse a prior tool manifest into typed module fingerprints."""
    if not path.exists():
        return {}
    try:
        raw = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as err:
        raise BuildError(f"invalid resume manifest {path}: {err}") from err
    if not isinstance(raw, dict) or raw.get("tool_version") != TOOL_VERSION:
        return {}
    entries = raw.get("modules")
    if not isinstance(entries, dict):
        raise BuildError(f"invalid resume manifest modules: {path}")
    if not all(
        isinstance(key, str) and isinstance(value, str)
        for key, value in entries.items()
    ):
        raise BuildError(f"invalid resume manifest entry: {path}")
    return dict(entries)


def write_manifest(path: Path, entries: dict[str, str]) -> None:
    """Atomically record successful module fingerprints."""
    temporary = path.with_suffix(".tmp")
    payload = {"tool_version": TOOL_VERSION, "modules": entries}
    temporary.write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    temporary.replace(path)


def output_path(output_root: Path, module: Module) -> Path:
    """Return the private olean path for a module."""
    return output_root / module.source.with_suffix(".olean")


def log_path(output_root: Path, module: Module) -> Path:
    """Return the private log path for a module."""
    return output_root / "logs" / f"{module.name.replace('.', '_')}.log"


def compile_module(repo: Path, output_root: Path, module: Module) -> None:
    """Compile one module through `lake env` and reject unsafe proof warnings."""
    output = output_path(output_root, module)
    log = log_path(output_root, module)
    output.parent.mkdir(parents=True, exist_ok=True)
    log.parent.mkdir(parents=True, exist_ok=True)
    shell = 'LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}" lean -o "$2" "$3"'
    with tempfile.TemporaryDirectory(
        prefix=f".{output.stem}-", dir=output.parent
    ) as staging:
        staged = Path(staging) / output.name
        result = subprocess.run(
            [
                "lake",
                "env",
                "sh",
                "-c",
                shell,
                "build-private",
                str(output_root),
                str(staged),
                str(module.source),
            ],
            cwd=repo,
            capture_output=True,
            text=True,
            check=False,
        )
        transcript = result.stdout + result.stderr
        log.write_text(transcript, encoding="utf-8")
        if result.returncode != 0:
            raise BuildError(f"Lean failed for {module.source}; see {log}")
        if "sorryAx" in transcript or re.search(
            r"declaration uses [`'](?:sorry|admit)[`']", transcript
        ):
            raise BuildError(f"unsafe proof reported for {module.source}; see {log}")
        if not staged.is_file():
            raise BuildError(f"Lean produced no object for {module.source}; see {log}")
        staged.replace(output)


def build(
    repo: Path,
    output_root: Path,
    *,
    include_executable: bool,
    list_only: bool,
    resume: bool,
) -> None:
    """Build or list all current modules in deterministic dependency order."""
    modules = discover_modules(repo, include_executable)
    order = topological_order(modules)
    if list_only:
        for module in order:
            print(module.source)
        return
    output_root.mkdir(parents=True, exist_ok=True)
    manifest_path = output_root / MANIFEST_NAME
    prior = load_manifest(manifest_path) if resume else {}
    fingerprints = module_fingerprints(repo, order, input_context(repo))
    completed: dict[str, str] = {}
    retained = dict(prior)
    for index, module in enumerate(order, start=1):
        fingerprint = fingerprints[module.name]
        if (
            resume
            and prior.get(module.name) == fingerprint
            and output_path(output_root, module).is_file()
        ):
            completed[module.name] = fingerprint
            print(f"[{index}/{len(order)}] skip {module.source}", flush=True)
            continue
        print(f"[{index}/{len(order)}] build {module.source}", flush=True)
        # Invalidate before installing an object. An interruption between object
        # installation and fingerprint publication must not reuse the old hash.
        retained.pop(module.name, None)
        write_manifest(manifest_path, retained)
        compile_module(repo, output_root, module)
        completed[module.name] = fingerprint
        retained[module.name] = fingerprint
        write_manifest(manifest_path, retained)
    write_manifest(manifest_path, completed)


def parse_args(argv: list[str]) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--include-executable", action="store_true")
    parser.add_argument("--list", action="store_true", dest="list_only")
    parser.add_argument("--resume", action="store_true")
    return parser.parse_args(argv)


def main(argv: list[str] | None = None) -> int:
    """Run the private build command."""
    args = parse_args(sys.argv[1:] if argv is None else argv)
    repo = Path(__file__).resolve().parents[1]
    try:
        output_root = validate_output_root(repo, args.output_root)
        build(
            repo,
            output_root,
            include_executable=args.include_executable,
            list_only=args.list_only,
            resume=args.resume,
        )
    except BuildError as err:
        print(f"build_private: {err}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
