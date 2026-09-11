#!/usr/bin/env python3
"""Record and measure immutable Lean attempt receipts.

Receipts describe attempts.  They are not proof certificates and never suppress a run.
Only receipts with complete, stable comparison inputs receive a comparison key.
"""

from __future__ import annotations

import argparse
import base64
import binascii
import hashlib
import json
import math
import os
import re
import shutil
import subprocess
import tempfile
import uuid
from collections import Counter
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path

try:
    from scripts import build_private
except ModuleNotFoundError:  # invoked as a script
    import build_private  # type: ignore[no-redef]

SCHEMA = "vsa.lean-attempt.v1"
FAILURE_CLASSES = (
    "success",
    "deterministic_heartbeat_timeout",
    "wall_clock_timeout",
    "explicit_transient_failure",
    "stale_or_missing_dependency",
    "compiler_diagnostic",
    "invocation_error",
)
HASH = re.compile(r"[0-9a-f]{64}\Z")
HEARTBEAT = re.compile(
    r"deterministic\) timeout|maximum number of heartbeats|heartbeat limit", re.I
)
STALE_INPUT = re.compile(
    r"stale private backend|object file .* does not exist|missing dependency", re.I
)
TRANSIENT = re.compile(
    r"connection reset|broken pipe|network unreachable|resource temporarily unavailable|"
    r"compiler lock (?:held|busy)|interrupted|killed by signal",
    re.I,
)
_FILE_HASH_CACHE: dict[tuple[str, int, int, int, int, int], str] = {}


@dataclass(frozen=True)
class Blob:
    """Exact UTF-8 bytes and their digest."""

    utf8_base64: str
    sha256: str
    bytes: int

    @classmethod
    def from_text(cls, text: str) -> Blob:
        raw = text.encode("utf-8")
        return cls(
            utf8_base64=base64.b64encode(raw).decode("ascii"),
            sha256=hashlib.sha256(raw).hexdigest(),
            bytes=len(raw),
        )


@dataclass(frozen=True)
class FileFingerprint:
    """A regular file fingerprint, or an explicit reason it was unavailable."""

    path: str
    resolved_path: str | None
    sha256: str | None
    bytes: int | None
    error: str | None


@dataclass(frozen=True)
class DependencyFingerprint:
    """Current source, expected build fingerprint, and backend artifact evidence."""

    module: str
    source: FileFingerprint
    expected_fingerprint: str
    manifest_fingerprint: str | None
    object: FileFingerprint
    current: bool


@dataclass(frozen=True)
class ArtifactInventory:
    """A deterministic aggregate fingerprint for a named file inventory."""

    name: str
    root: str
    sha256: str | None
    files: int
    bytes: int
    error: str | None


@dataclass(frozen=True)
class BuildSnapshot:
    """Toolchain and complete local import-closure evidence at one instant."""

    captured_at: str
    imported_modules: tuple[str, ...]
    input_context_sha256: str | None
    toolchain: tuple[FileFingerprint, ...]
    backend_manifest: FileFingerprint
    dependencies: tuple[DependencyFingerprint, ...]
    external_imports: tuple[str, ...]
    environment_artifacts: tuple[ArtifactInventory, ...]
    inherited_lean_path: str | None
    problems: tuple[str, ...]


@dataclass(frozen=True)
class CandidateInput:
    """One generated theorem target, statement, and candidate body."""

    target: str
    theorem: str
    label: str
    statement: Blob
    candidate: Blob


def utc_now() -> str:
    """Return a receipt timestamp in UTC."""
    return datetime.now(timezone.utc).isoformat()


def fingerprint_file(path: Path) -> FileFingerprint:
    """Fingerprint a regular file without treating missing input as hashable evidence."""
    absolute = path.absolute()
    try:
        resolved = absolute.resolve(strict=True)
        if not resolved.is_file():
            return FileFingerprint(
                str(absolute), str(resolved), None, None, "not a regular file"
            )
        stat = resolved.stat()
        cache_key = (
            str(resolved),
            stat.st_dev,
            stat.st_ino,
            stat.st_size,
            stat.st_mtime_ns,
            stat.st_ctime_ns,
        )
        digest = _FILE_HASH_CACHE.get(cache_key)
        if digest is None:
            hasher = hashlib.sha256()
            with resolved.open("rb") as stream:
                for block in iter(lambda: stream.read(1024 * 1024), b""):
                    hasher.update(block)
                after = os.fstat(stream.fileno())
            after_key = (
                str(resolved),
                after.st_dev,
                after.st_ino,
                after.st_size,
                after.st_mtime_ns,
                after.st_ctime_ns,
            )
            if after_key != cache_key:
                return FileFingerprint(
                    str(absolute),
                    str(resolved),
                    None,
                    None,
                    "file changed while it was fingerprinted",
                )
            digest = hasher.hexdigest()
            _FILE_HASH_CACHE[cache_key] = digest
    except OSError as error:
        return FileFingerprint(
            str(absolute), None, None, None, f"{type(error).__name__}: {error}"
        )
    return FileFingerprint(str(absolute), str(resolved), digest, stat.st_size, None)


def artifact_inventory(
    name: str, root: Path, paths: tuple[Path, ...]
) -> ArtifactInventory:
    """Aggregate exact bytes and relative names for a deterministic file set."""
    root = root.absolute()
    chosen = sorted(set(path.absolute() for path in paths), key=lambda path: str(path))
    if not chosen:
        return ArtifactInventory(
            name, str(root), None, 0, 0, "empty artifact inventory"
        )
    digest = hashlib.sha256()
    total = 0
    for path in chosen:
        try:
            relative = path.relative_to(root)
        except ValueError:
            return ArtifactInventory(
                name, str(root), None, 0, 0, f"artifact outside inventory root: {path}"
            )
        item = fingerprint_file(path)
        if item.sha256 is None or item.bytes is None:
            return ArtifactInventory(
                name,
                str(root),
                None,
                0,
                0,
                f"artifact unavailable: {path}: {item.error}",
            )
        digest.update(relative.as_posix().encode("utf-8"))
        digest.update(b"\0")
        digest.update(item.sha256.encode("ascii"))
        digest.update(b"\n")
        total += item.bytes
    return ArtifactInventory(
        name, str(root), digest.hexdigest(), len(chosen), total, None
    )


def _regular_files(root: Path) -> tuple[Path, ...]:
    if not root.is_dir():
        return ()
    return tuple(path for path in root.rglob("*") if path.is_file())


def _resolve_elan_tool(repo: Path, command: str) -> tuple[Path | None, str | None]:
    """Resolve an elan-managed binary without launching the resolved tool."""
    try:
        result = subprocess.run(
            ["elan", "which", command],
            cwd=repo,
            capture_output=True,
            text=True,
            check=False,
            timeout=15,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        return None, f"elan which {command} failed: {error}"
    lines = [line.strip() for line in result.stdout.splitlines() if line.strip()]
    if result.returncode != 0 or len(lines) != 1:
        detail = (result.stderr or result.stdout).strip()
        return None, f"elan which {command} returned {result.returncode}: {detail}"
    path = Path(lines[0]).absolute()
    if not path.is_file():
        return None, f"elan which {command} returned no regular file: {path}"
    return path, None


def _package_artifacts(
    repo: Path,
) -> tuple[tuple[ArtifactInventory, ...], tuple[str, ...]]:
    """Fingerprint compiled libraries and configs for top-manifest package entries."""
    manifest_path = repo / "lake-manifest.json"
    try:
        raw = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError, UnicodeError) as error:
        return (), (f"Lake package manifest unavailable: {error}",)
    if not isinstance(raw, dict):
        return (), ("Lake package manifest is not an object",)
    packages_dir = raw.get("packagesDir")
    packages = raw.get("packages")
    if not isinstance(packages_dir, str) or not isinstance(packages, list):
        return (), ("Lake package manifest has unsupported structure",)
    inventories = []
    problems = []
    seen: set[str] = set()
    for entry in packages:
        if not isinstance(entry, dict):
            problems.append("Lake package manifest contains a non-object entry")
            continue
        kind, name = entry.get("type"), entry.get("name")
        if not isinstance(name, str) or not name or name in seen:
            problems.append(
                "Lake package manifest contains a missing or duplicate name"
            )
            continue
        seen.add(name)
        if kind == "git":
            package = repo / packages_dir / name.replace("«", "").replace("»", "")
        elif kind == "path" and isinstance(entry.get("dir"), str):
            package = repo / entry["dir"]
        else:
            problems.append(f"Lake package {name} has unsupported type or path")
            continue
        package = package.resolve()
        config_name = entry.get("configFile")
        if not isinstance(config_name, str) or not config_name:
            problems.append(f"Lake package {name} has no config file declaration")
            continue
        compiled = package / ".lake/build/lib/lean"
        compiled_files = _regular_files(compiled)
        if not compiled_files:
            problems.append(f"Lake package {name} has no compiled library artifacts")
        paths = list(compiled_files)
        paths.append(package / config_name)
        for optional in ("lean-toolchain", "lake-manifest.json"):
            path = package / optional
            if path.is_file():
                paths.append(path)
        inventory = artifact_inventory(f"lake-package:{name}", package, tuple(paths))
        inventories.append(inventory)
        if inventory.sha256 is None:
            problems.append(
                f"Lake package {name} artifacts unavailable: {inventory.error}"
            )
    return tuple(inventories), tuple(problems)


def _dependency_closure(
    modules: dict[str, build_private.Module], roots: tuple[str, ...]
) -> tuple[str, ...]:
    chosen: set[str] = set()

    def visit(name: str) -> None:
        if name in chosen or name not in modules:
            return
        chosen.add(name)
        for dependency in modules[name].imports:
            visit(dependency)

    for root in roots:
        visit(root)
    return tuple(
        module.name
        for module in build_private.topological_order(modules)
        if module.name in chosen
    )


def capture_build_snapshot(
    repo: Path,
    backend: Path,
    generated_source: str,
    inherited_lean_path: str | None = None,
    extra_tool_paths: tuple[Path, ...] = (),
) -> BuildSnapshot:
    """Capture configured toolchain and complete local dependency build evidence."""
    problems: list[str] = []
    tool_paths = [
        repo / "lean-toolchain",
        repo / "lakefile.toml",
        repo / "lake-manifest.json",
        Path(build_private.__file__),
        Path(__file__),
        *extra_tool_paths,
    ]
    executable_paths: dict[str, Path] = {}
    for command in ("lean", "lake", "elan"):
        executable = shutil.which(command)
        if executable is None and command != "elan":
            problems.append(f"{command} executable is not discoverable")
        elif executable is not None:
            executable_paths[command] = Path(executable).absolute()
            tool_paths.append(Path(executable))
    lean_executable = executable_paths.get("lean")
    lake_executable = executable_paths.get("lake")
    elan_executable = executable_paths.get("elan")
    lean_is_shim = False
    if lean_executable is not None:
        lean_is_shim = (
            lean_executable.parent.name == "bin"
            and lean_executable.parent.parent.name == ".elan"
        )
        if elan_executable is not None:
            try:
                lean_is_shim = lean_is_shim or lean_executable.samefile(elan_executable)
            except OSError:
                pass
    actual_lean, actual_lake = lean_executable, lake_executable
    if lean_is_shim:
        if elan_executable is None:
            problems.append("actual Lean compiler is unresolved behind an elan shim")
        else:
            actual_lean, error = _resolve_elan_tool(repo, "lean")
            if error is not None:
                problems.append(error)
            actual_lake, error = _resolve_elan_tool(repo, "lake")
            if error is not None:
                problems.append(error)
            for path in (actual_lean, actual_lake):
                if path is not None:
                    tool_paths.append(path)
    toolchain = tuple(
        fingerprint_file(path)
        for path in dict.fromkeys(path.absolute() for path in tool_paths)
    )
    for item in toolchain:
        if item.sha256 is None:
            problems.append(f"toolchain input unavailable: {item.path}: {item.error}")
    if inherited_lean_path is None:
        problems.append("LEAN_PATH environment was not captured")
    elif inherited_lean_path:
        problems.append("inherited LEAN_PATH is not fingerprinted")

    environment_artifacts: list[ArtifactInventory] = []
    if actual_lean is None:
        problems.append("actual Lean compiler path is unavailable")
    else:
        toolchain_root = actual_lean.parent.parent
        toolchain_library = toolchain_root / "lib/lean"
        inventory = artifact_inventory(
            "lean-toolchain-lib", toolchain_library, _regular_files(toolchain_library)
        )
        environment_artifacts.append(inventory)
        if inventory.sha256 is None:
            problems.append(f"Lean toolchain artifacts unavailable: {inventory.error}")
    packages, package_problems = _package_artifacts(repo)
    environment_artifacts.extend(packages)
    problems.extend(package_problems)

    manifest_path = backend / build_private.MANIFEST_NAME
    manifest_file = fingerprint_file(manifest_path)
    manifest: dict[str, str] = {}
    if manifest_file.sha256 is None:
        problems.append(f"backend manifest unavailable: {manifest_file.error}")
    else:
        try:
            manifest = build_private.load_manifest(manifest_path)
        except (build_private.BuildError, OSError, UnicodeError) as error:
            problems.append(f"backend manifest invalid: {error}")

    dependencies: tuple[DependencyFingerprint, ...] = ()
    external_imports: tuple[str, ...] = ()
    input_context: str | None = None
    imports = build_private.parse_header_imports(generated_source)
    try:
        modules = build_private.discover_modules(repo, include_executable=True)
        order = build_private.topological_order(modules)
        input_context = build_private.input_context(repo)
        expected = build_private.module_fingerprints(repo, order, input_context)
        local_roots = tuple(name for name in imports if name in modules)
        missing_roots = tuple(
            name for name in imports if name.startswith("Vsa") and name not in modules
        )
        if missing_roots:
            problems.append(f"unknown local imports: {', '.join(missing_roots)}")
        selected = _dependency_closure(modules, local_roots)
        external_imports = tuple(
            sorted(
                {
                    dependency
                    for name in selected
                    for dependency in modules[name].imports
                    if dependency not in modules
                }
            )
        )
        found = []
        for name in selected:
            module = modules[name]
            source = fingerprint_file(repo / module.source)
            object_ = fingerprint_file(build_private.output_path(backend, module))
            current = (
                source.sha256 is not None
                and object_.sha256 is not None
                and manifest.get(name) == expected[name]
            )
            if not current:
                problems.append(f"dependency build is missing or stale: {name}")
            found.append(
                DependencyFingerprint(
                    module=name,
                    source=source,
                    expected_fingerprint=expected[name],
                    manifest_fingerprint=manifest.get(name),
                    object=object_,
                    current=current,
                )
            )
        dependencies = tuple(found)
    except (build_private.BuildError, OSError, UnicodeError) as error:
        problems.append(f"dependency inventory unavailable: {error}")

    return BuildSnapshot(
        captured_at=utc_now(),
        imported_modules=imports,
        input_context_sha256=input_context,
        toolchain=toolchain,
        backend_manifest=manifest_file,
        dependencies=dependencies,
        external_imports=external_imports,
        environment_artifacts=tuple(environment_artifacts),
        inherited_lean_path=inherited_lean_path,
        problems=tuple(problems),
    )


def _snapshot_identity(snapshot: BuildSnapshot) -> dict[str, object] | None:
    if (
        snapshot.problems
        or snapshot.input_context_sha256 is None
        or not snapshot.dependencies
    ):
        return None
    toolchain = {
        item.path: item.sha256 for item in snapshot.toolchain if item.sha256 is not None
    }
    if len(toolchain) != len(snapshot.toolchain):
        return None
    dependencies = {
        item.module: item.expected_fingerprint for item in snapshot.dependencies
    }
    objects = {
        item.module: item.object.sha256
        for item in snapshot.dependencies
        if item.object.sha256 is not None
    }
    if len(objects) != len(snapshot.dependencies):
        return None
    environment = {
        item.name: item.sha256
        for item in snapshot.environment_artifacts
        if item.sha256 is not None
    }
    if (
        not environment
        or len(environment) != len(snapshot.environment_artifacts)
        or len(environment)
        != len({item.name for item in snapshot.environment_artifacts})
    ):
        return None
    return {
        "input_context_sha256": snapshot.input_context_sha256,
        "toolchain_fingerprints": toolchain,
        "dependency_fingerprints": dependencies,
        "dependency_object_sha256": objects,
        "external_imports": list(snapshot.external_imports),
        "environment_artifact_fingerprints": environment,
        "inherited_lean_path": snapshot.inherited_lean_path,
    }


def has_stale_inputs(snapshot: BuildSnapshot) -> bool:
    """Return whether snapshot evidence explicitly identifies stale build inputs."""
    prefixes = (
        "backend manifest unavailable:",
        "backend manifest invalid:",
        "unknown local imports:",
        "dependency build is missing or stale:",
        "dependency inventory unavailable:",
    )
    return any(problem.startswith(prefixes) for problem in snapshot.problems)


def comparison_payload(
    targets: tuple[str, ...],
    source: Blob,
    candidates: tuple[CandidateInput, ...],
    snapshot: BuildSnapshot,
) -> dict[str, object] | None:
    """Return complete attempt identity, or ``None`` for incomplete inputs."""
    build = _snapshot_identity(snapshot)
    if (
        not targets
        or len(set(targets)) != len(targets)
        or not candidates
        or build is None
    ):
        return None
    return {
        "schema": SCHEMA,
        "targets": list(targets),
        "generated_source_sha256": source.sha256,
        "candidates": [
            {
                "target": item.target,
                "theorem": item.theorem,
                "label": item.label,
                "statement_sha256": item.statement.sha256,
                "candidate_sha256": item.candidate.sha256,
            }
            for item in candidates
        ],
        **build,
    }


def comparison_key(payload: object) -> str | None:
    """Hash a complete canonical identity; reject missing or unencodable metadata."""
    if not isinstance(payload, dict):
        return None
    required = {
        "schema",
        "targets",
        "generated_source_sha256",
        "candidates",
        "input_context_sha256",
        "toolchain_fingerprints",
        "dependency_fingerprints",
        "dependency_object_sha256",
        "external_imports",
        "environment_artifact_fingerprints",
        "inherited_lean_path",
    }
    if set(payload) != required or payload.get("schema") != SCHEMA:
        return None
    if not isinstance(payload.get("targets"), list) or not payload["targets"]:
        return None
    if not isinstance(payload.get("candidates"), list) or not payload["candidates"]:
        return None
    hashes = [
        payload.get("generated_source_sha256"),
        payload.get("input_context_sha256"),
    ]
    for name in (
        "toolchain_fingerprints",
        "dependency_fingerprints",
        "dependency_object_sha256",
        "environment_artifact_fingerprints",
    ):
        values = payload.get(name)
        if not isinstance(values, dict) or not values:
            return None
        hashes.extend(values.values())
    candidates = payload["candidates"]
    if not all(
        isinstance(item, dict)
        and set(item)
        == {"target", "theorem", "label", "statement_sha256", "candidate_sha256"}
        and all(
            isinstance(item[name], str) and item[name]
            for name in ("target", "theorem", "label")
        )
        and isinstance(item["statement_sha256"], str)
        and isinstance(item["candidate_sha256"], str)
        and HASH.fullmatch(item["statement_sha256"]) is not None
        and HASH.fullmatch(item["candidate_sha256"]) is not None
        for item in candidates
    ):
        return None
    if not all(isinstance(item, str) and item for item in payload["targets"]):
        return None
    if not isinstance(payload.get("external_imports"), list) or not all(
        isinstance(item, str) and item for item in payload["external_imports"]
    ):
        return None
    if not all(isinstance(item, str) and HASH.fullmatch(item) for item in hashes):
        return None
    if not isinstance(payload.get("inherited_lean_path"), str):
        return None
    try:
        encoded = json.dumps(
            payload,
            ensure_ascii=False,
            allow_nan=False,
            sort_keys=True,
            separators=(",", ":"),
        ).encode("utf-8")
    except (TypeError, ValueError):
        return None
    return hashlib.sha256(encoded).hexdigest()


def classify_result(returncode: int | None, diagnostics: str) -> str:
    """Classify only explicit process state and diagnostic evidence."""
    if returncode is None:
        return "wall_clock_timeout"
    if TRANSIENT.search(diagnostics):
        return "explicit_transient_failure"
    if HEARTBEAT.search(diagnostics):
        return "deterministic_heartbeat_timeout"
    if STALE_INPUT.search(diagnostics):
        return "stale_or_missing_dependency"
    unsafe = "sorryAx" in diagnostics or re.search(
        r"declaration uses [`'](?:sorry|admit)[`']", diagnostics
    )
    if (
        returncode == 0
        and not unsafe
        and not re.search(r"^.*?error(?:\([^)]*\))?:", diagnostics, re.M)
    ):
        return "success"
    return "compiler_diagnostic"


def classify_exception(error: BaseException) -> str:
    """Classify a caught invocation exception from its explicit type and message."""
    detail = str(error)
    if isinstance(error, TimeoutError):
        return "wall_clock_timeout"
    if isinstance(error, (KeyboardInterrupt, InterruptedError)):
        return "explicit_transient_failure"
    if STALE_INPUT.search(detail):
        return "stale_or_missing_dependency"
    if TRANSIENT.search(detail):
        return "explicit_transient_failure"
    return "invocation_error"


def write_receipt(directory: Path, receipt: dict[str, object]) -> Path:
    """Publish a new read-only receipt without replacing an earlier receipt."""
    directory.mkdir(parents=True, exist_ok=True)
    encoded = (
        json.dumps(receipt, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    ).encode()
    stamp = re.sub(r"[^0-9A-Za-z._-]", "_", str(receipt["started_at"]))
    destination = directory / f"attempt-{stamp}-{uuid.uuid4().hex}.json"
    with tempfile.NamedTemporaryFile(
        prefix=".attempt-", dir=directory, delete=False
    ) as stream:
        temporary = Path(stream.name)
        try:
            stream.write(encoded)
            stream.flush()
            os.fsync(stream.fileno())
            temporary.chmod(0o444)
            os.link(temporary, destination)
        finally:
            temporary.unlink(missing_ok=True)
    return destination


def make_receipt(
    *,
    targets: tuple[str, ...],
    source: Blob,
    candidates: tuple[CandidateInput, ...],
    before: BuildSnapshot,
    after: BuildSnapshot,
    started_at: str,
    finished_at: str,
    wall_seconds: float,
    returncode: int | None,
    diagnostics: str,
    failure_class: str,
    rerun_reason: str | None,
    capture_before_seconds: float = 0.0,
    capture_after_seconds: float = 0.0,
) -> dict[str, object]:
    """Construct one receipt and withhold comparability when inputs drifted."""
    if failure_class not in FAILURE_CLASSES:
        raise ValueError(f"unknown attempt failure class: {failure_class}")
    timings = (wall_seconds, capture_before_seconds, capture_after_seconds)
    if not all(math.isfinite(seconds) and seconds >= 0 for seconds in timings):
        raise ValueError("attempt timings must be finite nonnegative numbers")
    if rerun_reason is not None and not rerun_reason.strip():
        raise ValueError("rerun reason must contain text when supplied")
    diagnostics_blob = Blob.from_text(diagnostics)
    before_payload = comparison_payload(targets, source, candidates, before)
    after_payload = comparison_payload(targets, source, candidates, after)
    stable = before_payload is not None and before_payload == after_payload
    key = comparison_key(before_payload) if stable else None
    problems = list(before.problems)
    problems.extend(problem for problem in after.problems if problem not in problems)
    if before_payload is not None and after_payload is not None and not stable:
        problems.append("comparison inputs changed during the attempt")
    if before_payload is None and not problems:
        problems.append("comparison metadata is incomplete")
    return {
        "schema": SCHEMA,
        "started_at": started_at,
        "finished_at": finished_at,
        "timing_scope": "environment capture is separate from the Lean invocation",
        "timing_seconds": {
            "environment_capture_before": capture_before_seconds,
            "lean_wall": wall_seconds,
            "environment_capture_after": capture_after_seconds,
        },
        "targets": list(targets),
        "rerun_reason": rerun_reason,
        "generated": {
            "source": asdict(source),
            "candidates": [asdict(candidate) for candidate in candidates],
        },
        "build_before": asdict(before),
        "build_after": asdict(after),
        "result": {
            "returncode": returncode,
            "failure_class": failure_class,
            "diagnostics": asdict(diagnostics_blob),
            "diagnostics_sha256": diagnostics_blob.sha256,
            "diagnostics_bytes": diagnostics_blob.bytes,
        },
        "comparison": before_payload if stable else None,
        "comparable_key": key,
        "non_comparable_reasons": problems if key is None else [],
    }


def _blob_digest(value: object) -> tuple[str, int] | None:
    if not isinstance(value, dict) or set(value) != {"utf8_base64", "sha256", "bytes"}:
        return None
    encoded, digest, size = (
        value.get("utf8_base64"),
        value.get("sha256"),
        value.get("bytes"),
    )
    if (
        not isinstance(encoded, str)
        or not isinstance(digest, str)
        or HASH.fullmatch(digest) is None
        or not isinstance(size, int)
        or isinstance(size, bool)
        or size < 0
    ):
        return None
    try:
        raw = base64.b64decode(encoded, validate=True)
    except (binascii.Error, ValueError):
        return None
    if len(raw) != size or hashlib.sha256(raw).hexdigest() != digest:
        return None
    return digest, size


def _file_digest(value: object) -> tuple[str, str] | None:
    required = {"path", "resolved_path", "sha256", "bytes", "error"}
    if not isinstance(value, dict) or set(value) != required:
        return None
    path, resolved, digest = (
        value.get("path"),
        value.get("resolved_path"),
        value.get("sha256"),
    )
    size, error = value.get("bytes"), value.get("error")
    if (
        not isinstance(path, str)
        or not path
        or not isinstance(resolved, str)
        or not resolved
        or not isinstance(digest, str)
        or HASH.fullmatch(digest) is None
        or not isinstance(size, int)
        or isinstance(size, bool)
        or size < 0
        or error is not None
    ):
        return None
    return path, digest


def _build_identity_json(value: object) -> dict[str, object] | None:
    required = {
        "captured_at",
        "imported_modules",
        "input_context_sha256",
        "toolchain",
        "backend_manifest",
        "dependencies",
        "external_imports",
        "environment_artifacts",
        "inherited_lean_path",
        "problems",
    }
    if not isinstance(value, dict) or set(value) != required:
        return None
    context = value.get("input_context_sha256")
    imported = value.get("imported_modules")
    external = value.get("external_imports")
    inherited = value.get("inherited_lean_path")
    if (
        not isinstance(value.get("captured_at"), str)
        or not isinstance(context, str)
        or HASH.fullmatch(context) is None
        or not isinstance(imported, list)
        or not imported
        or not all(isinstance(item, str) and item for item in imported)
        or not isinstance(external, list)
        or not all(isinstance(item, str) and item for item in external)
        or not isinstance(inherited, str)
        or value.get("problems") != []
        or _file_digest(value.get("backend_manifest")) is None
    ):
        return None

    raw_tools = value.get("toolchain")
    if not isinstance(raw_tools, list) or not raw_tools:
        return None
    toolchain: dict[str, str] = {}
    for raw_tool in raw_tools:
        item = _file_digest(raw_tool)
        if item is None or item[0] in toolchain:
            return None
        toolchain[item[0]] = item[1]

    raw_dependencies = value.get("dependencies")
    if not isinstance(raw_dependencies, list) or not raw_dependencies:
        return None
    dependencies: dict[str, str] = {}
    objects: dict[str, str] = {}
    dependency_keys = {
        "module",
        "source",
        "expected_fingerprint",
        "manifest_fingerprint",
        "object",
        "current",
    }
    for raw_dependency in raw_dependencies:
        if (
            not isinstance(raw_dependency, dict)
            or set(raw_dependency) != dependency_keys
        ):
            return None
        module = raw_dependency.get("module")
        expected = raw_dependency.get("expected_fingerprint")
        manifest = raw_dependency.get("manifest_fingerprint")
        source = _file_digest(raw_dependency.get("source"))
        object_ = _file_digest(raw_dependency.get("object"))
        if (
            not isinstance(module, str)
            or not module
            or module in dependencies
            or not isinstance(expected, str)
            or HASH.fullmatch(expected) is None
            or manifest != expected
            or source is None
            or object_ is None
            or raw_dependency.get("current") is not True
        ):
            return None
        dependencies[module] = expected
        objects[module] = object_[1]

    raw_artifacts = value.get("environment_artifacts")
    if not isinstance(raw_artifacts, list) or not raw_artifacts:
        return None
    artifacts: dict[str, str] = {}
    artifact_keys = {"name", "root", "sha256", "files", "bytes", "error"}
    for raw_artifact in raw_artifacts:
        if not isinstance(raw_artifact, dict) or set(raw_artifact) != artifact_keys:
            return None
        name, root, digest = (
            raw_artifact.get("name"),
            raw_artifact.get("root"),
            raw_artifact.get("sha256"),
        )
        files, size = raw_artifact.get("files"), raw_artifact.get("bytes")
        if (
            not isinstance(name, str)
            or not name
            or name in artifacts
            or not isinstance(root, str)
            or not root
            or not isinstance(digest, str)
            or HASH.fullmatch(digest) is None
            or not isinstance(files, int)
            or isinstance(files, bool)
            or files <= 0
            or not isinstance(size, int)
            or isinstance(size, bool)
            or size < 0
            or raw_artifact.get("error") is not None
        ):
            return None
        artifacts[name] = digest
    return {
        "input_context_sha256": context,
        "toolchain_fingerprints": toolchain,
        "dependency_fingerprints": dependencies,
        "dependency_object_sha256": objects,
        "external_imports": external,
        "environment_artifact_fingerprints": artifacts,
        "inherited_lean_path": inherited,
    }


def _receipt_comparison(value: dict[str, object]) -> dict[str, object] | None:
    targets = value.get("targets")
    generated = value.get("generated")
    if (
        not isinstance(targets, list)
        or not targets
        or not all(isinstance(item, str) and item for item in targets)
        or not isinstance(generated, dict)
        or set(generated) != {"source", "candidates"}
    ):
        return None
    source = _blob_digest(generated.get("source"))
    raw_candidates = generated.get("candidates")
    if source is None or not isinstance(raw_candidates, list) or not raw_candidates:
        return None
    candidates = []
    candidate_keys = {"target", "theorem", "label", "statement", "candidate"}
    for raw_candidate in raw_candidates:
        if not isinstance(raw_candidate, dict) or set(raw_candidate) != candidate_keys:
            return None
        target, theorem, label = (
            raw_candidate.get("target"),
            raw_candidate.get("theorem"),
            raw_candidate.get("label"),
        )
        statement = _blob_digest(raw_candidate.get("statement"))
        candidate = _blob_digest(raw_candidate.get("candidate"))
        if (
            not isinstance(target, str)
            or not target
            or not isinstance(theorem, str)
            or not theorem
            or not isinstance(label, str)
            or not label
            or statement is None
            or candidate is None
        ):
            return None
        candidates.append(
            {
                "target": target,
                "theorem": theorem,
                "label": label,
                "statement_sha256": statement[0],
                "candidate_sha256": candidate[0],
            }
        )
    before = _build_identity_json(value.get("build_before"))
    after = _build_identity_json(value.get("build_after"))
    if before is None or before != after:
        return None
    return {
        "schema": SCHEMA,
        "targets": targets,
        "generated_source_sha256": source[0],
        "candidates": candidates,
        **before,
    }


def _valid_result(value: object) -> str | None:
    required = {
        "returncode",
        "failure_class",
        "diagnostics",
        "diagnostics_sha256",
        "diagnostics_bytes",
    }
    if not isinstance(value, dict) or set(value) != required:
        return None
    failure_class = value.get("failure_class")
    diagnostics = _blob_digest(value.get("diagnostics"))
    returncode = value.get("returncode")
    if (
        failure_class not in FAILURE_CLASSES
        or diagnostics is None
        or value.get("diagnostics_sha256") != diagnostics[0]
        or value.get("diagnostics_bytes") != diagnostics[1]
        or not (
            returncode is None
            or (isinstance(returncode, int) and not isinstance(returncode, bool))
        )
    ):
        return None
    return str(failure_class)


def measure_receipts(directory: Path) -> dict[str, object]:
    """Count comparable duplicate attempts without treating them as cache entries."""
    valid: list[tuple[Path, str, str]] = []
    invalid = []
    non_comparable = []
    paths = sorted(directory.rglob("attempt-*.json")) if directory.exists() else []
    for path in paths:
        try:
            raw = json.loads(path.read_text(encoding="utf-8"))
        except (json.JSONDecodeError, OSError, UnicodeError) as error:
            invalid.append({"path": str(path), "error": str(error)})
            continue
        if not isinstance(raw, dict) or raw.get("schema") != SCHEMA:
            invalid.append({"path": str(path), "error": "unsupported receipt schema"})
            continue
        top_level = {
            "schema",
            "started_at",
            "finished_at",
            "timing_scope",
            "timing_seconds",
            "targets",
            "rerun_reason",
            "generated",
            "build_before",
            "build_after",
            "result",
            "comparison",
            "comparable_key",
            "non_comparable_reasons",
        }
        if set(raw) != top_level:
            invalid.append({"path": str(path), "error": "malformed receipt fields"})
            continue
        if raw.get("comparison") is None and raw.get("comparable_key") is None:
            reasons = raw.get("non_comparable_reasons")
            if (
                not isinstance(reasons, list)
                or not reasons
                or not all(isinstance(reason, str) and reason for reason in reasons)
            ):
                invalid.append(
                    {"path": str(path), "error": "missing non-comparable reason"}
                )
            else:
                non_comparable.append({"path": str(path), "reasons": reasons})
            continue
        claimed = raw.get("comparison")
        key = comparison_key(claimed)
        reconstructed = _receipt_comparison(raw)
        if key is None or raw.get("comparable_key") != key or reconstructed != claimed:
            invalid.append({"path": str(path), "error": "comparison evidence mismatch"})
            continue
        if raw.get("non_comparable_reasons") != []:
            invalid.append(
                {"path": str(path), "error": "comparable receipt has caveats"}
            )
            continue
        failure_class = _valid_result(raw.get("result"))
        if failure_class is None:
            invalid.append({"path": str(path), "error": "invalid result"})
            continue
        valid.append((path, key, failure_class))
    counts = Counter(key for _, key, _ in valid)
    failures = Counter(key for _, key, cls in valid if cls != "success")
    duplicate_groups = [
        {
            "comparable_key": key,
            "count": count,
            "receipts": [str(path) for path, item, _ in valid if item == key],
        }
        for key, count in sorted(counts.items())
        if count > 1
    ]
    return {
        "schema": SCHEMA,
        "receipt_files": len(paths),
        "comparable_receipts": len(valid),
        "non_comparable_receipts": len(non_comparable),
        "non_comparable": non_comparable,
        "comparable_failed_receipts": sum(cls != "success" for _, _, cls in valid),
        "duplicate_groups": duplicate_groups,
        "duplicate_attempts_beyond_first": sum(count - 1 for count in counts.values()),
        "duplicate_failed_attempts_beyond_first": sum(
            count - 1 for count in failures.values()
        ),
        "invalid_receipts": invalid,
    }


def main(argv: list[str] | None = None) -> int:
    """Print duplicate measurements for a receipt directory."""
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("directory", type=Path)
    args = parser.parse_args(argv)
    print(json.dumps(measure_receipts(args.directory), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
