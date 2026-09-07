#!/usr/bin/env python3
"""Package 285 checked trace units without changing their Lean theorem bodies.

Run only after the serialized scratch campaign has completed. This program
validates every source/manifest/log/object before writing any repository file.
Scratch PASS records do not fingerprint backend imports; the packaged modules
still require the retained full-source integration gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import tempfile
from dataclasses import dataclass
from pathlib import Path

UNIT_COUNT = 285
PART_SIZE = 20
NAMESPACE = "Vsa.Sim.OutputAliasLoaded"
TARGET_MODULE = "Vsa.Sim.OutputAliasRun"
PART_ANNOTATION = (
    "-- discipline: allow(R7-conj-tower-def) Generated independent transition "
    "endpoints; each post is the named TraceHolds structure. Existentials "
    "bind reached configurations for Steps composition, not anonymous "
    "representation towers.\n"
)
ALLOWED_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
IMPORT = re.compile(rb"import ([A-Za-z_][A-Za-z_0-9.]*)\r?\n")
AXIOM_REPORT = re.compile(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]")
BAD_PROOF_TOKEN = re.compile(r"\b(?:sorryAx|sorry|native_decide|bv_decide)\b")
ERROR = re.compile(r"\berror\s*(?:\(|:)", re.IGNORECASE)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def read_json_object(path: Path) -> dict[str, object]:
    value = json.loads(path.read_text())
    require(isinstance(value, dict), f"{path}: expected JSON object")
    return value


@dataclass(frozen=True)
class PassRecord:
    fingerprint: str
    log: Path

    @classmethod
    def parse(cls, name: str, value: object) -> PassRecord:
        require(isinstance(value, dict), f"{name}: missing PASS manifest record")
        fp = value.get("fingerprint")
        log = value.get("log")
        require(
            isinstance(fp, str) and re.fullmatch("[0-9a-f]{64}", fp) is not None,
            f"{name}: invalid fingerprint",
        )
        require(isinstance(log, str), f"{name}: missing compiler log")
        # build_certificates.py writes a record only after exit 0 without
        # sorryAx and deletes failed entries. Its schema has no status field.
        require(value.get("status", "PASS") == "PASS", f"{name}: non-PASS status")
        return cls(fp, Path(log))


@dataclass(frozen=True)
class CheckedSource:
    name: str
    path: Path
    source: bytes
    imports: tuple[str, ...]
    body: bytes
    log: Path
    log_bytes: bytes
    object_file: Path
    fingerprint: str


def split_imports(source: bytes, label: str) -> tuple[tuple[str, ...], bytes]:
    """Remove only the contiguous import prefix; preserve all remaining bytes."""
    imports: list[str] = []
    offset = 0
    while match := IMPORT.match(source, offset):
        imports.append(match.group(1).decode("ascii"))
        offset = match.end()
    require(bool(imports), f"{label}: missing initial import block")
    body = source[offset:]
    require(
        re.search(rb"^\s*import\b", body, re.MULTILINE) is None,
        f"{label}: imports outside the initial block",
    )
    require(body.endswith(b"\n"), f"{label}: expected terminal newline")
    return tuple(imports), body


def check_source(
    name: str, scratch: Path, record: PassRecord, data_hash: str
) -> CheckedSource:
    path = scratch / f"{name}.lean"
    source = path.read_bytes()
    expected_fp = digest(source + data_hash.encode("ascii"))
    require(record.fingerprint == expected_fp, f"{name}: stale source/Data fingerprint")
    obj = scratch / f"{name}.olean"
    require(
        obj.is_file() and obj.stat().st_size > 0, f"{name}: compiled object missing"
    )
    expected_log = (scratch / f"{name}.log").resolve()
    require(record.log.resolve() == expected_log, f"{name}: unexpected log path")
    log_bytes = expected_log.read_bytes()
    text, log_text = source.decode("utf-8"), log_bytes.decode("utf-8")
    require(
        BAD_PROOF_TOKEN.search(text) is None, f"{name}: forbidden proof token in source"
    )
    require("sorryAx" not in log_text, f"{name}: sorryAx in compiler log")
    require(ERROR.search(log_text) is None, f"{name}: compiler error in log")
    require(
        re.search(r"^\s*(?:axiom|constant)\b", text, re.MULTILINE) is None,
        f"{name}: unproved declaration in source",
    )
    require(
        re.search(
            r"^\s*set_option\s+(?:maxRecDepth|maxHeartbeats)\b", text, re.MULTILINE
        )
        is None,
        f"{name}: proof-limit override in source",
    )
    require(
        text.count(f"namespace {NAMESPACE}\n") == 1
        and text.count(f"end {NAMESPACE}\n") == 1,
        f"{name}: unexpected namespace envelope",
    )
    reports = AXIOM_REPORT.findall(log_text)
    require(bool(reports), f"{name}: no compiler axiom audit")
    expected_theorem = (
        "traceStart"
        if name == "AliasTraceData"
        else "run" + name.removeprefix("AliasTrace")
    )
    expected_full_name = f"{NAMESPACE}.{expected_theorem}"
    require(
        sum(n == expected_full_name for n, _ in reports) == 1,
        f"{name}: missing/duplicate axiom audit for {expected_full_name}",
    )
    for theorem, raw_axioms in reports:
        axioms = {x.strip() for x in raw_axioms.split(",") if x.strip()}
        require(
            axioms <= ALLOWED_AXIOMS,
            f"{name}: unexpected axioms in {theorem}: {axioms}",
        )
    require(
        re.search(rf"^theorem {expected_theorem}\b", text, re.MULTILINE) is not None,
        f"{name}: expected theorem declaration missing",
    )
    imports, body = split_imports(source, name)
    return CheckedSource(
        name, path, source, imports, body, expected_log, log_bytes, obj, expected_fp
    )


def repository_import(repo: Path, module: str) -> bool:
    return (repo / (module.replace(".", "/") + ".lean")).is_file()


def atomic_write(path: Path, content: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        dir=path.parent, prefix=f".{path.name}.", delete=False
    ) as handle:
        temporary = Path(handle.name)
        handle.write(content)
    try:
        temporary.replace(path)
    finally:
        temporary.unlink(missing_ok=True)


def package(repo: Path, scratch: Path, receipt: Path) -> None:
    manifest_path = scratch / "build-manifest.json"
    manifest_bytes = manifest_path.read_bytes()
    manifest = read_json_object(manifest_path)
    data_bytes = (scratch / "AliasTraceData.lean").read_bytes()
    data_hash = digest(data_bytes)
    names = ["AliasTraceData"] + [f"AliasTrace{i:03}" for i in range(1, UNIT_COUNT + 1)]
    checked = [
        check_source(
            name, scratch, PassRecord.parse(name, manifest.get(name)), data_hash
        )
        for name in names
    ]
    data, *units = checked
    require(len(units) == UNIT_COUNT, "incomplete unit set")
    require(
        all(repository_import(repo, m) for m in data.imports),
        "Data imports must already exist in the repository",
    )
    destination = repo / "Vsa/Sim/OutputAliasRun"
    outputs: dict[Path, bytes] = {destination / "Data.lean": data.source}
    parts: list[dict[str, object]] = []
    for part_number, first in enumerate(range(0, UNIT_COUNT, PART_SIZE)):
        group = units[first : first + PART_SIZE]
        imports: set[str] = set()
        for unit in group:
            require(
                "AliasTraceData" in unit.imports, f"{unit.name}: missing Data import"
            )
            for module in unit.imports:
                if module == "AliasTraceData":
                    imports.add(TARGET_MODULE + ".Data")
                else:
                    require(
                        not module.startswith("AliasTrace"),
                        f"{unit.name}: unexpected scratch cross-import {module}",
                    )
                    require(
                        repository_import(repo, module),
                        f"{unit.name}: nonrepository import {module}",
                    )
                    imports.add(module)
        header = "".join(f"import {m}\n" for m in sorted(imports)).encode("utf-8")
        header += PART_ANNOTATION.encode("utf-8")
        # Keep the complete namespace/open/declaration blocks byte for byte.
        # Repeated namespace blocks preserve each source's original scope.
        content = header + b"".join(unit.body for unit in group)
        part_name = f"Part{part_number:02}"
        outputs[destination / f"{part_name}.lean"] = content
        parts.append(
            {
                "module": f"{TARGET_MODULE}.{part_name}",
                "first_unit": first + 1,
                "last_unit": first + len(group),
                "units": [unit.name for unit in group],
                "body_sha256": {unit.name: digest(unit.body) for unit in group},
                "imports": sorted(imports),
            }
        )
    require(len(parts) == 15 and len(outputs) == 16, "unexpected package layout")

    # Validate all inputs first, then recheck the complete snapshot immediately
    # before the first repository write. An active/incomplete campaign fails.
    require(
        manifest_path.read_bytes() == manifest_bytes,
        "manifest changed during validation",
    )
    for unit in checked:
        require(
            unit.path.read_bytes() == unit.source,
            f"{unit.name}: source changed during validation",
        )
        require(
            unit.log.read_bytes() == unit.log_bytes,
            f"{unit.name}: log changed during validation",
        )
        require(
            unit.object_file.is_file(),
            f"{unit.name}: object disappeared during validation",
        )
    for path, content in outputs.items():
        if not path.exists() or path.read_bytes() != content:
            atomic_write(path, content)
    package_receipt = {
        "schema": "vsa-output-alias-package-v1",
        "scratch_pass_records_checked": len(checked),
        "unit_pass_records_checked": UNIT_COUNT,
        "pass_semantics": "build_certificates.py records only exit-0 compilations without sorryAx",
        "fingerprint_formula": "sha256(source_bytes + sha256(Data_source_bytes).hexdigest().encode())",
        "scratch_manifest_sha256": digest(manifest_bytes),
        "data_copied_byte_for_byte": True,
        "unit_bodies_preserved_byte_for_byte": True,
        "part_header_annotation": PART_ANNOTATION,
        "namespace": NAMESPACE,
        "backend_fingerprints_in_scratch_manifest": False,
        "packaged_repository_imports_compiled": False,
        "required_next_gate": "retained full-source integration build",
        "sources": {
            u.name: {
                "source_sha256": digest(u.source),
                "compiler_log_sha256": digest(u.log_bytes),
                "build_fingerprint": u.fingerprint,
            }
            for u in checked
        },
        "outputs": {str(p.relative_to(repo)): digest(c) for p, c in outputs.items()},
        "parts": parts,
    }
    atomic_write(receipt, (json.dumps(package_receipt, indent=2) + "\n").encode())
    print(f"Packaged {UNIT_COUNT} checked units into Data + {len(parts)} Parts.")
    print(
        f"Receipt: {receipt}; packaged modules still require the full integration build."
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path.cwd())
    parser.add_argument(
        "--scratch",
        type=Path,
        default=Path("/private/tmp/vsa-alias-loaded/certificates"),
    )
    parser.add_argument(
        "--receipt",
        type=Path,
        default=Path("/private/tmp/vsa-alias-loaded/package-receipt.json"),
    )
    args = parser.parse_args()
    repo = args.repo.resolve()
    require(
        (repo / "Vsa/Sim/OutputAliasLoaded.lean").is_file(),
        "not the expected repository",
    )
    package(repo, args.scratch.resolve(), args.receipt.resolve())


if __name__ == "__main__":
    main()
