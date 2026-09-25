#!/usr/bin/env python3
"""Find checked suppliers for every inherited residual field.

Uses the complete current private backend. A search miss does not establish
that no supplier exists. Exit 0 means every requested field has a checked
supplier (or inventory-only succeeded); final theorem assembly is separate.
Exit 1 means open fields. Exit 2 means invalid or incomplete probe evidence.
"""

import argparse
import json
import os
import re
import signal
import subprocess
import tempfile
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path

try:
    from scripts import build_private, check_validation
except ModuleNotFoundError:
    import build_private
    import check_validation

ROOT = Path(__file__).resolve().parents[1]
SUPPORT = ROOT / "scripts/templates/FieldCensus.lean"
STRUCTURE = "Vsa.Sim.IHClause.Trivial.Residuals"
LAYOUT = "Vsa.Sim.LayoutInstance.interpRunLayout"
TIMEOUT_SECONDS = 240
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


@dataclass(frozen=True)
class Field:
    name: str
    projection: str


@dataclass(frozen=True)
class LeanResult:
    returncode: int | None
    output: str


@dataclass(frozen=True)
class ProbeResult:
    field: str
    verdict: str
    detail: str


def lean_identifier(value: str) -> str:
    if not value or not all(
        part.rstrip("'").isidentifier() for part in value.split(".")
    ):
        raise argparse.ArgumentTypeError("expected a qualified Lean identifier")
    return value


def records(output: str, marker: str) -> list[dict]:
    result = []
    for line in output.splitlines():
        if marker in line:
            item = json.loads(line.split(marker, 1)[1].strip())
            if not isinstance(item, dict):
                raise ValueError("invalid census record")
            result.append(item)
    return result


def unsafe_diagnostics(output: str) -> bool:
    """Reject incomplete proofs independently of the compiler exit status."""
    return "sorryAx" in output or bool(
        re.search(r"declaration uses [`'](?:sorry|admit)[`']", output)
    )


def extract_fields(result: LeanResult, object_exists: bool) -> list[Field]:
    if (
        result.returncode != 0
        or not object_exists
        or unsafe_diagnostics(result.output)
        or re.search(r"^.*?error:", result.output, re.MULTILINE)
    ):
        raise ValueError("compiled field inventory failed; inspect Inventory.log")
    fields = []
    for item in records(result.output, "VSA_CENSUS_FIELD "):
        if set(item) != {"field", "projection"}:
            raise ValueError("invalid field inventory record")
        if not all(isinstance(value, str) for value in item.values()):
            raise ValueError("non-text field inventory record")
        try:
            fields.append(
                Field(
                    lean_identifier(item["field"]), lean_identifier(item["projection"])
                )
            )
        except argparse.ArgumentTypeError as error:
            raise ValueError("invalid identifier in field inventory") from error
    if not fields or len({field.name for field in fields}) != len(fields):
        raise ValueError("empty or duplicated compiled field inventory")
    return fields


def classify(field: Field, result: LeanResult, object_exists: bool) -> ProbeResult:
    if result.returncode is None:
        return ProbeResult(field.name, "TIMEOUT", "compiler process group terminated")
    invalid = ProbeResult(
        field.name, "INVALID_EVIDENCE", "inspect the complete probe log"
    )
    if unsafe_diagnostics(result.output):
        return invalid
    try:
        found = records(result.output, "VSA_CENSUS_RESULT ")
    except ValueError:
        return invalid
    errors = re.findall(r"^.*?error: (.*)$", result.output, re.MULTILINE)
    if result.returncode == 0 and object_exists and len(found) == 1 and not errors:
        item = found[0]
        axioms = item.get("axioms")
        if (
            set(item) == {"field", "status", "axioms"}
            and item["field"] == field.name
            and item["status"] == "FOUND"
            and isinstance(axioms, list)
            and all(
                isinstance(axiom, str) and axiom in ALLOWED_AXIOMS for axiom in axioms
            )
        ):
            return ProbeResult(field.name, "FOUND", ", ".join(axioms))
    if (
        result.returncode == 1
        and not found
        and errors
        and all(
            error.startswith("`exact?` could not close the goal.") for error in errors
        )
    ):
        return ProbeResult(
            field.name, "NO_MATCH", "search inconclusive; no supplier certified"
        )
    return invalid


def run_lean(repo: Path, backend: Path, source: Path) -> LeanResult:
    output = source.with_suffix(".olean")
    output.unlink(missing_ok=True)
    shell = 'LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}" exec lean -R "$2" -o "$3" "$4"'
    command = [
        "lake",
        "env",
        "sh",
        "-c",
        shell,
        "field-census",
        str(backend),
        str(source.parent),
        str(output),
        str(source),
    ]
    with subprocess.Popen(
        command,
        cwd=repo,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        start_new_session=True,
    ) as process:
        try:
            transcript, _ = process.communicate(timeout=TIMEOUT_SECONDS)
            status = process.returncode
        except BaseException as error:
            # Capture failure or cancellation must not leave a detached compiler.
            try:
                os.killpg(process.pid, signal.SIGKILL)
            except ProcessLookupError:
                # The process group may exit between the timeout and signal.
                pass
            transcript, _ = process.communicate()
            if not isinstance(error, subprocess.TimeoutExpired):
                source.with_suffix(".log").write_text(transcript)
                raise
            status = None
    source.with_suffix(".log").write_text(transcript)
    return LeanResult(status, transcript)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--structure", default=STRUCTURE, type=lean_identifier)
    parser.add_argument("--layout", default=LAYOUT, type=lean_identifier)
    parser.add_argument("--field", action="append", default=[], type=lean_identifier)
    parser.add_argument("--inventory-only", action="store_true")
    args = parser.parse_args(argv)
    try:
        backend = args.backend.resolve()
        check_validation.verify_backend(ROOT, backend)
        manifest = backend / build_private.MANIFEST_NAME
        fingerprint = build_private.hash_file(manifest)
        destination = build_private.validate_output_root(ROOT, args.output)
        destination.mkdir(parents=True, exist_ok=True)
        run_dir = Path(tempfile.mkdtemp(prefix="run-", dir=destination))
        print(f"Run directory: {run_dir}", flush=True)
        driver_fingerprint = build_private.hash_file(Path(__file__))
        support_fingerprint = build_private.hash_file(SUPPORT)
        modules = build_private.discover_modules(ROOT, include_executable=True)
        imports = "\n".join(f"import {name}" for name in sorted(modules))
        header = imports + "\n" + SUPPORT.read_text() + "\n"
        inventory = run_dir / "Inventory.lean"
        inventory.write_text(header + f"census_fields {args.structure}\n")
        fields = extract_fields(
            run_lean(ROOT, backend, inventory),
            inventory.with_suffix(".olean").is_file(),
        )
        missing = set(args.field) - {field.name for field in fields}
        if missing:
            raise ValueError(f"unknown fields: {', '.join(sorted(missing))}")
        chosen = [
            field for field in fields if not args.field or field.name in args.field
        ]
        results = []
        if not args.inventory_only:
            for field in chosen:
                source = run_dir / f"{field.name}.lean"
                source.write_text(
                    header
                    + f"census_probe {args.structure} {field.name} at {args.layout}\n"
                )
                result = classify(
                    field,
                    run_lean(ROOT, backend, source),
                    source.with_suffix(".olean").is_file(),
                )
                results.append(result)
                print(f"{field.name}: {result.verdict}", flush=True)
        check_validation.verify_backend(ROOT, backend)
        if build_private.hash_file(manifest) != fingerprint:
            raise ValueError("backend changed during census")
        if (
            build_private.hash_file(Path(__file__)) != driver_fingerprint
            or build_private.hash_file(SUPPORT) != support_fingerprint
        ):
            raise ValueError("census tooling changed during run")
        report = {
            "driver_sha256": driver_fingerprint,
            "support_sha256": support_fingerprint,
            "artifacts_sha256": {
                path.name: build_private.hash_file(path)
                for path in sorted(run_dir.iterdir())
                if path.is_file()
            },
            "structure": args.structure,
            "layout": args.layout,
            "backend_manifest_sha256": fingerprint,
            "module_count": len(modules),
            "inventory": [asdict(field) for field in fields],
            "selected": [field.name for field in chosen],
            "inventory_only": args.inventory_only,
            "results": [asdict(result) for result in results],
            "run_directory": str(run_dir),
        }
        (run_dir / "report.json").write_text(json.dumps(report, indent=2) + "\n")
        with (run_dir / "fields.tsv").open("w") as stream:
            stream.write("field\tprojection\tverdict\tdetail\n")
            by_field = {result.field: result for result in results}
            for field in chosen:
                result = by_field.get(
                    field.name, ProbeResult(field.name, "INVENTORIED", "not probed")
                )
                stream.write(
                    f"{field.name}\t{field.projection}\t{result.verdict}\t{result.detail}\n"
                )
        print(
            f"Inventory: {len(fields)} fields; results: {dict(Counter(r.verdict for r in results))}"
        )
        print(f"Evidence: {run_dir / 'report.json'}")
        if any(result.verdict not in {"FOUND", "NO_MATCH"} for result in results):
            return 2
        return int(any(result.verdict == "NO_MATCH" for result in results))
    except (build_private.BuildError, OSError, ValueError) as error:
        print(f"field census failed: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
