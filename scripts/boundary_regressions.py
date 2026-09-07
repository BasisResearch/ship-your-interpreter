#!/usr/bin/env python3
"""Run four fixed initial-state regressions through the actual Sail interpreter.

Use a fingerprint-current private Lean backend. Reports and traces must remain
outside the repository. Sparse runs do not prove a dense Loaded execution.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any

try:
    from scripts import build_private
except ModuleNotFoundError:
    import build_private  # type: ignore[no-redef]

REPO = Path(__file__).resolve().parents[1]
FIXTURE = Path("experiments/smt/BoundaryRegressions.lean")
LOCK = Path("experiments/smt/boundary-regressions.lock.json")
NEW_MODULES = frozenset(
    f"Vsa.Sim.NativeNameAudit.{name}"
    for name in ("Memory", "Ast", "Admission", "Loaded")
)
CASE_IDS = ("ast_output_alias", "ast_unreadable", "native_name_alias", "stable_control")
EXPECTED_AXIOM_REPORTS = frozenset(
    (
        "Vsa.While.LoadedOutputAlias.program_bigStep",
        "Vsa.Sim.OutputAliasLoaded.snapshot_loaded",
        "Vsa.Sim.OutputAliasLoaded.snapshot_not_loaded",
        "Vsa.Sim.OutputAliasLoaded.snapshot_halts_twoLF",
        "Vsa.Sim.AstAccessAudit.access_bigStep",
        "Vsa.Sim.AstAccessAudit.access_loaded",
        "Vsa.Sim.AstAccessAudit.access_not_loaded",
        "Vsa.Sim.AstAccessAudit.access_not_halts",
        "Vsa.Sim.NativeNameAudit.nativeName_bigStep",
        "Vsa.Sim.NativeNameAudit.nativeName_loaded",
        "Vsa.Sim.NativeNameAudit.nativeName_not_loaded",
        "Vsa.Sim.NativeNameAudit.Control.loaded",
    )
)
STANDARD_AXIOMS = frozenset(("propext", "Classical.choice", "Quot.sound"))
EXPECTED = {
    "ast_output_alias": ("htif_halt", "\n\n", "\n", None),
    "ast_unreadable": ("sail_error", "", "", 0x80004014),
    "native_name_alias": ("sail_error", "\n", "\n\n", 0x80004600),
    "stable_control": ("htif_halt", "\n\n", "\n\n", None),
}
EXPECTED_BOUNDARY = {
    "ast_output_alias": ("excluded", None, "Vsa.Sim.OutputAliasLoaded.snapshot_not_loaded"),
    "ast_unreadable": ("excluded", None, "Vsa.Sim.AstAccessAudit.access_not_loaded"),
    "native_name_alias": ("excluded", None, "Vsa.Sim.NativeNameAudit.nativeName_not_loaded"),
    "stable_control": ("admitted", "Vsa.Sim.NativeNameAudit.Control.loaded", None),
}



class RegressionError(Exception):
    """Reject stale inputs, failed replay, or incomplete evidence."""


def validate_axiom_reports(transcript: str) -> dict[str, list[str]]:
    """Require precisely the fixture's theorem reports, with standard axioms.

    Axiom-free Lean reports and any subset of the standard three are accepted.
    Missing, repeated, unexpected, malformed and unsafe reports fail closed.
    """
    reports: dict[str, list[str]] = {}
    pattern = re.compile(
        r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    )
    if "sorryAx" in transcript:
        raise RegressionError("sorryAx in fixture diagnostics")
    for line in transcript.splitlines():
        if "axiom" not in line:
            continue
        match = pattern.fullmatch(line.strip())
        if match is None:
            raise RegressionError(f"malformed axiom report: {line[:160]}")
        theorem, names = match.groups()
        if theorem not in EXPECTED_AXIOM_REPORTS:
            raise RegressionError(f"unrelated axiom report: {theorem}")
        if theorem in reports:
            raise RegressionError(f"duplicate axiom report: {theorem}")
        axioms = [] if not names else [name.strip() for name in names.split(",")]
        if not set(axioms) <= STANDARD_AXIOMS or len(set(axioms)) != len(axioms):
            raise RegressionError(f"nonstandard axiom report: {theorem}: {axioms}")
        reports[theorem] = axioms
    if set(reports) != EXPECTED_AXIOM_REPORTS:
        raise RegressionError(
            f"missing axiom reports: {sorted(EXPECTED_AXIOM_REPORTS - reports.keys())}"
        )
    return reports


def dependency_order(repo: Path) -> list[build_private.Module]:
    """Find the complete local import closure of the checked fixture."""
    modules = build_private.discover_modules(repo)
    selected: set[str] = set()

    def visit(name: str) -> None:
        if name not in modules or name in selected:
            return
        selected.add(name)
        for dependency in modules[name].imports:
            visit(dependency)

    for name in build_private.parse_header_imports((repo / FIXTURE).read_text()):
        visit(name)
    return build_private.topological_order({name: modules[name] for name in selected})


def input_hashes(repo: Path) -> dict[str, str]:
    """Hash the ELF, fixture, boundary and its full local proof-source closure."""
    paths = {module.source for module in dependency_order(repo)}
    for root in (
        "riscv-lean/lean_emulator",
        "riscv-lean/lean-sail",
        "riscv-lean/Lean_RV64D_executable",
    ):
        for path in (repo / root).rglob("*"):
            if (
                ".lake" not in path.parts
                and path.is_file()
                and (
                    path.suffix in {".lean", ".toml"}
                    or path.name in {"lake-manifest.json", "lean-toolchain"}
                )
            ):
                paths.add(path.relative_to(repo))
    paths.update(
        {
            FIXTURE,
            Path("scripts/boundary_regressions.py"),
            Path("scripts/check_validation.py"),
            Path("scripts/build_private.py"),
            Path("c/while-riscv-htif.elf"),
            Path("lean-toolchain"),
            Path("lake-manifest.json"),
            Path("lakefile.toml"),
        }
    )
    return {str(path): build_private.hash_file(repo / path) for path in sorted(paths)}


def check_lock(repo: Path, lock: Path) -> dict[str, Any]:
    """Reject a changed source, ELF, boundary, fixture, or case inventory."""
    receipt = json.loads(lock.read_text())
    if receipt.get("schema") != 1 or receipt.get("case_ids") != list(CASE_IDS):
        raise RegressionError("invalid locked case inventory")
    actual = input_hashes(repo)
    expected = receipt.get("inputs")
    if actual != expected:
        changed = sorted(
            key
            for key in actual.keys() | (expected or {}).keys()
            if actual.get(key) != (expected or {}).get(key)
        )
        raise RegressionError(f"input fingerprint drift: {', '.join(changed[:12])}")
    return receipt


def check_result(case_id: str, row: dict[str, Any]) -> dict[str, Any]:
    """Validate actual Sail rows and the explicit terminal attempt."""
    if case_id not in EXPECTED or row.get("case") != case_id or row.get("schema") != 1:
        raise RegressionError(f"invalid replay identity: {case_id}")
    boundary = tuple(row.get(key) for key in (
        "current_boundary_status", "current_admission", "current_exclusion"
    ))
    if boundary != EXPECTED_BOUNDARY[case_id]:
        raise RegressionError(f"boundary proof classification drift for {case_id}")
    status, output, source_output, fault_pc = EXPECTED[case_id]
    final = row.get("final_full_state", {})
    event = row.get("terminal_event", {})
    if row.get("status") != status or final.get("output") != output:
        raise RegressionError(f"unexpected Sail outcome for {case_id}")
    if row.get("expected_source_output") != source_output:
        raise RegressionError(f"source oracle drift for {case_id}")
    if row.get("fuel") != 20000 or not 0 < row.get("steps", 0) < 20000:
        raise RegressionError(f"invalid fuel/step count for {case_id}")
    if event.get("kind") != status:
        raise RegressionError(f"missing terminal attempt for {case_id}")
    if status == "sail_error":
        if event.get("error") != "Unreachable" or final.get("pc") != fault_pc:
            raise RegressionError(f"unexpected Sail error for {case_id}")
        if row.get("exit_code") is not None or final.get("mcause") is not None:
            raise RegressionError(f"unexpected exception state for {case_id}")
    elif (
        row.get("exit_code") != 0
        or event.get("exit_code") != 0
        or final.get("htif_done") is not True
    ):
        raise RegressionError(f"unexpected exit code for {case_id}")
    trace = row.get("trace")
    if not isinstance(trace, list) or len(trace) != row["steps"] - (
        status == "htif_halt"
    ):
        raise RegressionError(f"missing successful rows for {case_id}")
    for index, step in enumerate(trace):
        if step.get("steps") != index or len(step.get("gprs", [])) != 31:
            raise RegressionError(f"incomplete trace row {index} for {case_id}")
        successor = (
            trace[index + 1] if index + 1 < len(trace) else event.get("attempt", {})
        )
        if step.get("next_pc") != successor.get("pc"):
            raise RegressionError(f"broken trace successor {index} for {case_id}")
    for claim in (
        "dense_memory_evaluated",
        "replay_establishes_dense_loaded_execution",
        "complete_contract_validation",
    ):
        if row.get(claim) is not False:
            raise RegressionError(f"unsupported proof claim {claim} for {case_id}")
    return {
        "case": case_id,
        "status": status,
        "steps": row["steps"],
        "machine_output": output,
        "source_output": source_output,
        "matches_source_output": output == source_output,
        "matches_source_termination": status == "htif_halt",
        "source_oracle": row.get("source_oracle"),
        "dense_admission": row.get("dense_admission"),
        "current_boundary_status": row["current_boundary_status"],
        "current_admission": row["current_admission"],
        "current_exclusion": row["current_exclusion"],
        "independent_dense_execution_theorem": row.get(
            "independent_dense_execution_theorem"
        ),
    }


def validate_results(rows: dict[str, dict[str, Any]]) -> list[dict[str, Any]]:
    """Require all four distinct cases, including the positive control."""
    if set(rows) != set(CASE_IDS):
        raise RegressionError("dropped or unknown regression cases")
    return [check_result(case_id, rows[case_id]) for case_id in CASE_IDS]


def current_findings(cases: list[dict[str, Any]]) -> list[str]:
    """Classify mismatches only after each snapshot's admission proof is checked."""
    return [row["case"] for row in cases
            if row["current_boundary_status"] == "admitted"
            and not (row["matches_source_output"] and row["matches_source_termination"])]


def load_verified_results(
    directory: Path, repo: Path = REPO, lock: Path = REPO / LOCK
) -> dict[str, dict[str, Any]]:
    """Bind retained results to the current lock and recorded artifact digests.

    This checks replay receipt consistency, not a sparse-to-dense execution proof.
    The receipt and its artifact directory are retained local run evidence.
    """
    receipt = check_lock(repo, lock)
    summary = json.loads((directory / "summary.json").read_text())
    if (
        summary.get("schema") != 1
        or summary.get("status") not in {"PASS", "FINDINGS"}
        or summary.get("regression_status") != "PASS"
        or summary.get("inputs") != receipt["inputs"]
    ):
        raise RegressionError("stale or invalid regression source receipt")
    artifacts = summary.get("artifacts")
    expected_files = {
        f"{case}.{suffix}" for case in CASE_IDS for suffix in ("json", "log")
    }
    if not isinstance(artifacts, dict) or set(artifacts) != expected_files:
        raise RegressionError("incomplete replay artifact receipt")
    for name in sorted(expected_files):
        path = directory / name
        if not path.is_file() or build_private.hash_file(path) != artifacts[name]:
            raise RegressionError(f"artifact fingerprint drift: {name}")
    rows: dict[str, dict[str, Any]] = {}
    for case in CASE_IDS:
        validate_axiom_reports((directory / f"{case}.log").read_text())
        rows[case] = json.loads((directory / f"{case}.json").read_text())
    cases = validate_results(rows)
    if summary.get("cases") != cases:
        raise RegressionError("regression case summary drift")
    if (
        summary.get("current_boundary_candidate_findings") != current_findings(cases)
        or summary.get("status") != ("FINDINGS" if current_findings(cases) else "PASS")
        or summary.get("complete_contract_validation") is not False
        or summary.get("dense_execution_proved_by_replay") is not False
    ):
        raise RegressionError("unsupported regression summary claim")
    return rows


def prepare_backend(repo: Path, backend: Path, output: Path) -> Path:
    """Reuse only current dependencies and privately compile the four new leaves."""
    order = dependency_order(repo)
    current = build_private.module_fingerprints(
        repo, order, build_private.input_context(repo)
    )
    prior = build_private.load_manifest(backend / build_private.MANIFEST_NAME)
    overlay = output / "backend"
    overlay.mkdir()
    compiled: dict[str, str] = {}
    for module in order:
        target = build_private.output_path(overlay, module)
        original = build_private.output_path(backend, module)
        target.parent.mkdir(parents=True, exist_ok=True)
        if prior.get(module.name) == current[module.name] and original.is_file():
            target.symlink_to(original)
        elif module.name in NEW_MODULES:
            build_private.compile_module(repo, overlay, module)
        else:
            raise RegressionError(
                f"backend not current for {module.name}; refresh it first"
            )
        compiled[module.name] = current[module.name]
    build_private.write_manifest(overlay / build_private.MANIFEST_NAME, compiled)
    return overlay


def run_checked(command: list[str], repo: Path, log: Path) -> None:
    """Run Lean synchronously and preserve its complete output on failure."""
    result = subprocess.run(
        command, cwd=repo, capture_output=True, text=True, check=False
    )
    log.write_text(result.stdout + result.stderr)
    if result.returncode or "sorryAx" in result.stdout + result.stderr:
        raise RegressionError(f"Lean failed ({result.returncode}); see {log}")
    validate_axiom_reports(result.stdout + result.stderr)


def run(repo: Path, backend: Path, output: Path, lock: Path) -> dict[str, Any]:
    """Compile the fixture, replay every case, and record a bounded evidence report."""
    output = output.resolve()
    if output.is_relative_to(repo.resolve()):
        raise RegressionError("output must be outside the repository")
    output.mkdir(parents=True, exist_ok=False)
    receipt = check_lock(repo, lock)
    overlay = prepare_backend(repo, backend.resolve(), output)
    # --run compiles and checks the source oracle/admission axiom audits each run.
    # Arguments use positional shell parameters; no interpolation of path contents.
    shell = 'LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}" lean --run "$2" "$3" "$4"'
    rows: dict[str, dict[str, Any]] = {}
    commands: list[list[str]] = []
    for case_id in CASE_IDS:
        destination = output / f"{case_id}.json"
        command = [
            "lake",
            "env",
            "sh",
            "-c",
            shell,
            "boundary-regressions",
            str(overlay),
            str(FIXTURE),
            case_id,
            str(destination),
        ]
        commands.append(command)
        (output / "commands.json").write_text(json.dumps(commands, indent=2) + "\n")
        run_checked(command, repo, output / f"{case_id}.log")
        rows[case_id] = json.loads(destination.read_text())
        check_result(case_id, rows[case_id])
    cases = validate_results(rows)
    findings = current_findings(cases)
    status = "FINDINGS" if findings else "PASS"
    # Detect source changes while the compiler/runtime was active.
    check_lock(repo, lock)
    report = {
        "schema": 1,
        "status": status,
        "regression_status": "PASS",
        "current_boundary_candidate_findings": findings,
        "evidence_kind": "actual Sail sparse-runtime regressions with separate Lean proof references",
        "complete_contract_validation": False,
        "dense_execution_proved_by_replay": False,
        "cases": cases,
        "inputs": receipt["inputs"],
        "artifacts": {
            f"{case_id}.{suffix}": build_private.hash_file(
                output / f"{case_id}.{suffix}"
            )
            for case_id in CASE_IDS
            for suffix in ("json", "log")
        },
    }
    (output / "summary.json").write_text(json.dumps(report, indent=2) + "\n")
    load_verified_results(output, repo, lock)
    return {
        "status": status,
        "regression_status": "PASS",
        "case_count": len(cases),
        "current_boundary_candidate_findings": findings,
        "summary": str(output / "summary.json"),
    }


def main(argv: list[str] | None = None) -> int:
    """Expose a fail-closed command with explicit backend and artifact roots."""
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument(
        "--self-test",
        action="store_true",
        help="accept expected findings only when all four regressions match",
    )
    args = parser.parse_args(argv)
    try:
        report = run(REPO, args.backend, args.output, REPO / LOCK)
    except (
        RegressionError,
        build_private.BuildError,
        OSError,
        ValueError,
        TypeError,
        KeyError,
    ) as error:
        print(json.dumps({"status": "FAIL", "error": str(error)}))
        return 1
    print(json.dumps(report))
    return 0 if args.self_test or not report["current_boundary_candidate_findings"] else 1


if __name__ == "__main__":
    sys.exit(main())
