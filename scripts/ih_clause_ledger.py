#!/usr/bin/env python3
"""Evidence ledger for induction-hypothesis clause residual fields.

Sibling of `residual_coverage_ledger.py` for the generated clause records
`Vsa.Sim.IHClause.<Name>.Residuals`.  Every field gets one row per evidence
kind — `execution` (trace corpus), `smt` (statement refutation), `oracle`
(bounded invariant/proof engines) and `lean-bridge` (a compiled Lean proof or
draft) — read from the artifacts the Level-4 tools emit under one directory:

  ih_clause_status.tsv    scripts/ih_clause_status.py          (required)
  ih_clause_fuzz.tsv      scripts/ih_clause_fuzz.py            (optional)
  ih_clause_suggest.tsv   scripts/ih_clause_status.py --suggest (optional)
  --execution TSV         clause, field, verdict, evidence      (optional)

A row is covered only when the named artifact reports it; a missing artifact
is an explicit hole, never silent coverage.  The ledger reports emitted
evidence; it does not promote a draft, a fuzz miss or a trace to a proof of
the clause step.

>>> covered("smt", {"verdict": "NOT-REFUTED"})
(True, 'NOT-REFUTED')
>>> covered("oracle", {"houdini": "ENCODE-GAP: x", "autoprove": "ENCODE-GAP: x"})
(False, 'ENCODE-GAP')
"""

from __future__ import annotations

import argparse
import csv
import json
import sys
from pathlib import Path

try:
    from scripts import residual_coverage_ledger as base
except ModuleNotFoundError:  # invoked as a script
    import residual_coverage_ledger as base  # type: ignore[no-redef]

EVIDENCE_KINDS = ("execution", "smt", "oracle", "lean-bridge")
COLUMNS = ("clause", "field", "status", "kind", "covered", "verdict", "evidence",
           "hole", "dimensions")
ORACLE_POSITIVE = {"PROVABLE-DIRECT", "PROVED-DIRECT", "IH-FOUND", "PROVED-WITH-IH",
                   "PROVED-VIA-LLM"}
HOLES = {
    "execution": "no trace query targets this clause step",
    "smt": "no refutation artifact",
    "oracle": "no bounded-engine artifact",
    "lean-bridge": "no compiled Lean proof or draft",
}


class ClauseLedgerError(ValueError):
    """An emitted clause artifact is missing, duplicated or inconsistent."""


def read_tsv(path: Path, required: set[str]) -> list[dict[str, str]]:
    with path.open(newline="") as stream:
        reader = csv.DictReader(stream, delimiter="\t")
        rows = list(reader)
        columns = set(reader.fieldnames or ())
    if not required <= columns:
        raise ClauseLedgerError(f"{path}: missing columns {sorted(required - columns)}")
    return rows


def keyed(rows: list[dict[str, str]], path: Path) -> dict[tuple[str, str], dict[str, str]]:
    result: dict[tuple[str, str], dict[str, str]] = {}
    for row in rows:
        key = (row["clause"], row["field"])
        if key in result:
            raise ClauseLedgerError(f"{path}: duplicate row for {key[0]}.{key[1]}")
        result[key] = row
    return result


def covered(kind: str, row: dict[str, str] | None) -> tuple[bool, str]:
    """Whether an artifact row is positive evidence of `kind`, and its verdict."""
    if row is None:
        return False, ""
    if kind == "execution":
        return row.get("verdict", "") not in ("", "UNSUPPORTED"), row.get("verdict", "")
    if kind == "smt":
        verdict = row.get("verdict", "")
        return verdict in ("REFUTED", "NOT-REFUTED"), verdict
    if kind == "oracle":
        verdicts = [row.get(e, "").split(":", 1)[0] for e in ("houdini", "autoprove")]
        hits = [v for v in verdicts if v in ORACLE_POSITIVE]
        return bool(hits), hits[0] if hits else (verdicts[0] or "")
    if kind == "lean-bridge":
        if row.get("status") == "WIRED" and row.get("census", "") in ("", "FOUND"):
            return True, "wired" + (":census-FOUND" if row.get("census") else "")
        if row.get("hook_backend") == "exists":
            return True, "hook-lemma"
        if row.get("outcome") == "DIRECT" and row.get("lean_candidate"):
            return True, f"draft:{row['lean_candidate']}"
        return False, row.get("outcome", "")
    raise ClauseLedgerError(f"unknown evidence kind {kind}")


def build(directory: Path, execution: Path | None = None) -> dict[str, object]:
    status_path = directory / "ih_clause_status.tsv"
    if not status_path.is_file():
        raise ClauseLedgerError(f"missing {status_path} (run ih_clause_status.py first)")
    status = keyed(read_tsv(status_path, {"clause", "field", "status"}), status_path)
    clauses: dict[str, str] = {}
    status_json = directory / "ih_clause_status.json"
    if status_json.is_file():
        report = json.loads(status_json.read_text())
        for name, info in report.get("clauses", {}).items():
            clauses[name] = f"{info.get('pred', '')} {info.get('notes', '')}"
    artifacts: dict[str, dict[tuple[str, str], dict[str, str]]] = {}
    sources = {"smt": directory / "ih_clause_fuzz.tsv",
               "oracle": directory / "ih_clause_suggest.tsv",
               "execution": execution}
    for kind, path in sources.items():
        if path is None or not path.is_file():
            artifacts[kind] = {}
            continue
        rows = keyed(read_tsv(path, {"clause", "field"}), path)
        unknown = sorted(set(rows) - set(status))
        if unknown:
            raise ClauseLedgerError(
                f"{path}: rows for unknown fields {unknown[:3]}")
        artifacts[kind] = rows
    cells = []
    for (clause, field), row in status.items():
        dims = ",".join(base.dimensions_for(clauses.get(clause, ""))) if clauses else ""
        for kind in EVIDENCE_KINDS:
            if kind == "lean-bridge":
                suggestion = artifacts["oracle"].get((clause, field), {})
                evidence_row = {**row, **suggestion}
                is_covered, verdict = covered(kind, evidence_row)
                if verdict.startswith("draft:"):
                    evidence = suggestion.get("evidence", "") or suggestion.get("draft", "")
                else:
                    evidence = row.get("evidence", "")
                hole = "" if is_covered else (
                    suggestion.get("lean_detail", "") or HOLES[kind])
            else:
                evidence_row = artifacts[kind].get((clause, field))
                is_covered, verdict = covered(kind, evidence_row)
                source = evidence_row or {}
                evidence = source.get("evidence", "") or source.get("draft", "")
                hole = "" if is_covered else (
                    source.get("detail", "") or source.get("houdini", "") or HOLES[kind])
            cells.append({
                "clause": clause, "field": field, "status": row["status"], "kind": kind,
                "covered": is_covered, "verdict": verdict, "evidence": evidence,
                "hole": hole, "dimensions": dims,
            })
    summary = {kind: sum(c["covered"] for c in cells if c["kind"] == kind)
               for kind in EVIDENCE_KINDS}
    return {
        "schema": 1,
        "warning": "Evidence matrix only; it does not establish any clause step.",
        "directory": str(directory),
        "field_count": len(status),
        "cell_count": len(cells),
        "covered": summary,
        "cells": cells,
    }


def write_outputs(ledger: dict[str, object], tsv_path: Path, json_path: Path) -> None:
    cells = ledger["cells"]
    assert isinstance(cells, list)
    rows = [tuple("yes" if c == "covered" and cell[c] else str(cell[c]) if c != "covered"
                  else "no" for c in COLUMNS) for cell in cells]
    base._write_tsv(tsv_path, COLUMNS, rows)
    json_path.write_text(json.dumps(ledger, indent=2, sort_keys=True) + "\n")


def summary_text(ledger: dict[str, object]) -> str:
    covered_ = ledger["covered"]
    assert isinstance(covered_, dict)
    parts = " ".join(f"{k} {v}/{ledger['field_count']}" for k, v in covered_.items())
    return f"IH clause ledger: {ledger['field_count']} field(s); covered: {parts}"


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = parser.add_subparsers(dest="command", required=True)
    build_ = sub.add_parser("build")
    build_.add_argument("--dir", type=Path, required=True,
                        help="directory holding the ih_clause_*.tsv artifacts")
    build_.add_argument("--execution", type=Path,
                        help="TSV (clause, field, verdict, evidence) of trace evidence")
    build_.add_argument("--out-tsv", type=Path)
    build_.add_argument("--out-json", type=Path)
    args = parser.parse_args(argv)
    try:
        ledger = build(args.dir, args.execution)
    except (ClauseLedgerError, OSError, json.JSONDecodeError) as error:
        print(f"ih_clause_ledger failed: {error}", file=sys.stderr)
        return 2
    tsv = args.out_tsv or args.dir / "ih_clause_ledger.tsv"
    js = args.out_json or args.dir / "ih_clause_ledger.json"
    write_outputs(ledger, tsv, js)
    print(summary_text(ledger))
    print(f"Evidence: {tsv}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
