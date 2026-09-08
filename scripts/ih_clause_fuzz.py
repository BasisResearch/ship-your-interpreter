#!/usr/bin/env python3
"""Refute-before-prove for induction-hypothesis clause steps.

For every residual field of a clause (`Vsa.Sim.IHClause.<Name>.Residuals`) the
tool extracts the step statement into a hermetic module
`<output>/statements/<Name>_<case>.lean` (`def Step_<case> (_L : Layout) : Prop`,
the `--file`/`--prop` input shape of `statement_fuzz.py`) and reports ONE of

  REFUTED       a machine-checked counterexample (statement_fuzz REFUTED);
  NOT-REFUTED   no counterexample: the field is WIRED (a compiled Lean proof)
                or the fuzzer ran in its fragment without refuting it
                (inconclusive, never a survival claim);
  UNSUPPORTED   outside the tools' fragment, with the reason.

Every clause step concludes a motive (`EvalIHWith <pred>` over machine runs),
which is outside the address-map fragment (Mem, BitVec, StackOK, windows) of
`statement_fuzz.py` and `smt_check.py`; unwired steps are therefore
UNSUPPORTED unless `--lean` runs the fuzzer's witness probe anyway against
`--backend` (statement_fuzz requires a fingerprint-current backend, set as
`VSA_PRIVATE_BUILD`).  `smt_check.py` is not run: a motive conclusion is an
opaque atom to its encoder and its verdict would be REFUTED-MODULO-OPAQUE by
construction.  Run Lean-backed modes with exclusive compiler access.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile
from pathlib import Path

try:
    from scripts import gen_ih_clause as generator, ih_clause_model as model
except ModuleNotFoundError:  # invoked as a script
    import gen_ih_clause as generator  # type: ignore[no-redef]
    import ih_clause_model as model  # type: ignore[no-redef]

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = Path(tempfile.gettempdir()) / "vsa-ih-clause"
VERDICTS = ("REFUTED", "NOT-REFUTED", "UNSUPPORTED")
COLUMNS = ("clause", "field", "status", "verdict", "engine", "detail", "statement", "evidence")
# statement_fuzz verdict → this tool's verdict.
FUZZ_MAP = {
    "REFUTED": "REFUTED",
    "INCONCLUSIVE": "NOT-REFUTED",
    "INHABITED": "NOT-REFUTED",
    "SURVIVED-IN-FRAGMENT": "NOT-REFUTED",
    "UNDECIDABLE": "UNSUPPORTED",
    "TIMEOUT": "UNSUPPORTED",
}


def statement_name(field: model.ClauseField) -> str:
    return f"Step_{field.name}"


def write_statement(info: model.ClauseInfo, field: model.ClauseField, directory: Path) -> Path:
    path = directory / "statements" / f"{info.name}_{field.name}.lean"
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(model.statement_module(info, field, statement_name(field)))
    return path


def run_fuzzer(path: Path, prop: str, backend: Path, log_path: Path) -> tuple[str, str]:
    """statement_fuzz `--file` probe of `∀ L, <prop> L`; (raw verdict, detail)."""
    try:
        from scripts import build_private, check_validation, statement_fuzz  # noqa: PLC0415
    except ModuleNotFoundError:
        import build_private  # type: ignore[no-redef]  # noqa: PLC0415
        import check_validation  # type: ignore[no-redef]  # noqa: PLC0415
        import statement_fuzz  # type: ignore[no-redef]  # noqa: PLC0415
    try:
        check_validation.verify_backend(ROOT, backend)
    except (build_private.BuildError, OSError) as error:
        return "BACKEND-INVALID", f"statement_fuzz not run: {error}"
    os.environ["VSA_PRIVATE_BUILD"] = str(backend)
    with log_path.open("a") as log:
        verdict = statement_fuzz.fuzz_file(
            str(path), f"(∀ L : Vsa.Refine.Layout, {prop} L)", None, log)
    return verdict, f"statement_fuzz.fuzz_file: {verdict}"


def fuzz_field(info: model.ClauseInfo, field: model.ClauseField, directory: Path,
               backend: Path | None, lean: bool) -> dict[str, str]:
    statement = write_statement(info, field, directory)
    row = {"clause": info.name, "field": field.name, "status": field.status,
           "statement": str(statement), "evidence": "", "engine": "", "detail": ""}
    if field.status == "WIRED":
        row.update(verdict="NOT-REFUTED", engine="lean-wiring",
                   detail=f"compiled wiring `{' '.join(field.wiring.split())}`",
                   evidence=f"{info.path}:{field.wiring_line}")
        return row
    reason = model.fragment_reason(field, info)
    if not (lean and backend is not None):
        row.update(verdict="UNSUPPORTED", engine="fragment", detail=reason)
        return row
    log_path = directory / "statements" / f"{info.name}_{field.name}.fuzz.log"
    prop = f"{info.namespace}.{statement_name(field)}"
    raw, detail = run_fuzzer(statement, prop, backend, log_path)
    row.update(verdict=FUZZ_MAP.get(raw, "UNSUPPORTED"), engine="statement_fuzz",
               detail=f"{detail}; {reason}", evidence=str(log_path))
    return row


def summary(rows: list[dict[str, str]]) -> str:
    lines = [f"IH clause fuzz: {len(rows)} field(s)"]
    by_clause: dict[str, list[dict[str, str]]] = {}
    for row in rows:
        by_clause.setdefault(row["clause"], []).append(row)
    for clause, mine in by_clause.items():
        counts = {v: sum(r["verdict"] == v for r in mine) for v in VERDICTS}
        lines.append(f"  {clause:<12} " + " ".join(f"{v} {n}" for v, n in counts.items()))
        for row in mine:
            if row["verdict"] == "REFUTED":
                lines.append(f"    {row['field']}: REFUTED ({row['evidence']})")
    return "\n".join(lines)


def write_tsv(path: Path, rows: list[dict[str, str]]) -> None:
    with path.open("w") as stream:
        stream.write("\t".join(COLUMNS) + "\n")
        for row in rows:
            stream.write("\t".join(str(row.get(c, "")).replace("\t", " ").replace("\n", " ")
                                   for c in COLUMNS) + "\n")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tsv", type=Path, default=generator.TSV)
    parser.add_argument("--clause", action="append", default=[])
    parser.add_argument("--field", action="append", default=[])
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--backend", type=Path,
                        help="fingerprint-current private backend for --lean")
    parser.add_argument("--lean", action="store_true",
                        help="run statement_fuzz's witness probe on unwired steps")
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args(argv)
    if args.lean and args.backend is None:
        parser.error("--lean requires --backend")
    try:
        model_ = model.load_model(args.tsv, clauses=args.clause or None)
        rows = []
        for info in model_.values():
            for field in info.fields:
                if args.field and field.name not in args.field:
                    continue
                rows.append(fuzz_field(info, field, args.output,
                                       args.backend.resolve() if args.backend else None,
                                       args.lean))
        if args.field:
            known = {f.name for i in model_.values() for f in i.fields}
            unknown = sorted(set(args.field) - known)
            if unknown:
                raise ValueError(f"unknown field(s): {', '.join(unknown)}")
        args.output.mkdir(parents=True, exist_ok=True)
        write_tsv(args.output / "ih_clause_fuzz.tsv", rows)
        report = {"tsv": str(args.tsv), "backend": str(args.backend) if args.backend else None,
                  "lean": args.lean, "rows": rows}
        (args.output / "ih_clause_fuzz.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2) if args.json else summary(rows))
        print(f"Evidence: {args.output / 'ih_clause_fuzz.tsv'}")
        return 1 if any(r["verdict"] == "REFUTED" for r in rows) else 0
    except (ValueError, OSError) as error:
        print(f"ih_clause_fuzz failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
