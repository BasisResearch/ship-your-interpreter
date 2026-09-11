#!/usr/bin/env python3
"""Status of every generated induction-hypothesis clause residual field.

For each clause in `scripts/ih_clauses.tsv` the tool lists the fields of
`Vsa.Sim.IHClause.<Name>.Residuals`, their table tag and their status:

  WIRED   tag `exact:`/`from_old:`/`unguarded:` and the generated
          `Residuals.ofUnwired` fills the field (the module is current);
  HOOK    tag `generic:<id>`: the field waits for the generic discharger
          `Vsa.Sim.IHClauseGeneric.<id>.<case>`; the tool reports whether that
          lemma is declared in the sources and, with `--backend`, whether it
          compiles (one Lean run per clause);
  MANUAL  tag `manual`;
  STALE   a wired tag whose generated module is missing or stale (regenerate).

`--suggest` drafts candidate proofs for every HOOK/MANUAL field (the hook lemma
and every `*_of_old` discharger of `Vsa/Sim/IHClauseSupport.lean`, plus
`--candidate` terms), checks them in ONE Lean run per clause against
`--backend`, runs the bounded engines (`houdini_ih.py`, `autoprove.py`) with the
field registered at its declared encoding, and records DIRECT / WITH-IH /
FAILED / UNSUPPORTED per field.  Drafts stay under `--output/drafts`; nothing is
written into `Vsa/`.  `--verify-census` re-checks each WIRED wiring through the
census elaborator (`census_probe … using`).

Run Lean-backed modes with exclusive compiler access.  `--backend` may be the
full private backend or a `proof_slice` overlay that contains the clause modules.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import tempfile
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path

try:
    from scripts import attempt_receipts
    from scripts import build_private, field_census as census, gen_ih_clause as generator
    from scripts import ih_clause_model as model
except ModuleNotFoundError:  # invoked as a script
    import attempt_receipts  # type: ignore[no-redef]
    import build_private  # type: ignore[no-redef]
    import field_census as census  # type: ignore[no-redef]
    import gen_ih_clause as generator  # type: ignore[no-redef]
    import ih_clause_model as model  # type: ignore[no-redef]

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = Path(tempfile.gettempdir()) / "vsa-ih-clause"
LAYOUT = census.LAYOUT
OUTCOMES = ("DIRECT", "WITH-IH", "FAILED", "UNSUPPORTED")
AXIOM_REPORT = re.compile(
    r"^'(.+?)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", re.M)
UNKNOWN_CONSTANT = re.compile(r"[Uu]nknown (?:constant|identifier) `([^`]+)`")
ERROR_LINE = re.compile(r"^(.*?):(\d+):(\d+): error(?:\([^)]*\))?: (.*)$", re.M)
STATUS_COLUMNS = ("clause", "field", "constructor", "relation", "tag", "status",
                  "hook_lemma", "hook_source", "hook_backend", "wiring", "census", "evidence")
SUGGEST_COLUMNS = ("clause", "field", "status", "outcome", "lean_candidate", "lean_detail",
                   "houdini", "autoprove", "encoding", "draft", "evidence",
                   "attempt_receipt")


@dataclass(frozen=True)
class Candidate:
    label: str
    kind: str
    term: str


# ------------------------------------------------------------------ Lean I/O


def run_lean(backend: Path, directory: Path, name: str, source: str) -> census.LeanResult:
    """Compile `source` against `backend` (full backend or overlay); keep the log."""
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"{name}.lean"
    path.write_text(source)
    return census.run_lean(ROOT, backend, path)


def axiom_reports(output: str) -> dict[str, list[str]]:
    reports: dict[str, list[str]] = {}
    for match in AXIOM_REPORT.finditer(output):
        axioms = [a.strip() for a in (match.group(2) or "").split(",") if a.strip()]
        reports[match.group(1)] = axioms
    return reports


def unknown_constants(output: str) -> set[str]:
    return set(UNKNOWN_CONSTANT.findall(output))


def error_lines(output: str) -> list[tuple[int, str]]:
    return [(int(m.group(2)), m.group(4)) for m in ERROR_LINE.finditer(output)]


def clean(axioms: list[str]) -> bool:
    return set(axioms) <= census.ALLOWED_AXIOMS


# -------------------------------------------------------------- hook lemmas


_SOURCE_INDEX: dict[Path, list[tuple[str, list[str]]]] = {}


def source_index(root: Path = ROOT) -> list[tuple[str, list[str]]]:
    """Comment-stripped `Vsa/**/*.lean` texts with their namespaces, read once."""
    if root not in _SOURCE_INDEX:
        entries = []
        for path in sorted((root / "Vsa").rglob("*.lean")):
            text = model.strip_comments(path.read_text())
            entries.append((text, re.findall(r"^namespace\s+(\S+)", text, re.M)))
        _SOURCE_INDEX[root] = entries
    return _SOURCE_INDEX[root]


def declared_in_source(lemma: str, root: Path = ROOT) -> bool:
    """Heuristic source scan for `theorem <lemma>` under a matching namespace."""
    parts = lemma.split(".")
    short, prefix = parts[-1], ".".join(parts[:-1])
    for text, namespaces in source_index(root):
        if re.search(rf"^theorem\s+{re.escape(lemma)}\b", text, re.M):
            return True
        if not re.search(rf"^theorem\s+{re.escape(short)}\b", text, re.M):
            continue
        if any(prefix == ns or prefix.endswith("." + ns) for ns in namespaces):
            return True
    return False


def hook_probe_source(info: model.ClauseInfo, lemmas: list[str]) -> str:
    return f"import {info.module}\n\n" + "".join(
        f"#print axioms {lemma}\n" for lemma in lemmas
    )


def probe_hooks(info: model.ClauseInfo, backend: Path, directory: Path) -> dict[str, str]:
    """`exists` / `exists-unclean` / `missing` / `unknown` per hook lemma."""
    lemmas = sorted({f.hook_lemma for f in info.fields if f.hook_lemma})
    if not lemmas:
        return {}
    result = run_lean(backend, directory, f"Hooks_{info.name}", hook_probe_source(info, lemmas))
    reports = axiom_reports(result.output)
    missing = unknown_constants(result.output)
    verdicts = {}
    for lemma in lemmas:
        if lemma in reports:
            verdicts[lemma] = "exists" if clean(reports[lemma]) else "exists-unclean"
        elif lemma in missing:
            verdicts[lemma] = "missing"
        else:
            verdicts[lemma] = "unknown"
    return verdicts


# ---------------------------------------------------------- census re-check


def census_probe_source(info: model.ClauseInfo, field: model.ClauseField, layout: str) -> str:
    term = " ".join(field.wiring.split())
    return (f"import {info.module}\nimport Vsa.Sim.LayoutInstance\n"
            + census.SUPPORT.read_text() + "\n"
            + f"open Vsa.Sim.IHClause {info.namespace}\n"
            + f"census_probe {info.namespace}.Residuals {field.name} at {layout} using {term}\n")


def verify_census(info: model.ClauseInfo, backend: Path, directory: Path,
                  layout: str) -> dict[str, str]:
    verdicts = {}
    for field in info.fields:
        if field.status != "WIRED":
            continue
        name = f"Census_{info.name}_{field.name}"
        result = run_lean(backend, directory, name, census_probe_source(info, field, layout))
        probe = census.classify(census.Field(field.name, field.projection), result,
                                (directory / f"{name}.olean").is_file())
        verdicts[field.name] = probe.verdict
    return verdicts


# ------------------------------------------------------------- suggestions


def candidates(field: model.ClauseField, dischargers: list[str],
               extra: list[tuple[str, str]], kind: str = "extra",
               at_motive_shape: frozenset[str] = frozenset()) -> list[Candidate]:
    """The hook lemma, each `*_of_old` discharger bare and (unless already stated
    as `EvalIHWithM`) through the clause's embedding (`ofWith` for kind `extra`,
    `.toM` for `extraM`), then the `extra` candidates."""
    result = []
    if field.hook_lemma:
        result.append(Candidate(f"exact:{field.hook_lemma}", "exact", field.hook_lemma))
    wrap = "ofWith" if kind == "extra" else ".toM"
    for name in dischargers:
        result.append(Candidate(f"from_old:{name}", "from_old", field.from_old_term(name)))
        if name not in at_motive_shape:
            result.append(Candidate(f"from_old:{wrap}∘{name}", "from_old",
                                    field.from_old_term(name, wrap)))
    for kind, payload in extra:
        term = payload if kind == "exact" else field.from_old_term(payload)
        result.append(Candidate(f"{kind}:{payload}", kind, term))
    return result


def draft_source(info: model.ClauseInfo, drafts: dict[str, list[Candidate]]
                 ) -> tuple[str, dict[str, tuple[int, int]]]:
    """The per-clause draft module and each candidate theorem's line range."""
    lines = model.module_header(info).splitlines()
    lines += ["/-! Candidate proofs drafted by `scripts/ih_clause_status.py --suggest`;",
              "review before moving anything into `Vsa/`. -/", ""]
    ranges: dict[str, tuple[int, int]] = {}
    for case, options in drafts.items():
        field = info.field(case)
        for index, option in enumerate(options, start=1):
            name = f"draft_{case}_{index}"
            start = len(lines) + 1
            lines.append(f"/-- `{case}` candidate {index}: `{option.label}`. -/")
            lines.append(f"theorem {name} :")
            lines.extend((model.indent(field.field_type, 4) + " :=").splitlines())
            lines.extend(model.indent(option.term, 2).splitlines())
            lines.append(f"#print axioms {name}")
            lines.append("")
            ranges[name] = (start, len(lines))
    lines.append(f"end {info.namespace}")
    return "\n".join(lines) + "\n", ranges


def evaluate_drafts(info: model.ClauseInfo, drafts: dict[str, list[Candidate]],
                    output: str, ranges: dict[str, tuple[int, int]]) -> dict[str, dict]:
    """Per field: the first axiom-clean candidate, or the first failure detail."""
    reports = axiom_reports(output)
    errors = error_lines(output)
    results: dict[str, dict] = {}
    for case, options in drafts.items():
        found = ""
        details = []
        for index, option in enumerate(options, start=1):
            name = f"draft_{case}_{index}"
            qualified = f"{info.namespace}.{name}"
            start, end = ranges[name]
            local_errors = [msg for line, msg in errors if start <= line <= end]
            axioms = reports.get(qualified)
            if axioms is not None and clean(axioms) and not local_errors:
                found = option.label
                break
            reason = local_errors[0] if local_errors else (
                "unclean axioms" if axioms is not None else "no axiom report")
            details.append(f"{option.label}: {reason}")
        results[case] = {"candidate": found, "detail": "; ".join(details)[:400]}
    return results


def _candidate_inputs(
    info: model.ClauseInfo, drafts: dict[str, list[Candidate]]
) -> tuple[attempt_receipts.CandidateInput, ...]:
    result = []
    for case, options in drafts.items():
        field = info.field(case)
        target = f"{info.namespace}.Residuals.{case}"
        for index, option in enumerate(options, start=1):
            result.append(
                attempt_receipts.CandidateInput(
                    target=target,
                    theorem=f"{info.namespace}.draft_{case}_{index}",
                    label=option.label,
                    statement=attempt_receipts.Blob.from_text(
                        model.indent(field.field_type, 4)
                    ),
                    candidate=attempt_receipts.Blob.from_text(model.indent(option.term, 2)),
                )
            )
    return tuple(result)


def run_candidate_lean(
    info: model.ClauseInfo,
    backend: Path,
    directory: Path,
    name: str,
    source: str,
    drafts: dict[str, list[Candidate]],
    *,
    rerun_reason: str | None = None,
    inherited_lean_path: str | None = None,
) -> tuple[census.LeanResult, Path, str]:
    """Compile one generated candidate module and append its attempt receipt."""
    targets = tuple(f"{info.namespace}.Residuals.{case}" for case in drafts)
    candidates_ = _candidate_inputs(info, drafts)
    source_ = attempt_receipts.Blob.from_text(source)
    capture_started = time.monotonic()
    before = attempt_receipts.capture_build_snapshot(
        ROOT,
        backend,
        source,
        inherited_lean_path,
        (Path(__file__), Path(census.__file__)),
    )
    capture_before_seconds = time.monotonic() - capture_started
    log_path = directory / f"{name}.log"
    log_path.unlink(missing_ok=True)
    started_at = datetime.now(timezone.utc).isoformat()
    started = time.monotonic()
    try:
        result = run_lean(backend, directory, name, source)
    except (OSError, build_private.BuildError, KeyboardInterrupt) as error:
        wall = time.monotonic() - started
        diagnostics = str(error)
        try:
            saved_diagnostics = log_path.read_text(encoding="utf-8")
        except (OSError, UnicodeError):
            saved_diagnostics = ""
        if saved_diagnostics:
            diagnostics = saved_diagnostics
        capture_started = time.monotonic()
        after = attempt_receipts.capture_build_snapshot(
            ROOT,
            backend,
            source,
            inherited_lean_path,
            (Path(__file__), Path(census.__file__)),
        )
        capture_after_seconds = time.monotonic() - capture_started
        receipt = attempt_receipts.make_receipt(
            targets=targets,
            source=source_,
            candidates=candidates_,
            before=before,
            after=after,
            started_at=started_at,
            finished_at=datetime.now(timezone.utc).isoformat(),
            wall_seconds=wall,
            returncode=None,
            diagnostics=diagnostics,
            failure_class=attempt_receipts.classify_exception(error),
            rerun_reason=rerun_reason,
            capture_before_seconds=capture_before_seconds,
            capture_after_seconds=capture_after_seconds,
        )
        attempt_receipts.write_receipt(directory.parent / "attempts", receipt)
        raise
    wall = time.monotonic() - started
    capture_started = time.monotonic()
    after = attempt_receipts.capture_build_snapshot(
        ROOT,
        backend,
        source,
        inherited_lean_path,
        (Path(__file__), Path(census.__file__)),
    )
    capture_after_seconds = time.monotonic() - capture_started
    failure_class = attempt_receipts.classify_result(result.returncode, result.output)
    before_identity = attempt_receipts.comparison_payload(
        targets, source_, candidates_, before
    )
    after_identity = attempt_receipts.comparison_payload(
        targets, source_, candidates_, after
    )
    if (
        failure_class in ("success", "compiler_diagnostic")
        and (
            attempt_receipts.has_stale_inputs(before)
            or attempt_receipts.has_stale_inputs(after)
            or (
                before_identity != after_identity
                and (before_identity is not None or after_identity is not None)
            )
        )
    ):
        failure_class = "stale_or_missing_dependency"
    receipt = attempt_receipts.make_receipt(
        targets=targets,
        source=source_,
        candidates=candidates_,
        before=before,
        after=after,
        started_at=started_at,
        finished_at=datetime.now(timezone.utc).isoformat(),
        wall_seconds=wall,
        returncode=result.returncode,
        diagnostics=result.output,
        failure_class=failure_class,
        rerun_reason=rerun_reason,
        capture_before_seconds=capture_before_seconds,
        capture_after_seconds=capture_after_seconds,
    )
    path = attempt_receipts.write_receipt(directory.parent / "attempts", receipt)
    return result, path, failure_class


def bounded_engines(key: str, encoding: str, lemma: str) -> dict[str, str]:
    """Run houdini_ih / autoprove with the field registered at `encoding`."""
    try:
        sys.path.insert(0, str(ROOT / "scripts"))
        import houdini_ih as houdini  # noqa: PLC0415
        import autoprove  # noqa: PLC0415
    except Exception as error:  # noqa: BLE001 - engines are optional
        return {"houdini": f"UNSUPPORTED: engine unavailable ({error})",
                "autoprove": "UNSUPPORTED: engine unavailable"}
    houdini.FIELD_REGISTRY[key] = (encoding, lemma)
    autoprove.FIELD_MAP[key] = (encoding, lemma)
    try:
        first = houdini.run_field(key)
        second = autoprove.run_field(key, do_transcribe=False, do_lean=False, block_llm=False)
    finally:
        houdini.FIELD_REGISTRY.pop(key, None)
        autoprove.FIELD_MAP.pop(key, None)
    return {"houdini": f"{first['verdict']}: {first['detail']}",
            "autoprove": f"{second['verdict']}: {second['detail']}"}


def outcome(lean_candidate: str, lean_ran: bool, houdini: str, autoprove: str) -> str:
    if lean_candidate:
        return "DIRECT"
    verdicts = [houdini.split(":", 1)[0], autoprove.split(":", 1)[0]]
    if any(v in ("PROVABLE-DIRECT", "PROVED-DIRECT") for v in verdicts):
        return "DIRECT"
    if any(v in ("IH-FOUND", "PROVED-WITH-IH", "PROVED-VIA-LLM") for v in verdicts):
        return "WITH-IH"
    if lean_ran or any(v in ("IH-NOT-FOUND", "NEEDS-LLM") for v in verdicts):
        return "FAILED"
    return "UNSUPPORTED"


def suggest(info: model.ClauseInfo, backend: Path | None, directory: Path,
            dischargers: list[str], extra: list[tuple[str, str]],
            targets: dict[str, str], trivial: set[str], *,
            rerun_reason: str | None = None,
            inherited_lean_path: str | None = None) -> list[dict[str, str]]:
    open_fields = [f for f in info.fields if f.status in ("HOOK", "MANUAL", "STALE")]
    shaped = frozenset(model.dischargers_at_motive_shape())
    drafts = {f.name: candidates(f, dischargers, extra, info.kind, shaped) for f in open_fields}
    source, ranges = draft_source(info, drafts)
    draft_path = directory / "drafts" / f"Draft_{info.name}.lean"
    draft_path.parent.mkdir(parents=True, exist_ok=True)
    draft_path.write_text(source)
    lean_results: dict[str, dict] = {}
    attempt_receipt = ""
    if backend is not None and drafts:
        result, receipt_path, failure_class = run_candidate_lean(
            info,
            backend,
            draft_path.parent,
            f"Draft_{info.name}",
            source,
            drafts,
            rerun_reason=rerun_reason,
            inherited_lean_path=inherited_lean_path,
        )
        attempt_receipt = str(receipt_path)
        if failure_class == "stale_or_missing_dependency":
            lean_results = {
                case: {
                    "candidate": "",
                    "detail": "not accepted: stale or changing build inputs",
                }
                for case in drafts
            }
        else:
            lean_results = evaluate_drafts(info, drafts, result.output, ranges)
    rows = []
    for field in open_fields:
        key = f"IHClause.{info.name}.{field.name}"
        encoding = targets.get(field.name) or targets.get("*")
        if not encoding:
            if model.predicate_is_trivial(info.pred, trivial):
                note = "predicate retains nothing; the step is a Lean from_old wiring"
            else:
                note = model.fragment_reason(field, info)
            encoding = f"encode-gap:{note}"
        engines = bounded_engines(key, encoding, field.projection)
        lean = lean_results.get(field.name, {"candidate": "", "detail": "not run (no --backend)"})
        rows.append({
            "clause": info.name, "field": field.name, "status": field.status,
            "outcome": outcome(lean["candidate"], bool(lean_results), engines["houdini"],
                               engines["autoprove"]),
            "lean_candidate": lean["candidate"], "lean_detail": lean["detail"],
            "houdini": engines["houdini"], "autoprove": engines["autoprove"],
            "encoding": encoding, "draft": str(draft_path),
            "evidence": str(draft_path.with_suffix(".log")) if lean_results else "",
            "attempt_receipt": attempt_receipt,
        })
    return rows


# ------------------------------------------------------------------ report


def status_rows(model_: dict[str, model.ClauseInfo], hooks: dict[str, dict[str, str]],
                census_: dict[str, dict[str, str]], source_scan: bool) -> list[dict[str, str]]:
    rows = []
    for info in model_.values():
        for field in info.fields:
            hook_source = ""
            if field.hook_lemma and source_scan:
                hook_source = "declared" if declared_in_source(field.hook_lemma) else "missing"
            evidence = ""
            if field.status == "WIRED":
                evidence = f"{info.path}:{field.wiring_line}"
            rows.append({
                "clause": info.name, "field": field.name, "constructor": field.constructor,
                "relation": field.relation, "tag": field.tag, "status": field.status,
                "hook_lemma": field.hook_lemma, "hook_source": hook_source,
                "hook_backend": hooks.get(info.name, {}).get(field.hook_lemma, ""),
                "wiring": " ".join(field.wiring.split()),
                "census": census_.get(info.name, {}).get(field.name, ""),
                "evidence": evidence,
            })
    return rows


def summary(model_: dict[str, model.ClauseInfo], rows: list[dict[str, str]],
            suggestions: list[dict[str, str]]) -> str:
    total = sum(len(i.fields) for i in model_.values())
    lines = [f"IH clause status: {len(model_)} clause(s), {total} residual field(s)"]
    for info in model_.values():
        counts = info.counts()
        guard = f" guard={info.guard}" if info.guard else ""
        lines.append(
            f"  {info.name:<12} {info.kind}={info.pred:<24}{guard} "
            + " ".join(f"{s} {counts[s]}" for s in model.STATUSES)
            + f"  closed={'yes' if info.closed else 'no'} module={info.module_state}")
        hooks = [r for r in rows if r["clause"] == info.name and r["hook_lemma"]]
        if hooks:
            ids = sorted({r["hook_lemma"].rsplit(".", 1)[0] for r in hooks})
            src = sorted({r["hook_source"] or "not scanned" for r in hooks})
            back = sorted({r["hook_backend"] or "not probed" for r in hooks})
            lines.append(f"    hooks: {', '.join(ids)}.<case> ({len(hooks)})"
                         f" source: {'/'.join(src)}; backend: {'/'.join(back)}")
        census_ = sorted({r["census"] for r in rows if r["clause"] == info.name and r["census"]})
        if census_:
            lines.append(f"    census re-check: {', '.join(census_)}")
        mine = [s for s in suggestions if s["clause"] == info.name]
        if mine:
            counts_ = {o: sum(s["outcome"] == o for s in mine) for o in OUTCOMES}
            lines.append("    suggest: " + " ".join(f"{o} {n}" for o, n in counts_.items()))
            for item in mine:
                if item["lean_candidate"]:
                    lines.append(f"      {item['field']}: DIRECT via {item['lean_candidate']}")
    return "\n".join(lines)


def write_tsv(path: Path, columns: tuple[str, ...], rows: list[dict[str, str]]) -> None:
    with path.open("w") as stream:
        stream.write("\t".join(columns) + "\n")
        for row in rows:
            stream.write("\t".join(str(row.get(c, "")).replace("\t", " ").replace("\n", " ")
                                   for c in columns) + "\n")


def parse_candidate(text: str) -> tuple[str, str]:
    kind, payload = generator.parse_tag(text)
    if kind not in ("from_old", "exact"):
        raise argparse.ArgumentTypeError("candidate must be from_old:<term> or exact:<term>")
    return kind, payload


def parse_target(text: str) -> tuple[str, str]:
    case, sep, encoding = text.partition("=")
    if not sep or not case or not encoding:
        raise argparse.ArgumentTypeError("expected <case|*>=<encoding>")
    return case, encoding


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tsv", type=Path, default=generator.TSV)
    parser.add_argument("--clause", action="append", default=[])
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT,
                        help="directory for status/suggest TSV+JSON, Lean probes and drafts")
    parser.add_argument("--backend", type=Path,
                        help="full private backend or proof_slice overlay with the clause modules")
    parser.add_argument("--layout", default=LAYOUT, type=census.lean_identifier)
    parser.add_argument("--no-source-scan", action="store_true",
                        help="skip the source scan for hook lemmas")
    parser.add_argument("--verify-census", action="store_true",
                        help="re-check each WIRED wiring through the census elaborator")
    parser.add_argument("--suggest", action="store_true",
                        help="draft and check candidate proofs for HOOK/MANUAL fields")
    parser.add_argument("--candidate", action="append", default=[], type=parse_candidate,
                        help="extra from_old:<term> or exact:<term> candidate for --suggest")
    parser.add_argument("--bounded-target", action="append", default=[], type=parse_target,
                        help="<case|*>=<encoding> for houdini_ih/autoprove (e.g. valuerepr-copy:str)")
    parser.add_argument("--rerun-reason",
                        help="optional reason for deliberately repeating a candidate attempt")
    parser.add_argument("--summary", action="store_true", help="print the summary only")
    parser.add_argument("--json", action="store_true", help="print the JSON report")
    args = parser.parse_args(argv)
    try:
        model_ = model.load_model(args.tsv, clauses=args.clause or None)
        hooks: dict[str, dict[str, str]] = {}
        census_: dict[str, dict[str, str]] = {}
        suggestions: list[dict[str, str]] = []
        backend = args.backend.resolve() if args.backend else None
        lean_dir = args.output / "lean"
        if backend is not None:
            for info in model_.values():
                hooks[info.name] = probe_hooks(info, backend, lean_dir)
                if args.verify_census:
                    census_[info.name] = verify_census(info, backend, lean_dir, args.layout)
        elif args.verify_census:
            parser.error("--verify-census requires --backend")
        rows = status_rows(model_, hooks, census_, not args.no_source_scan)
        if args.suggest:
            dischargers = model.from_old_dischargers()
            trivial = model.trivial_predicates()
            for info in model_.values():
                suggestions += suggest(info, backend, args.output, dischargers, args.candidate,
                                       dict(args.bounded_target), trivial,
                                       rerun_reason=args.rerun_reason,
                                       inherited_lean_path=os.environ.get("LEAN_PATH", ""))
        text = summary(model_, rows, suggestions)
        if args.summary and not (args.suggest or backend):
            print(text)
            return 0
        args.output.mkdir(parents=True, exist_ok=True)
        write_tsv(args.output / "ih_clause_status.tsv", STATUS_COLUMNS, rows)
        report = {
            "tsv": str(args.tsv),
            "backend": str(backend) if backend else None,
            "backend_manifest_sha256": build_private.hash_file(backend / build_private.MANIFEST_NAME)
            if backend and (backend / build_private.MANIFEST_NAME).is_file() else None,
            "clauses": {name: {**asdict(info), "fields": [asdict(f) for f in info.fields]}
                        for name, info in model_.items()},
            "status": rows,
            "suggest": suggestions,
        }
        (args.output / "ih_clause_status.json").write_text(json.dumps(report, indent=2) + "\n")
        if args.suggest:
            write_tsv(args.output / "ih_clause_suggest.tsv", SUGGEST_COLUMNS, suggestions)
        print(json.dumps(report, indent=2) if args.json else text)
        print(f"Evidence: {args.output / 'ih_clause_status.tsv'}")
        return 0
    except (ValueError, OSError, build_private.BuildError) as error:
        print(f"ih_clause_status failed: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
