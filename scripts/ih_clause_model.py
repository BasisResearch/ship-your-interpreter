#!/usr/bin/env python3
"""Field model of the generated induction-hypothesis clause residuals.

Every clause in `scripts/ih_clauses.tsv` emits `Vsa.Sim.IHClause.<Name>.Residuals`
with one field per recursor case (`scripts/gen_ih_clause.py`).  This module is
the shared read-only view of those fields for the Level-4 automation
(`ih_clause_status.py`, `ih_clause_fuzz.py`, `ih_clause_ledger.py`): the case
model comes from the generator itself, the wiring from the generated module,
and the discharger vocabulary from `Vsa/Sim/IHClauseSupport.lean`.  Nothing
here runs Lean.
"""

from __future__ import annotations

import re
from dataclasses import asdict, dataclass
from pathlib import Path

try:
    from scripts import gen_ih_clause as generator
except ModuleNotFoundError:  # invoked as a script
    import gen_ih_clause as generator  # type: ignore[no-redef]

ROOT = Path(__file__).resolve().parents[1]
SUPPORT = ROOT / "Vsa/Sim/IHClauseSupport.lean"
GENERIC_NAMESPACE = "Vsa.Sim.IHClauseGeneric"
STATUSES = ("WIRED", "HOOK", "MANUAL", "STALE")
MODULE_STATES = ("current", "stale", "missing")
# The statement fragment statement_fuzz.py / smt_check.py can express: Mem,
# BitVec, StackOK and address windows.  A clause step concludes a motive.
FRAGMENT_REASON = (
    "the step concludes `m{relation} …` = `{guard}EvalIHWithM extraM` (kind `{kind}`, "
    "predicate `{pred}`) over machine runs (∀-closed Config contract); outside "
    "the address-map fragment"
)
WIRED_TAGS = ("from_old", "exact", "unguarded")
KINDS = ("extra", "extraM")


@dataclass(frozen=True)
class ClauseField:
    """One residual field of a clause's `Residuals` record."""

    clause: str
    name: str
    projection: str
    module: str
    constructor: str
    relation: str
    children: int
    binders: tuple[str, ...]
    tag: str
    kind: str
    payload: str
    status: str
    hook_lemma: str
    wiring: str
    wiring_line: int
    field_type: str
    guard: str = ""

    @property
    def hypothesis_names(self) -> list[str]:
        olds = [f"old_{i + 1}" for i in range(self.children)]
        ihs = [f"ih_{i + 1}" for i in range(self.children)]
        return olds + ["hOld"] + ihs + (["hg"] if self.guard else [])

    def from_old_term(self, discharger: str, wrap: str = "") -> str:
        """The field value `fun <binders> <olds> hOld <ihs> [_hg] => <discharger> hOld`.

        `wrap` post-composes an adapter: `ofWith` (kind `extra`) or `.toM`.
        """
        names = ["_" + n for n in self.binders]
        for hyp in self.hypothesis_names:
            names.append(hyp if hyp == "hOld" else "_" + hyp)
        body = f"{discharger} hOld"
        if wrap == ".toM":
            body = f"({body}).toM"
        elif wrap:
            body = f"{wrap} ({body})"
        return f"fun {' '.join(names)} =>\n    {body}"


@dataclass(frozen=True)
class ClauseInfo:
    """A declared clause with its generated module and fields."""

    name: str
    kind: str
    pred: str
    notes: str
    guard: str
    module: str
    namespace: str
    path: str
    module_state: str
    closed: bool
    opens: tuple[str, ...]
    fields: tuple[ClauseField, ...]

    def field(self, name: str) -> ClauseField:
        for field in self.fields:
            if field.name == name:
                return field
        raise KeyError(f"{self.name}: no field {name}")

    def counts(self) -> dict[str, int]:
        return {status: sum(f.status == status for f in self.fields) for status in STATUSES}


def module_name(clause: str) -> str:
    return f"Vsa.Sim.rows.IHClause_{clause}"


def namespace(clause: str) -> str:
    return f"Vsa.Sim.IHClause.{clause}"


def hook_lemma(payload: str, case: str) -> str:
    return f"{GENERIC_NAMESPACE}.{payload}.{case}"


def strip_comments(source: str) -> str:
    """Blank Lean comments (line and nested block), keeping line structure."""
    out: list[str] = []
    depth = 0
    previous = 0
    for match in re.finditer(r'"(?:\\.|[^"\\])*"|/-|-/|--[^\n]*', source):
        skipped = source[previous:match.start()]
        out.append(skipped if depth == 0 else "\n" * skipped.count("\n"))
        token = match.group()
        if token == "/-":
            depth += 1
        elif token == "-/" and depth:
            depth -= 1
        elif depth == 0 and token.startswith('"'):
            out.append(token)
        previous = match.end()
    tail = source[previous:]
    out.append(tail if depth == 0 else "\n" * tail.count("\n"))
    return "".join(out)


def trivial_predicates(support: Path = SUPPORT) -> set[str]:
    """`EvalExtra` abbreviations in the support module that retain nothing."""
    text = strip_comments(support.read_text())
    pattern = r"abbrev\s+(\w+)\s*:\s*EvalExtra\s*:=\s*fun(?:\s+_)+\s*=>\s*True\b"
    return set(re.findall(pattern, text))


def from_old_dischargers(support: Path = SUPPORT) -> list[str]:
    """Theorems `<name>_of_old` in the support module: `from_old` candidates."""
    text = strip_comments(support.read_text())
    return re.findall(r"^theorem\s+(\w+_of_old)\b", text, re.M)


def dischargers_at_motive_shape(support: Path = SUPPORT) -> set[str]:
    """The `*_of_old` dischargers already stated as `EvalIHWithM` (no embedding needed)."""
    text = strip_comments(support.read_text())
    result = set()
    for match in re.finditer(r"^theorem\s+(\w+_of_old)\b(.*?)(?=^theorem|^end |\Z)", text, re.M | re.S):
        statement = match.group(2).split(":=", 1)[0]
        if "EvalIHWithM" in statement:
            result.add(match.group(1))
    return result


def predicate_is_trivial(pred: str, trivial: set[str]) -> bool:
    text = pred.strip()
    if text in trivial:
        return True
    return re.fullmatch(r"fun(?:\s+_)+\s*=>\s*True", text) is not None


def parse_wiring(module_text: str) -> dict[str, tuple[str, int]]:
    """Fields filled in the generated `Residuals.ofUnwired` (term, line)."""
    lines = module_text.splitlines()
    start = next((i for i, l in enumerate(lines) if l.startswith("theorem Residuals.ofUnwired")), None)
    if start is None:
        return {}
    wired: dict[str, tuple[str, int]] = {}
    index = start + 1
    while index < len(lines) and not lines[index].startswith(("theorem", "#print", "/-", "end ")):
        match = re.match(r"^  (\w+) :=(.*)$", lines[index])
        if match:
            case, rest = match.group(1), match.group(2).strip()
            if rest:
                if rest != case:
                    wired[case] = (rest, index + 1)
                index += 1
                continue
            term: list[str] = []
            line = index + 1
            index += 1
            while index < len(lines) and lines[index].startswith("    "):
                term.append(lines[index].strip())
                index += 1
            wired[case] = (" ".join(term), line)
            continue
        index += 1
    return wired


def fragment_reason(field: ClauseField, info: "ClauseInfo") -> str:
    guard = f"{info.guard} → " if info.guard else ""
    return FRAGMENT_REASON.format(relation=field.relation, pred=info.pred, kind=info.kind,
                                  guard=guard)


def load_model(tsv: Path = generator.TSV, assembly: Path = generator.bundle.ASSEMBLY,
               output_dir: Path = generator.OUTPUT_DIR,
               clauses: list[str] | None = None) -> dict[str, ClauseInfo]:
    """Every declared clause with its fields and their statuses."""
    cases, signatures = generator.load_cases(assembly)
    result: dict[str, ClauseInfo] = {}
    for clause in generator.load_clauses(tsv):
        if clauses and clause.name not in clauses:
            continue
        rendered = generator.render_clause(clause, cases, signatures)
        path = output_dir / f"IHClause_{clause.name}.lean"
        if not path.exists():
            state, text = "missing", ""
        else:
            text = path.read_text()
            state = "current" if text == rendered else "stale"
        wiring = parse_wiring(text or rendered)
        fields = []
        for case in cases:
            if not (case.conclusion.relation == "EvalE"
                    or clause.motive_body(case.conclusion.relation) is not None):
                continue
            kind, payload = generator.parse_tag(clause.tag(case.name))
            term, line = wiring.get(case.name, ("", 0))
            if kind in WIRED_TAGS:
                status = "WIRED" if term and state == "current" else "STALE"
            elif kind == "generic":
                status = "HOOK"
            else:
                status = "MANUAL"
            fields.append(ClauseField(
                clause=clause.name, name=case.name,
                projection=f"{namespace(clause.name)}.Residuals.{case.name}",
                module=module_name(clause.name), constructor=case.constructor,
                relation=case.conclusion.relation, children=len(case.children),
                binders=tuple(case.binder_names), tag=clause.tag(case.name), kind=kind, payload=payload, status=status,
                hook_lemma=hook_lemma(payload, case.name) if kind == "generic" else "",
                wiring=term, wiring_line=line, field_type=generator.field_type(case),
                guard=clause.guard))
        result[clause.name] = ClauseInfo(
            name=clause.name, kind=getattr(clause, "kind", "extra"), pred=clause.pred,
            notes=clause.notes, guard=clause.guard,
            module=module_name(clause.name), namespace=namespace(clause.name),
            path=str(path), module_state=state,
            closed="theorem closed" in (text or rendered),
            opens=tuple(re.findall(r"^open .*$", text or rendered, re.M)),
            fields=tuple(fields))
    unknown = sorted(set(clauses or []) - set(result))
    if unknown:
        raise ValueError(f"unknown clause(s): {', '.join(unknown)}")
    return result


def field_rows(model: dict[str, ClauseInfo]) -> list[dict[str, object]]:
    rows = []
    for info in model.values():
        for field in info.fields:
            row = asdict(field)
            row.pop("field_type")
            rows.append(row)
    return rows


def module_header(info: ClauseInfo, imports: tuple[str, ...] = ()) -> str:
    """Imports, namespace and the generated module's `open` block."""
    lines = [f"import {info.module}"] + [f"import {m}" for m in imports if m != info.module]
    lines += ["", f"namespace {info.namespace}", ""]
    lines += list(info.opens) + ["", 'local notation "SpecSt" => Vsa.While.St', ""]
    return "\n".join(lines) + "\n"


def indent(text: str, spaces: int) -> str:
    return "\n".join(" " * spaces + line if line else line for line in text.splitlines())


def statement_module(info: ClauseInfo, field: ClauseField, definition: str) -> str:
    """A hermetic module defining the field's step as `def <definition> (L : Layout) : Prop`.

    The file is the statement input of `statement_fuzz.py --file … --prop … --layout`.
    """
    return (
        module_header(info)
        + f"/-- The `{info.name}` clause step for `{field.constructor}` (field `{field.name}`). -/\n"
        f"def {definition} (_L : Layout) : Prop :=\n{indent(field.field_type, 2)}\n\n"
        f"end {info.namespace}\n"
    )
