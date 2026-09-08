#!/usr/bin/env python3
"""Generate one induction-hypothesis clause module per `scripts/ih_clauses.tsv` line.

A clause is an `EvalExtra` predicate recursed through the mutual `EvalE` family
as the `EvalIHWith` motive.  For clause `<Name>` the module
`Vsa/Sim/rows/IHClause_<Name>.lean` (namespace `Vsa.Sim.IHClause.<Name>`) holds

* `extraM : EvalExtraM` and the nine clause motives `mEvalE … mExecSeq`
  (`mEvalE` is `EvalIHWithM extraM`, under the table's `guard` on the
  expression when one is declared; a kind-`extra` clause also has
  `extra : EvalExtra`, `extraM` = its `sp`/`m0`-blind embedding, and `ofWith`
  = `EvalIHWith.toM`; the other eight motives are `True` unless the TSV
  overrides them);
* `structure Residuals (L : Layout) : Prop` with ONE field per recursor case
  whose parent relation has a non-`True` clause motive — the case's clause step:
  constructor binders → old child IHs → old parent (`hOld`) → clause child IHs
  → clause parent.  Field names are the `TermCases` premise names;
* `of_residuals` / `execSeq_of_residuals`: the recursor application with the
  product motive (old ∧ clause), so declaring a clause never breaks the build;
* `Residuals.ofUnwired` (and `closed` when nothing is unwired) for the fields
  the TSV wires to a discharger.

The case list and every binder come from `term_sim_of_cases`
(`Vsa/Sim/TermSimAssembly.lean`), the same source `gen_term_case_bundle.py`
reads, so the two cannot drift.
"""

from __future__ import annotations

import argparse
import difflib
import pathlib
import re
import sys

try:
    from scripts import gen_term_case_bundle as bundle
except ModuleNotFoundError:  # invoked as a script
    import gen_term_case_bundle as bundle  # type: ignore[no-redef]


ROOT = pathlib.Path(__file__).resolve().parents[1]
TSV = ROOT / "scripts/ih_clauses.tsv"
OUTPUT_DIR = ROOT / "Vsa/Sim/rows"
BASE_NAMESPACE = "Vsa.Sim.TermSimAssembly"
RELATIONS = [
    "EvalE", "EvalArgs", "Call", "ExecS", "ExecInit",
    "ForLoop", "ForCond", "ExecStep", "ExecSeq",
]
COLUMNS = ["name", "kind", "pred", "imports", "motives", "guard", "steps", "notes"]
KINDS = ("extra", "extraM")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*$")
TAG_KINDS = ("manual", "generic", "from_old", "exact", "unguarded")


# ----------------------------------------------------------------- TSV schema


class Clause:
    """One declared clause."""

    def __init__(self, name: str, pred: str, imports: list[str],
                 motives: dict[str, str], steps: dict[str, str], notes: str,
                 kind: str = "extra", guard: str = "") -> None:
        self.name = name
        self.kind = kind
        self.pred = pred
        self.imports = imports
        self.motives = motives
        self.guard = guard
        self.steps = steps
        self.notes = notes

    def eval_motive_body(self, params: str = "st d env e st' v") -> str:
        """The `EvalE` motive body: `EvalIHWithM extraM …`, under the guard when declared."""
        body = f"EvalIHWithM extraM {params}"
        return f"{self.guard} → {body}" if self.guard else body

    def motive_body(self, relation: str) -> str | None:
        """The clause motive body for a non-`EvalE` relation, or None for `True`."""
        return self.motives.get(relation)

    def tag(self, case: str) -> str:
        return self.steps.get(case, self.steps.get("*", "manual"))


def parse_tag(tag: str) -> tuple[str, str]:
    """Split `kind[:payload]`; validate the kind and payload presence."""
    kind, _, payload = tag.partition(":")
    if kind not in TAG_KINDS:
        raise ValueError(f"unknown step tag kind {kind!r} (expected one of {TAG_KINDS})")
    if kind == "manual" and payload:
        raise ValueError("manual takes no payload")
    if kind != "manual" and not payload:
        raise ValueError(f"step tag {kind!r} needs a payload")
    return kind, payload


def parse_pairs(cell: str, what: str) -> dict[str, str]:
    """Parse `key=value;key=value` ('-' = empty); keys must be unique."""
    result: dict[str, str] = {}
    if cell.strip() in ("", "-"):
        return result
    for item in cell.split(";"):
        item = item.strip()
        if not item:
            continue
        key, sep, value = item.partition("=")
        key, value = key.strip(), value.strip()
        if not sep or not key or not value:
            raise ValueError(f"{what}: expected key=value, got {item!r}")
        if key in result:
            raise ValueError(f"{what}: duplicate key {key!r}")
        result[key] = value
    return result


def load_clauses(tsv: pathlib.Path = TSV) -> list[Clause]:
    """Read the clause table; validate names, tags and relation keys."""
    clauses: list[Clause] = []
    columns: list[str] | None = None
    for number, line in enumerate(tsv.read_text().splitlines(), start=1):
        if not line.strip() or line.startswith("#"):
            continue
        if line.startswith("name\t"):
            columns = [c.strip() for c in line.split("\t")]
            unknown = sorted(set(columns) - set(COLUMNS))
            if unknown or "name" not in columns or "pred" not in columns:
                raise ValueError(f"{tsv.name}:{number}: bad header columns {columns}")
            continue
        if columns is None:
            raise ValueError(f"{tsv.name}:{number}: a header row (name\t…) must precede rows")
        cells = line.split("\t")
        if len(cells) < len(columns):
            raise ValueError(f"{tsv.name}:{number}: expected {len(columns)} columns")
        row = {c: "" for c in COLUMNS}
        row.update(zip(columns, cells))
        kind = row["kind"].strip() or "extra"
        if kind not in KINDS:
            raise ValueError(f"{tsv.name}:{number}: kind must be one of {KINDS}: {kind!r}")
        name = row["name"].strip()
        if not IDENT.match(name) or not name[0].isupper():
            raise ValueError(f"{tsv.name}:{number}: clause name must be CamelCase: {name!r}")
        pred = row["pred"].strip()
        if not pred:
            raise ValueError(f"{tsv.name}:{number}: empty pred")
        imports = [m.strip() for m in row["imports"].split(",") if m.strip() and m.strip() != "-"]
        motives = parse_pairs(row["motives"], f"{tsv.name}:{number} motives")
        for relation in motives:
            if relation not in RELATIONS[1:]:
                raise ValueError(
                    f"{tsv.name}:{number}: motives key {relation!r} is not one of {RELATIONS[1:]}")
        guard = row["guard"].strip()
        if guard == "-":
            guard = ""
        steps = parse_pairs(row["steps"], f"{tsv.name}:{number} steps")
        for case, tag in steps.items():
            if case != "*" and not IDENT.match(case):
                raise ValueError(f"{tsv.name}:{number}: bad case key {case!r}")
            try:
                tag_kind, _ = parse_tag(tag)
            except ValueError as error:
                raise ValueError(f"{tsv.name}:{number}: {error}") from None
            if tag_kind == "unguarded" and not guard:
                raise ValueError(f"{tsv.name}:{number}: unguarded tag needs a guard column")
        clauses.append(Clause(name, pred, imports, motives, steps, row["notes"].strip(), kind,
                              guard))
    names = [clause.name for clause in clauses]
    duplicates = sorted({n for n in names if names.count(n) > 1})
    if duplicates:
        raise ValueError(f"duplicate clause names: {', '.join(duplicates)}")
    return clauses


# ----------------------------------------------------- recursor case structure


class Atom:
    """A motive application `m<Rel> <args>`."""

    def __init__(self, relation: str, args: str) -> None:
        self.relation = relation
        self.args = args

    def render(self, prefix: str) -> str:
        return f"{prefix}m{self.relation} {self.args}"


class Case:
    """One recursor minor premise: binders, child IHs, conclusion."""

    def __init__(self, name: str, binders: list[tuple[list[str], str]],
                 children: list[Atom], conclusion: Atom) -> None:
        self.name = name
        self.binders = binders
        self.children = children
        self.conclusion = conclusion

    @property
    def binder_names(self) -> list[str]:
        return [n for names, _ in self.binders for n in names]

    @property
    def binder_text(self) -> str:
        return " ".join(f"({' '.join(names)} : {ty})" for names, ty in self.binders)

    @property
    def constructor(self) -> str:
        term = self.conclusion.args.rsplit("(", 1)[1]
        return term.split()[0]


def split_top(text: str, separator: str) -> list[str]:
    """Split on `separator` outside parentheses, braces and brackets."""
    parts: list[str] = []
    depth = 0
    start = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth -= 1
        elif depth == 0 and text.startswith(separator, index):
            parts.append(text[start:index])
            index += len(separator)
            start = index
            continue
        index += 1
    parts.append(text[start:])
    return [part.strip() for part in parts]


def parse_atom(text: str) -> Atom:
    head, _, args = text.strip().partition(" ")
    if not head.startswith("m") or head[1:] not in RELATIONS:
        raise ValueError(f"not a motive application: {text[:60]!r}")
    return Atom(head[1:], args.strip())


def parse_case(name: str, type_source: str) -> Case:
    """Parse `∀ (binders), IH → … → m<Rel> args (Ctor …)`."""
    source = type_source.strip()
    if not source.startswith("∀"):
        raise ValueError(f"{name}: premise is not ∀-closed")
    cursor = 1
    binders: list[tuple[list[str], str]] = []
    while True:
        while cursor < len(source) and source[cursor].isspace():
            cursor += 1
        if cursor >= len(source):
            raise ValueError(f"{name}: unterminated binder list")
        if source[cursor] == "(":
            end = bundle.matching_paren(source, cursor)
            group = source[cursor + 1:end]
            names, sep, ty = group.partition(" : ")
            if not sep:
                raise ValueError(f"{name}: binder without type: {group!r}")
            binders.append((names.split(), ty.strip()))
            cursor = end + 1
        elif source[cursor] == ",":
            cursor += 1
            break
        else:
            raise ValueError(f"{name}: unexpected {source[cursor]!r} in binder list")
    parts = split_top(source[cursor:], "→")
    children = [parse_atom(part) for part in parts[:-1]]
    conclusion = parse_atom(parts[-1])
    return Case(name, binders, children, conclusion)


def motive_signature(source: str, relation: str) -> list[tuple[list[str], str]]:
    """Binders of `def m<Rel>` in the assembly (the relation's motive signature)."""
    marker = f"def m{relation} "
    start = source.index(marker) + len(marker)
    binders: list[tuple[list[str], str]] = []
    cursor = start
    while True:
        while cursor < len(source) and source[cursor].isspace():
            cursor += 1
        if cursor >= len(source) or source[cursor] != "(":
            break
        end = bundle.matching_paren(source, cursor)
        group = source[cursor + 1:end]
        names, sep, ty = group.partition(" : ")
        if not sep:
            raise ValueError(f"m{relation}: binder without type: {group!r}")
        binders.append((names.split(), ty.strip()))
        cursor = end + 1
    if not binders or not binders[-1][0][0].startswith("_h"):
        raise ValueError(f"m{relation}: expected a trailing derivation binder")
    return binders


def load_cases(assembly: pathlib.Path = bundle.ASSEMBLY) -> tuple[list[Case], dict[str, list]]:
    """The recursor cases and motive signatures from the assembly source."""
    source = assembly.read_text()
    binders, _ = bundle.theorem_parts(source, "term_sim_of_cases")
    cases = [parse_case(n, ty) for n, ty in binders if n.startswith("h")]
    if len(cases) != 50:
        raise ValueError(f"expected 50 recursor cases, found {len(cases)}")
    signatures = {relation: motive_signature(source, relation) for relation in RELATIONS}
    return cases, signatures


# -------------------------------------------------------------------- emission


def indent(text: str, spaces: int) -> str:
    prefix = " " * spaces
    return "\n".join(prefix + line if line else line for line in text.splitlines())


def field_type(case: Case) -> str:
    """The clause step: binders → old children → old parent → clause children → clause parent."""
    hyps = [atom.render(f"{BASE_NAMESPACE}.") for atom in case.children]
    hyps.append(case.conclusion.render(f"{BASE_NAMESPACE}."))
    hyps.extend(atom.render("") for atom in case.children)
    lines = [f"∀ {case.binder_text},"]
    for hyp in hyps:
        lines.append(f"  {hyp} →")
    lines.append(f"  {case.conclusion.render('')}")
    return "\n".join(lines)


def hypothesis_names(case: Case) -> tuple[list[str], str, list[str]]:
    olds = [f"old_{i + 1}" for i in range(len(case.children))]
    ihs = [f"ih_{i + 1}" for i in range(len(case.children))]
    return olds, "hOld", ihs


def wiring_term(case: Case, kind: str, payload: str, guard: str = "") -> str:
    """The field value for a wired case.

    `exact`: `payload` at the field type.  `from_old`: `payload hOld` (the
    guard hypothesis `_hg`, when the clause is guarded, is discarded).
    `unguarded` (guarded clauses only): `<term>|<proj_1>|…|<proj_k>` where
    `<term>` has the field's type WITHOUT the guard on the `EvalE` child IHs
    and on the parent, and `proj_i : <guard parent> → <guard child_i>` for the
    i-th `EvalE` child (none for a leaf); the wiring is
    `fun <binders> <olds> hOld <ihs> hg => <term> <binders> <olds> hOld (ih_i (proj_i hg)) …`.
    """
    if kind == "exact":
        return payload
    olds, old, ihs = hypothesis_names(case)
    guard_hyp = ["_hg"] if guard else []
    if kind == "unguarded":
        parts = split_top(payload, "|")
        term, projections = parts[0], parts[1:]
        eval_children = [i for i, atom in enumerate(case.children) if atom.relation == "EvalE"]
        if len(projections) != len(eval_children):
            raise ValueError(
                f"unguarded: case {case.name!r} has {len(eval_children)} guarded child IH(s); "
                f"expected `<term>` followed by that many `|<guard projection>`, got "
                f"{len(projections)}")
        lifted = list(ihs)
        for index, projection in zip(eval_children, projections):
            lifted[index] = f"({ihs[index]} ({projection} hg))"
        names = case.binder_names + olds + [old] + ihs + (["hg"] if projections else ["_hg"])
        args = case.binder_names + olds + [old] + lifted
        return f"fun {' '.join(names)} =>\n  {term} {' '.join(args)}"
    unused = (["_" + n for n in case.binder_names + olds] + [old] + ["_" + n for n in ihs]
              + guard_hyp)
    return f"fun {' '.join(unused)} =>\n  {payload} {old}"


def case_lambda(case: Case, has_field: bool) -> str:
    """The product-motive minor premise for the recursor application."""
    ihs = [f"ih_{i + 1}" for i in range(len(case.children))]
    names = " ".join(case.binder_names + ihs)
    old_args = " ".join(case.binder_names + [f"{ih}.1" for ih in ihs])
    old = f"B.{case.name} {old_args}"
    if not has_field:
        return f"(fun {names} =>\n  And.intro ({old}) True.intro)"
    clause_args = " ".join(case.binder_names + [f"{ih}.1" for ih in ihs] + ["hOld"]
                           + [f"{ih}.2" for ih in ihs])
    return (f"(fun {names} =>\n  have hOld := {old}\n"
            f"  And.intro hOld (R.{case.name} {clause_args}))")


def render_clause(clause: Clause, cases: list[Case],
                  signatures: dict[str, list]) -> str:
    fields = [c for c in cases if c.conclusion.relation == "EvalE"
              or clause.motive_body(c.conclusion.relation) is not None]
    nontrivial = ["EvalE"] + [r for r in RELATIONS[1:] if clause.motive_body(r) is not None]
    for case in clause.steps:
        if case != "*" and case not in {c.name for c in fields}:
            raise ValueError(
                f"clause {clause.name}: step {case!r} is not a case with a non-True parent motive "
                f"(non-True relations: {', '.join(nontrivial)})")
    ns = f"Vsa.Sim.IHClause.{clause.name}"
    always = ["Vsa.Sim.TermCaseBundle", "Vsa.Sim.ExitFootprint", "Vsa.Sim.IHClauseSupport"]
    imports = always + [m for m in clause.imports if m not in always]
    lines = [f"import {m}" for m in imports]
    lines += [
        "",
        "/-!",
        f"# Generated induction-hypothesis clause `{clause.name}`",
        "",
        "Generated by `scripts/gen_ih_clause.py` from `scripts/ih_clauses.tsv` and the",
        "authoritative `term_sim_of_cases` signature. Do not hand-edit.",
        "",
        f"Clause predicate: `{clause.pred}` (kind `{clause.kind}`: "
        + ("an `EvalExtra`, embedded as an `EvalExtraM` through `EvalIHWith.toM`)."
           if clause.kind == "extra" else "an `EvalExtraM`, retained through `EvalIHWithM`)."),
    ]
    if clause.guard:
        lines += [
            "",
            f"Guard: `{clause.guard}` — the `EvalE` motive is `{clause.eval_motive_body()}`;",
            "every clause child IH and the clause parent carry the guard, so a step for",
            "an expression outside the guard is vacuous.",
        ]
    if clause.notes:
        lines += ["", clause.notes]
    lines += [
        "",
        "The old motive (`TermSimAssembly.mEvalE`, …) is consumed for free: every",
        "residual field takes the case's old child IHs and old parent conclusion",
        "beside the clause child IHs. `of_residuals` recurses the product motive",
        "(old ∧ clause) so that a declared clause never breaks the build.",
        "-/",
        "",
        f"namespace {ns}",
        "",
        "open LeanRV64DExecutable Sail",
        "open Register",
        "open Vsa.Machine (MState Config Halts)",
        "open Vsa.Logic",
        "open Vsa.RuntimeRepr",
        "open Vsa.MemRepr",
        "open Vsa.While",
        "open Vsa.Alloc",
        "open Vsa.Refine (Layout Loaded InterpSim)",
        "open Vsa.Sim",
        "open Vsa.Sim.Scaffold",
        "open Vsa.Sim.TermCaseBundle (TermCases)",
        "",
        "local notation \"SpecSt\" => Vsa.While.St",
        "",
        "/-! ## Clause motives -/",
        "",
    ]
    if clause.kind == "extra":
        lines += [
            f"/-- The `{clause.name}` clause retained at the child's actual return. -/",
            f"def extra : EvalExtra := {clause.pred}",
            "",
            "/-- The clause as an `sp`/`m0`-blind `EvalExtraM` (the motive's shape). -/",
            "def extraM : EvalExtraM := fun N A SL φf φc _ sret _ => extra N A SL φf φc sret.toNat",
            "",
            "/-- Embed an `EvalIHWith extra` fact into the clause motive. -/",
            "theorem ofWith {st st' : SpecSt} {d env : Nat} {e : Expr} {v : Value}",
            "    (h : EvalIHWith extra st d env e st' v) : EvalIHWithM extraM st d env e st' v :=",
            "  h.toM",
            "",
        ]
    else:
        lines += [
            f"/-- The `{clause.name}` clause retained at the child's actual return",
            "(`sp`/`m0`-aware). -/",
            f"def extraM : EvalExtraM := {clause.pred}",
            "",
        ]
    for relation in RELATIONS:
        binders = signatures[relation]
        binder_text = " ".join(f"({' '.join(n)} : {ty})" for n, ty in binders)
        params = " ".join(n for names, _ in binders[:-1] for n in names)
        if relation == "EvalE":
            body = clause.eval_motive_body(params)
            doc = ("`EvalE` motive: the clause as an `EvalIHWithM`"
                   + (" under the guard." if clause.guard else "."))
        elif clause.motive_body(relation) is not None:
            body = clause.motive_body(relation)
            doc = f"`{relation}` motive (from the clause table)."
        else:
            body = "True"
            doc = f"`{relation}` motive: no clause declared for this relation."
        lines += [
            f"/-- {doc} -/",
            f"def m{relation} {binder_text} : Prop :=",
            f"  {body}",
            "",
        ]
    lines += [
        "/-! ## Residual clause steps",
        "",
        "One field per recursor case whose parent relation carries a clause motive.",
        "Field names are the `TermCases` premise names; hypotheses are, in order, the",
        "constructor binders, the old child IHs, the old parent conclusion, and the",
        "clause child IHs. -/",
        "",
        "/-- The clause steps not discharged generically. The `Layout` parameter is",
        "the census interface (`scripts/field_census.py`); no field depends on it. -/",
        "structure Residuals (_L : Layout) : Prop where",
    ]
    wired: dict[str, str] = {}
    hooks: list[tuple[str, str]] = []
    for case in fields:
        kind, payload = parse_tag(clause.tag(case.name))
        if kind == "manual":
            note = "Discharger: manual (residual)."
        elif kind == "generic":
            note = (f"Discharger: `generic:{payload}` (hook `wire_{case.name}` below; "
                    f"unwired until agent L2 lands it).")
            hooks.append((case.name, payload))
        elif kind == "from_old":
            note = f"Discharger: wired from the old motive by `{payload}`."
            wired[case.name] = wiring_term(case, kind, payload, clause.guard)
        elif kind == "unguarded":
            note = f"Discharger: wired from the unguarded step `{payload}`."
            try:
                wired[case.name] = wiring_term(case, kind, payload, clause.guard)
            except ValueError as error:
                raise ValueError(f"clause {clause.name}: {error}") from None
        else:
            note = f"Discharger: wired exactly by `{payload}`."
            wired[case.name] = wiring_term(case, kind, payload, clause.guard)
        lines += [
            f"  /-- `{case.name}`: the `{clause.name}` step for `{case.constructor}`",
            f"      (parent relation `{case.conclusion.relation}`). {note} -/",
            f"  {case.name} :",
            indent(field_type(case), 4),
        ]
    lines += [
        "",
        "/-! ## The recursor application (product motive: old ∧ clause) -/",
        "",
        "/-- The clause for every `EvalE` derivation, from the old case bundle and",
        "the clause residuals. -/",
        "theorem of_residuals (B : TermCases) {L : Layout} (R : Residuals L)",
        "    {st : SpecSt} {d : Nat} {env : Addr} {e : Expr} {st' : SpecSt} {v : Value}",
        "    (t : EvalE st d env e st' v) : mEvalE st d env e st' v t :=",
        "  (@EvalE.rec",
    ]
    field_names = {c.name for c in fields}
    lines.append(indent(product_motives(signatures), 4))
    for case in cases:
        lines.append(indent(case_lambda(case, case.name in field_names), 4))
    lines += [
        "    st d env e st' v t).2",
        "",
        "/-- The `ExecSeq`-rooted clause from the same residuals. -/",
        "theorem execSeq_of_residuals (B : TermCases) {L : Layout} (R : Residuals L)",
        "    {st : SpecSt} {d : Nat} {env : Addr} {ss : List Stmt} {st' : SpecSt}",
        "    {status : Status}",
        "    (t : ExecSeq st d env ss st' status) : mExecSeq st d env ss st' status t :=",
        "  (@ExecSeq.rec",
    ]
    lines.append(indent(product_motives(signatures), 4))
    for case in cases:
        lines.append(indent(case_lambda(case, case.name in field_names), 4))
    lines += [
        "    st d env ss st' status t).2",
        "",
    ]
    unwired = [c for c in fields if c.name not in wired]
    if wired:
        lines += [
            "/-! ## Wired dischargers -/",
            "",
            "/-- The residual record from its unwired fields; the wired fields are",
            "supplied by their table dischargers. -/",
            "theorem Residuals.ofUnwired (L : Layout)" + (" : Residuals L where" if not unwired else ""),
        ]
        for case in unwired:
            lines.append(f"    ({case.name} :")
            lines.append(indent(field_type(case), 6) + ")")
        if unwired:
            lines.append("    : Residuals L where")
        for case in fields:
            if case.name in wired:
                lines.append(f"  {case.name} :=")
                lines.append(indent(wired[case.name], 4))
            else:
                lines.append(f"  {case.name} := {case.name}")
        lines.append("")
        if not unwired:
            lines += [
                "/-- Every step is wired: the clause holds of every derivation. -/",
                "theorem closed (B : TermCases) (L : Layout)",
                "    {st : SpecSt} {d : Nat} {env : Addr} {e : Expr} {st' : SpecSt} {v : Value}",
                "    (t : EvalE st d env e st' v) : mEvalE st d env e st' v t :=",
                "  of_residuals B (Residuals.ofUnwired L) t",
                "",
            ]
    if hooks:
        lines += [
            "/-! ## Generic discharger hooks",
            "",
            "Each hook names the generic lemma (agent L2) expected to fill the field.",
            "Wire it by changing the case's table tag to `exact:<lemma>` (or",
            "`from_old:<lemma>` when it consumes only the old parent, `unguarded:<lemma>`",
            "for a leaf lemma stated without the clause guard); the generator",
            "then moves the field into `Residuals.ofUnwired`. -/",
            "",
        ]
        for case_name, tag in hooks:
            lines += [
                f"-- IHCLAUSE-HOOK {clause.name} {case_name} generic:{tag}",
                f"--   expected: `Vsa.Sim.IHClauseGeneric.{tag}.{case_name}` at the type of",
                f"--   `{ns}.Residuals.{case_name}`",
            ]
        lines.append("")
    lines += [
        "#print axioms of_residuals",
        "#print axioms execSeq_of_residuals",
    ]
    if wired and not unwired:
        lines.append("#print axioms closed")
    lines += ["", f"end {ns}", ""]
    return "\n".join(lines)


def product_motives(signatures: dict[str, list]) -> str:
    out = []
    for relation in RELATIONS:
        names = [n for group, _ in signatures[relation] for n in group]
        names[-1] = "h"
        args = " ".join(names)
        out.append(f"(fun {args} => {BASE_NAMESPACE}.m{relation} {args} ∧ m{relation} {args})")
    return "\n".join(out)


def output_path(clause: Clause, output_dir: pathlib.Path = OUTPUT_DIR) -> pathlib.Path:
    return output_dir / f"IHClause_{clause.name}.lean"


def render_all(tsv: pathlib.Path = TSV,
               assembly: pathlib.Path = bundle.ASSEMBLY) -> dict[str, str]:
    cases, signatures = load_cases(assembly)
    return {clause.name: render_clause(clause, cases, signatures)
            for clause in load_clauses(tsv)}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--tsv", type=pathlib.Path, default=TSV)
    parser.add_argument("--output-dir", type=pathlib.Path, default=OUTPUT_DIR)
    parser.add_argument("--clause", action="append", default=[],
                        help="restrict to these clause names")
    parser.add_argument("--check", action="store_true",
                        help="report stale or missing generated modules; exit 1 on drift")
    parser.add_argument("--stdout", action="store_true", help="print instead of writing")
    args = parser.parse_args(argv)
    try:
        rendered = render_all(args.tsv)
    except (ValueError, OSError) as error:
        print(error, file=sys.stderr)
        return 2
    unknown = sorted(set(args.clause) - set(rendered))
    if unknown:
        print(f"unknown clause(s): {', '.join(unknown)}", file=sys.stderr)
        return 2
    selected = {n: t for n, t in rendered.items() if not args.clause or n in args.clause}
    stale = 0
    for name, text in selected.items():
        target = args.output_dir / f"IHClause_{name}.lean"
        if args.stdout:
            sys.stdout.write(text)
            continue
        if args.check:
            current = target.read_text() if target.exists() else ""
            if current != text:
                stale += 1
                print(f"{relative(target)} is stale", file=sys.stderr)
                sys.stderr.writelines(difflib.unified_diff(
                    current.splitlines(True), text.splitlines(True),
                    fromfile=str(relative(target)), tofile="generated"))
            else:
                print(f"{relative(target)}: up to date")
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(text)
        print(f"wrote {relative(target)}")
    return 1 if stale else 0


def relative(path: pathlib.Path) -> pathlib.Path:
    try:
        return path.relative_to(ROOT)
    except ValueError:
        return path


if __name__ == "__main__":
    raise SystemExit(main())
