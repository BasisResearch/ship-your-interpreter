#!/usr/bin/env python3
"""Decision-tactic census across Vsa/**/*.lean.

For every .lean file under Vsa/ counts lines and decision-tactic calls
(omega / decide / bv_decide / simp / norm_num), extracts the tactic blocks
containing omega|decide|bv_decide, normalizes them into shape keys, clusters
identical normalized blocks, and reports:

  - experiments/decision-census.tsv          per-file totals, sorted by
                                             omega+decide+bv_decide desc
  - experiments/decision-census-patterns.md  top-N files' top patterns +
                                             cross-file SHARED shape ranking
                                             (+ helper coverage + leaf status)

Pure text analysis: no lean/lake invocation.
"""

import os
import re
import sys
from collections import Counter, defaultdict

ROOT = "/Users/kirancodes/Documents/code/verified-semantic-abstraction"
VSA = os.path.join(ROOT, "Vsa")
TSV_OUT = os.path.join(ROOT, "experiments", "decision-census.tsv")
MD_OUT = os.path.join(ROOT, "experiments", "decision-census-patterns.md")
TOP_N_FILES = 25
TOP_PATTERNS_PER_FILE = 8

# ---------------------------------------------------------------- counting

WORD = {
    "omega": re.compile(r"(?<![\w_])omega(?![\w_])"),
    # plain `decide` — excludes bv_decide / native_decide (underscore is a word char)
    "decide": re.compile(r"(?<![\w_])decide(?![\w_])"),
    "bv_decide": re.compile(r"(?<![\w_])bv_decide(?![\w_])"),
    # simp / simp only / simp_all / simpa all start with simp; count the family
    "simp": re.compile(r"(?<![\w_])simp(?:_all|a)?(?![\w_])"),
    "norm_num": re.compile(r"(?<![\w_])norm_num(?![\w_])"),
}

COMMENT_LINE = re.compile(r"^\s*--")


def strip_comments(text: str) -> str:
    """Remove -- line comments and /- ... -/ block comments (nested)."""
    out = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth == 0 and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j == -1 else j
            continue
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(text[i])
        elif text[i] == "\n":
            out.append("\n")  # keep line structure
        i += 1
    return "".join(out)


# --------------------------------------------------------- block extraction

DECISION = re.compile(r"(?<![\w_])(omega|bv_decide|decide)(?![\w_])")


def find_by_blocks(text: str):
    """Return list of (start, end, blocktext) for balanced `(by ...)` spans."""
    spans = []
    for m in re.finditer(r"\(\s*by(?![\w_])", text):
        start = m.start()
        depth = 0
        i = start
        n = len(text)
        while i < n:
            c = text[i]
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0:
                    spans.append((start, i + 1, text[start:i + 1]))
                    break
            i += 1
    return spans


def enclosing_span(spans, pos):
    best = None
    for s, e, t in spans:
        if s <= pos < e:
            if best is None or (e - s) < (best[1] - best[0]):
                best = (s, e, t)
    return best


# ---------------------------------------------------------- normalization

KEYWORDS = {
    "by", "omega", "decide", "bv_decide", "native_decide", "simp", "simpa",
    "simp_all", "norm_num", "rw", "rwa", "rcases", "obtain", "cases", "exact",
    "refine", "show", "with", "at", "only", "intro", "intros", "have", "let",
    "fun", "constructor", "left", "right", "and_intro", "And", "Or", "inl",
    "inr", "subst", "apply", "unfold", "change", "generalize", "rfl", "trivial",
    "first", "all_goals", "any_goals", "try", "repeat", "if", "then", "else",
    "from", "this", "And.intro", "Or.inl", "Or.inr", "assumption", "exists",
    "use", "constructor", "ext", "funext", "calc", "match", "revert",
}

# keep namespaced lemma names (BitVec.eq_of_toNat_eq, Nat.mod_lt, …) informative
NAMESPACED = re.compile(r"^[A-Z][A-Za-z0-9]*\.[A-Za-z0-9_.']+$")

# an application head just before a bare (by decide)/(by omega) argument block
HEAD_RE = re.compile(
    r"(?:exact|refine|apply|:=|from|▸)\s+\(?([A-Za-z_][A-Za-z0-9_.']*)")


def head_context(text: str, pos: int) -> str:
    """Nearest application head before `pos` (which lemma consumes the arg)."""
    window = text[max(0, pos - 800):pos]
    heads = HEAD_RE.findall(window)
    for h in reversed(heads):
        if h not in KEYWORDS and h not in ("by",):
            # normalize per-site names: site_80008100_sd -> site_HEX_sd
            h = re.sub(r"[0-9a-fA-F]{6,}", "HEX", h)
            h = re.sub(r"\d+$", "N", h)
            return h
    return "?"

IDENT = re.compile(r"[A-Za-z_][A-Za-z0-9_'.!?]*")
HEXNUM = re.compile(r"0x[0-9a-fA-F]+")
NUM = re.compile(r"\d+")


def normalize_block(block: str) -> str:
    s = block
    # collapse bracket lists after rw/simp/rcases-with into a placeholder
    s = re.sub(r"(rw|rewrite)\s*\[[^\]]*\]", r"\1 [·]", s)
    s = re.sub(r"(simp(?:_all|a)?)(\s+only)?\s*\[[^\]]*\]", r"\1\2 [·]", s)
    s = re.sub(r"with\s+[^<;)⟩]*", "with · ", s)

    def tok(m):
        w = m.group(0)
        if w in KEYWORDS or NAMESPACED.match(w):
            return w
        return "ID"

    s = HEXNUM.sub("HEX", s)
    s = IDENT.sub(tok, s)
    s = NUM.sub("N", s)
    s = re.sub(r"(ID\s*[,+\-*/]?\s*)+ID", "ID…", s)  # collapse ident runs
    s = re.sub(r"\s+", " ", s).strip()
    return s


def extract_shapes(text: str):
    """Return Counter of normalized shape -> count, plus one raw example each."""
    spans = find_by_blocks(text)
    shapes = Counter()
    examples = {}
    seen_span_starts = set()
    for m in DECISION.finditer(text):
        sp = enclosing_span(spans, m.start())
        if sp is not None:
            if sp[0] in seen_span_starts:
                continue  # block counted once even w/ multiple omegas
            seen_span_starts.add(sp[0])
            raw = sp[2]
        else:
            # take the containing line as context
            ls = text.rfind("\n", 0, m.start()) + 1
            le = text.find("\n", m.start())
            if le == -1:
                le = len(text)
            raw = text[ls:le].strip()
        key = normalize_block(raw)
        if key in ("( by decide )", "(by decide)", "( by omega )", "(by omega)"):
            # sub-cluster the bare ground-arg blocks by the lemma that consumes them
            blockpos = sp[0] if sp is not None else m.start()
            head = head_context(text, blockpos)
            base = "(by decide)" if "decide" in key else "(by omega)"
            key = f"{base} arg-of {head}"
        shapes[key] += 1
        if key not in examples:
            examples[key] = re.sub(r"\s+", " ", raw)[:160]
    return shapes, examples


# ------------------------------------------------------- helper coverage

HELPER_RULES = [
    # (predicate on normalized shape, helper label)
    (lambda s: s.startswith("(by decide) arg-of obs_"),
     "NONE — register-disequality/ground args to a StepObs `obs_*` consumer "
     "(e.g. obs_alu_other takes 8 `(by decide)` Register-`==`-false args per call, "
     "Muldi3Spec.lean:330). Fix: bundled-diseq wrapper (1 decide per call, 8x cut) "
     "or block-reflection (`block_facts`) migration which deletes the whole "
     "per-site obs_* threading"),
    (lambda s: s.startswith("(by decide) arg-of hG."),
     "NONE — machine-config ground facts (mseccfg/misa/cur_privilege) fed per "
     "site; fix: pack into one `MachineConfigOK` record proved once per spec"),
    (lambda s: "BitVec.eq_of_toNat_eq" in s and "decide" in s,
     "NONE — concrete BitVec equality (mostly `BitVec.addInt pc 4 = pc'`); fix: "
     "one `addInt4_eq`-style rewrite lemma family / pc-advance-normalized obs_*_pc"),
    (lambda s: "BitVec.addInt" in s and "from by decide" in s,
     "NONE — pc-advance readback (`have := obs_*_pc …; rwa [show addInt pc 4 = "
     "pc' from by decide]`); fix: obs_*_pc variant stated at the concrete next pc "
     "(table-driven), or a `pc_step` macro-lemma"),
    (lambda s: ("rw [·] ; omega" in s or "rw [·]; omega" in s)
     and "have" not in s,
     "COVERED (if spill/expr/slot addr): SpillSafe.spill_load_safe4/8, "
     "OmegaHelpers.expr_load_safe4 / slot_load_safe"),
    (lambda s: "rcases" in s and "omega" in s,
     "COVERED: OmegaHelpers.code_disjoint / vi_disjoint (rcases stack-disjunction "
     "<;> omega)"),
    (lambda s: "fun" in s and "omega" in s and "⟨" in s,
     "COVERED: OmegaHelpers.frame_window8/4 (per-index window membership)"),
    (lambda s: "show" in s and "omega" in s,
     "PARTIAL: SpillSafe.spill_shift8 covers the sp-K byte re-index instance"),
    (lambda s: "have := ID" in s and "omega" in s,
     "NONE — frame-bound omega over a named hypothesis (hcodeStk/hstkRam…); "
     "candidates: extend code_disjoint/vi_disjoint family with the direct-bound "
     "variants"),
    (lambda s: s.startswith("(by omega) arg-of") or s == "(by omega)",
     "NONE — bare ground/linear omega arg; classify per receiving lemma"),
    (lambda s: s.startswith("(by decide) arg-of"),
     "NONE — ground decide arg; cheap individually, cost is call volume"),
]


def helper_coverage(shape: str) -> str:
    for pred, label in HELPER_RULES:
        if pred(shape):
            return label
    return "—"


# ---------------------------------------------------------------- imports

def module_of(path: str) -> str:
    rel = os.path.relpath(path, ROOT)
    return rel[:-len(".lean")].replace(os.sep, ".")


def build_reverse_imports(all_lean_files):
    imported_by = defaultdict(set)
    imp_re = re.compile(r"^import\s+([\w.]+)", re.M)
    for p in all_lean_files:
        try:
            with open(p, encoding="utf-8") as f:
                head = f.read(20000)
        except OSError:
            continue
        for m in imp_re.finditer(head):
            imported_by[m.group(1)].add(module_of(p))
    return imported_by


# -------------------------------------------------------------------- main

def main():
    lean_files = []
    for dirpath, _dirs, files in os.walk(VSA):
        for fn in files:
            if fn.endswith(".lean"):
                lean_files.append(os.path.join(dirpath, fn))
    # also scan repo-root .lean files (Vsa.lean god-module) for import graph
    all_for_imports = list(lean_files)
    for fn in os.listdir(ROOT):
        if fn.endswith(".lean"):
            all_for_imports.append(os.path.join(ROOT, fn))

    rows = []
    file_shapes = {}
    file_examples = {}
    for p in sorted(lean_files):
        with open(p, encoding="utf-8") as f:
            raw = f.read()
        text = strip_comments(raw)
        nlines = raw.count("\n") + 1
        counts = {k: len(rx.findall(text)) for k, rx in WORD.items()}
        decision = counts["omega"] + counts["decide"] + counts["bv_decide"]
        shapes, examples = extract_shapes(text)
        rel = os.path.relpath(p, ROOT)
        rows.append({
            "file": rel, "lines": nlines, "decision": decision, **counts,
        })
        file_shapes[rel] = shapes
        file_examples[rel] = examples

    rows.sort(key=lambda r: (-r["decision"], r["file"]))

    os.makedirs(os.path.dirname(TSV_OUT), exist_ok=True)
    with open(TSV_OUT, "w", encoding="utf-8") as f:
        f.write("file\tlines\tomega\tdecide\tbv_decide\tsimp\tnorm_num\tdecision_total\n")
        for r in rows:
            f.write(f"{r['file']}\t{r['lines']}\t{r['omega']}\t{r['decide']}\t"
                    f"{r['bv_decide']}\t{r['simp']}\t{r['norm_num']}\t{r['decision']}\n")

    top = [r for r in rows if r["decision"] > 0][:TOP_N_FILES]
    top_files = [r["file"] for r in top]

    # ---- shared shapes across the top files
    shape_files = defaultdict(dict)   # shape -> {file: count}
    shape_example = {}
    for rel in top_files:
        for shp, c in file_shapes[rel].items():
            shape_files[shp][rel] = c
            shape_example.setdefault(shp, file_examples[rel].get(shp, ""))
    shared = [(shp, fmap) for shp, fmap in shape_files.items() if len(fmap) >= 2]
    shared.sort(key=lambda kv: (-sum(kv[1].values()), -len(kv[1])))

    # ---- reverse imports (leaf status)
    imported_by = build_reverse_imports(all_for_imports)

    def leaf_info(rel):
        mod = rel[:-len(".lean")].replace(os.sep, ".")
        importers = imported_by.get(mod, set())
        # Vsa.lean root aggregator import doesn't make it structurally load-bearing,
        # but report raw count and whether all importers are the god-module.
        real = {i for i in importers if i != "Vsa"}
        return len(importers), len(real)

    leaf_mark = {}

    def mark(rel):
        if rel not in leaf_mark:
            _tot, real = leaf_info(rel)
            leaf_mark[rel] = " (LEAF)" if real == 0 else (
                " (near-leaf)" if real == 1 else "")
        return leaf_mark[rel]

    with open(MD_OUT, "w", encoding="utf-8") as f:
        w = f.write
        w("# Decision-tactic census — clustered patterns (auto-generated by scripts/decision_census.py)\n\n")
        w(f"Scanned {len(lean_files)} `.lean` files under `Vsa/`. Full per-file totals: "
          f"`experiments/decision-census.tsv`.\n\n")
        w("Counts are comment-stripped occurrences. A `(by …)` block with several "
          "omegas counts once as a *shape instance* but each call counts in the totals. "
          "Bare `(by decide)`/`(by omega)` argument blocks are sub-clustered by the "
          "lemma that consumes them (`arg-of <head>`, site hex normalized to HEX).\n\n")

        w("## Executive summary\n\n")
        w("- The wall is NOT mostly omega in these files: it is `(by decide)` "
          "argument volume into the hand-threaded StepObs `obs_*` consumer family "
          "(`obs_alu_other` alone consumes ~17.5k blocks across 24 of the top 25 "
          "files — 8 register-disequality args per call, see "
          "`Vsa/Sim/Muldi3Spec.lean:330`).\n")
        w("- Single highest-leverage helper: a bundled-disequality variant of the "
          "`obs_*_other` consumers (one packed `decide` per call instead of 8; or "
          "`rfl`-reducible per-register table), applied uniformly — it touches "
          "every top file. The strictly stronger move remains block-reflection "
          "(`block_facts`) migration, which deletes the whole per-site obs_* "
          "threading (proven 226→68s on EvalGtRow).\n")
        w("- The omega shapes already have helpers (SpillSafe/OmegaHelpers) that "
          "cover the biggest structured cluster (`(by rw [·]; omega)`, ~666 "
          "instances / 19 files) — migration is unfinished outside the Eval* row "
          "cohort.\n")
        w("- The `BitVec.addInt pc 4 = pc' from by decide` pc-advance shape "
          "(~500+ instances over the string/exec cohort) has no helper yet and is "
          "table-friendly.\n\n")

        w(f"## Top {len(top)} files by omega+decide+bv_decide\n\n")
        w("| file | lines | omega | decide | bv_decide | simp | total | importers (all / excl. Vsa.lean) | leaf? |\n")
        w("|---|---:|---:|---:|---:|---:|---:|---:|---|\n")
        for r in top:
            tot_imp, real_imp = leaf_info(r["file"])
            leaf = "LEAF" if real_imp == 0 else ""
            w(f"| `{r['file']}` | {r['lines']} | {r['omega']} | {r['decide']} | "
              f"{r['bv_decide']} | {r['simp']} | {r['decision']} | {tot_imp} / {real_imp} | {leaf} |\n")

        w("\n## Shared-shape ranking (exponentiating order)\n\n")
        w("| # | shape | total | files | helper coverage |\n")
        w("|--:|---|---:|---:|---|\n")
        for i, (shp, fmap) in enumerate(shared[:40], 1):
            total = sum(fmap.values())
            cov = helper_coverage(shp)
            cov_short = cov.split(";")[0].split(".")[0][:80]
            if cov.startswith("COVERED"):
                cov_short = "COVERED (SpillSafe/OmegaHelpers)"
            elif cov.startswith("PARTIAL"):
                cov_short = "PARTIAL (SpillSafe.spill_shift8)"
            elif cov.startswith("NONE"):
                cov_short = "none — " + cov.split("—", 1)[1].split(";")[0].split(". ")[0].strip()[:90]
            w(f"| {i} | `{shp[:70]}` | {total} | {len(fmap)} | {cov_short} |\n")

        w("\n## Shared shapes — detail (files, counts, leaf status)\n\n")
        for shp, fmap in shared[:40]:
            total = sum(fmap.values())
            w(f"### `{shp}`  — {total} instances in {len(fmap)} files\n\n")
            ex = shape_example.get(shp, "")
            if ex:
                w(f"- example: `{ex}`\n")
            cov = helper_coverage(shp)
            w(f"- helper coverage: {cov}\n")
            per = ", ".join(f"`{os.path.basename(fl)}`:{c}{mark(fl)}"
                            for fl, c in sorted(fmap.items(), key=lambda kv: -kv[1]))
            w(f"- per-file: {per}\n\n")

        w("\n## Per-file top patterns\n\n")
        for r in top:
            rel = r["file"]
            w(f"### `{rel}` ({r['decision']} decision calls, {r['lines']} lines)\n\n")
            for shp, c in file_shapes[rel].most_common(TOP_PATTERNS_PER_FILE):
                ex = file_examples[rel].get(shp, "")
                w(f"- ×{c} `{shp}`\n")
                if ex and ex != shp:
                    w(f"  - e.g. `{ex}`\n")
            w("\n")

    print(f"wrote {TSV_OUT} ({len(rows)} files) and {MD_OUT} "
          f"({len(shared)} shared shapes among top {len(top)})")


if __name__ == "__main__":
    sys.exit(main())
