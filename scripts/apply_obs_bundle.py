#!/usr/bin/env python3
"""apply_obs_bundle.py — mechanically rewrite `obs_*_other` register-frame ladder
callsites to their bundled `Vsa/Sim/ObsAvoid.lean` variants (`<base>'`), collapsing
the 7-8 per-site `(by decide)` disequality arguments into ONE `(by decide)`.

Each recognized callsite has the shape (all on a single logical line):

    <head> <A> <B> (by decide) (by decide) ... (by decide) <tail>

where, per base lemma:
  * 8-decide, `hobs R` order:  obs_alu_other / obs_jal_other
        obs_alu_other  <hobs> Register.<r> (by decide)x8 <hσ>
     -> obs_alu_other' <hobs> Register.<r> (by decide)   <hσ>
  * 7-decide, `hobs R` order:  obs_store_other / obs_store_other_val /
        obs_btaken_other / obs_bnottaken_other / obs_jr_other /
        obs_branch_taken_other / obs_branch_nottaken_other
        obs_store_other  <hobs> Register.<r> (by decide)x7 <hσ>
     -> obs_store_other' <hobs> Register.<r> (by decide)   <hσ>
  * 7-decide, `R hobs` order:  obs_store_other_sn4 / obs_store_other_sn3
        obs_store_other_sn4  Register.<r> <hobs> (by decide)x7 <hσ>
     -> obs_store_other_sn4' Register.<r> <hobs> (by decide)   <hσ>

CONSERVATIVE by construction:
  * Only the exact recognized head + arg-shape is rewritten. The two operand tokens
    (`<A> <B>`) must be simple identifiers / `Register.xNN` (no nested parens), and the
    tail hypothesis a single identifier token. Anything else is left untouched.
  * The `(by decide)` run must have EXACTLY the head's expected count (8 or 7). A site
    with a different count, or with any non-`(by decide)` arg mixed in, is skipped and
    reported (with --verbose) so nothing ambiguous is silently changed.
  * Lines already using a primed head (`obs_*_other'`) are ignored.
  * Comment lines (leading `--`) are ignored.

Usage:
    scripts/apply_obs_bundle.py [--dry-run] [--verbose] FILE.lean [FILE.lean ...]
    scripts/apply_obs_bundle.py --dry-run Vsa/Sim/SnprintfSpec17.lean

--dry-run  : report file:line + head counts, write nothing.
(default)  : rewrite in place, print a per-file + total summary.

Also ensures `import Vsa.Sim.ObsAvoid` is present when a file is modified (inserted
after the last existing `import` line); with --dry-run the import is only reported.
"""

import argparse
import re
import sys

# head -> (expected decide count, order) where order is 'hobs_R' or 'R_hobs'
HEADS = {
    "obs_alu_other":               (8, "hobs_R"),
    "obs_jal_other":               (8, "hobs_R"),
    "obs_store_other":             (7, "hobs_R"),
    "obs_store_other_val":         (7, "hobs_R"),
    "obs_btaken_other":            (7, "hobs_R"),
    "obs_bnottaken_other":         (7, "hobs_R"),
    "obs_jr_other":                (7, "hobs_R"),
    "obs_branch_taken_other":      (7, "hobs_R"),
    "obs_branch_nottaken_other":   (7, "hobs_R"),
    "obs_store_other_sn4":         (7, "R_hobs"),
    "obs_store_other_sn3":         (7, "R_hobs"),
}

# Longest head first so e.g. `obs_store_other_val` is tried before `obs_store_other`.
HEADS_BY_LEN = sorted(HEADS, key=len, reverse=True)

# A single simple argument token: identifier (with dots, e.g. Register.x10) — NO parens.
TOK = r"[A-Za-z_][A-Za-z0-9_.']*"
DECIDE = r"\(by decide\)"


def build_pattern(head, count):
    # `head` then two simple operand tokens, then exactly `count` (by decide), then a
    # single trailing token, then a boundary (end-of-line / `,` / `)` / whitespace-run).
    decides = r"\(by decide\)(?:\s+\(by decide\)){%d}" % (count - 1)
    return re.compile(
        r"(?P<indent>)"                      # placeholder (kept for symmetry)
        + r"\b" + re.escape(head) + r"\b"
        + r"(?P<sp1>\s+)(?P<a>" + TOK + r")"
        + r"(?P<sp2>\s+)(?P<b>" + TOK + r")"
        + r"(?P<sp3>\s+)(?P<decides>" + decides + r")"
        + r"(?P<sp4>\s+)(?P<tail>" + TOK + r")"
    )


PATTERNS = [(h, HEADS[h][0], HEADS[h][1], build_pattern(h, HEADS[h][0])) for h in HEADS_BY_LEN]


def rewrite_line(line):
    """Return (new_line, [head,...] rewritten on this line). One line may hold several
    callsites (Snprintf files pack them one per physical line, but be safe)."""
    if line.lstrip().startswith("--"):
        return line, []
    hits = []
    # Try each head; a primed head can never match (the regex requires the exact base
    # word boundary, and `obs_alu_other'` has a trailing `'` which `\b...\b` on the base
    # would still match up to the `'` — guard explicitly below).
    for head, count, order, pat in PATTERNS:
        def repl(m):
            # Guard: the char immediately after the head must not be `'` (already primed)
            # — enforced by requiring `\s` right after head via sp1, so `'` cannot follow.
            hits.append(head)
            return (head + "'" + m.group("sp1") + m.group("a")
                    + m.group("sp2") + m.group("b")
                    + m.group("sp3") + "(by decide)"
                    + m.group("sp4") + m.group("tail"))
        line = pat.sub(repl, line)
    return line, hits


def ensure_import(lines):
    """Insert `import Vsa.Sim.ObsAvoid` after the last import line if absent."""
    target = "import Vsa.Sim.ObsAvoid"
    if any(l.strip() == target for l in lines):
        return lines, False
    last_import = -1
    for i, l in enumerate(lines):
        if re.match(r"\s*import\s+\S", l):
            last_import = i
    if last_import < 0:
        return lines, False  # no import block; leave untouched (report)
    new = lines[:last_import + 1] + [target + "\n"] + lines[last_import + 1:]
    return new, True


def process(path, dry_run, verbose):
    with open(path) as f:
        lines = f.readlines()
    counts = {}
    total = 0
    out = []
    for lineno, line in enumerate(lines, 1):
        new_line, hits = rewrite_line(line)
        if hits:
            for h in hits:
                counts[h] = counts.get(h, 0) + 1
            total += len(hits)
            if verbose or dry_run:
                print(f"  {path}:{lineno}  " + ", ".join(hits))
        out.append(new_line)
    imported = any(l.strip() == "import Vsa.Sim.ObsAvoid" for l in lines)
    if total and not dry_run:
        out, added = ensure_import(out)
        with open(path, "w") as f:
            f.writelines(out)
        if added:
            print(f"  {path}: inserted `import Vsa.Sim.ObsAvoid`")
    elif total and dry_run and not imported:
        print(f"  {path}: (would insert `import Vsa.Sim.ObsAvoid`)")
    return counts, total


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--dry-run", action="store_true", help="report only, write nothing")
    ap.add_argument("--verbose", action="store_true", help="print every rewritten site")
    ap.add_argument("files", nargs="+")
    args = ap.parse_args()

    grand = {}
    grand_total = 0
    for path in args.files:
        print(f"== {path} ==")
        counts, total = process(path, args.dry_run, args.verbose)
        for h, c in sorted(counts.items(), key=lambda kv: -kv[1]):
            print(f"    {h:28} {c}")
        print(f"    {'TOTAL sites':28} {total}   (decides saved ≈ "
              + str(sum(c * (HEADS[h][0] - 1) for h, c in counts.items())) + ")")
        for h, c in counts.items():
            grand[h] = grand.get(h, 0) + c
        grand_total += total

    print("\n== GRAND TOTAL ==")
    for h, c in sorted(grand.items(), key=lambda kv: -kv[1]):
        print(f"    {h:28} {c}")
    saved = sum(c * (HEADS[h][0] - 1) for h, c in grand.items())
    print(f"    {'sites':28} {grand_total}")
    print(f"    {'(by decide) blocks removed':28} {saved}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
