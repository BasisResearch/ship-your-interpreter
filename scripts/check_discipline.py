#!/usr/bin/env python3
"""Proof-discipline gate: enforce the exponentiating layer programmatically.

Scans Vsa/**/*.lean (tracked AND untracked) against scripts/discipline_rules.tsv.
Files listed in scripts/discipline_grandfather.txt are exempt (legacy, pre-layer);
NEW files are strict. A specific line can be exempted with:

    -- discipline: allow(<rule_id>) <justification>

on the same line or the line directly above. COUNT>N:<needle> patterns fire when
a file contains more than N occurrences of <needle> (whole-file rules).

Exit 1 on any violation. Extensible: add rules to the TSV, no code changes.
"""
import fnmatch
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RULES = ROOT / "scripts" / "discipline_rules.tsv"
GRANDFATHER = ROOT / "scripts" / "discipline_grandfather.txt"
ALLOW = re.compile(r"--\s*discipline:\s*allow\(([A-Za-z0-9_-]+)\)")


def load_rules():
    rules = []
    for line in RULES.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) < 4:
            continue
        rid, scope, pat, msg = parts[0], parts[1], parts[2], "\t".join(parts[3:])
        rules.append((rid, scope, pat, msg))
    return rules


def load_grandfather():
    if not GRANDFATHER.exists():
        return set()
    return {l.strip() for l in GRANDFATHER.read_text().splitlines()
            if l.strip() and not l.startswith("#")}


def allowed(rid, lines, idx):
    for j in (idx, idx - 1):
        if 0 <= j < len(lines):
            m = ALLOW.search(lines[j])
            if m and m.group(1) == rid:
                return True
    return False


def main():
    rules = load_rules()
    grandfather = load_grandfather()
    violations = []
    for f in sorted((ROOT / "Vsa").rglob("*.lean")):
        rel = str(f.relative_to(ROOT))
        if rel in grandfather:
            continue
        text = f.read_text()
        lines = text.splitlines()
        for rid, scope, pat, msg in rules:
            if not fnmatch.fnmatch(rel, scope):
                continue
            if pat.startswith("COUNT>"):
                m = re.match(r"COUNT>(\d+):(.*)", pat)
                n, needle = int(m.group(1)), m.group(2)
                count = text.count(needle)
                if count > n and f"discipline: allow({rid})" not in text:
                    violations.append(f"{rel}: [{rid}] {needle} x{count} — {msg}")
                continue
            rx = re.compile(pat)
            for i, line in enumerate(lines):
                if rx.search(line) and not allowed(rid, lines, i):
                    violations.append(f"{rel}:{i+1}: [{rid}] {msg}")
    if violations:
        print("discipline: FAIL — the exponentiating layer is mandatory for new files")
        for v in violations:
            print("  " + v)
        print("  (exempt a genuine exception with `-- discipline: allow(<rule>) <why>`;")
        print("   legacy files are listed in scripts/discipline_grandfather.txt)")
        return 1
    print(f"discipline: OK ({len(rules)} rules, {len(grandfather)} grandfathered files)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
