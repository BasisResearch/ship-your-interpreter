#!/usr/bin/env python3
"""Fail if IrisHoles fields and VsaIris/HOLES.md rows disagree, or if any VsaIris
file outside the design skeleton contains sorry/admit/axiom."""
import re, sys, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
rows = set(re.findall(r'^\| `([\w.]+)` \|', (root/'VsaIris/HOLES.md').read_text(), re.M))
src = "\n".join(p.read_text() for p in (root/'VsaIris').rglob('*.lean') if 'Interp/Specs.lean' not in str(p))
m = re.search(r'structure IrisHoles[^\n]*\n((?:  .*\n|\n)*)', src)
fields = set()
if m:
    # fields may be nested structures: record `name` and `name.sub` from `name : Sub` + Sub's fields
    for f, ty in re.findall(r'^  (\w+)\s*:\s*(\w+)', m.group(1), re.M):
        sub = re.search(rf'structure {ty}[^\n]*\n((?:  .*\n|\n)*)', src)
        subs = re.findall(r'^  (\w+)\s*:', sub.group(1), re.M) if sub else []
        fields |= {f"{f}.{s}" for s in subs} or {f}
bad = []
if m and fields != rows:
    bad.append(f"IrisHoles fields {sorted(fields - rows)} lack HOLES.md rows; rows {sorted(rows - fields)} lack fields")
for p in (root/'VsaIris').rglob('*.lean'):
    if 'Interp/Specs.lean' in str(p): continue
    t = re.sub(r'/-.*?-/|--[^\n]*', '', p.read_text(), flags=re.S)
    if re.search(r'\b(sorry|admit)\b|^\s*axiom\s', t, re.M): bad.append(f"hole tactic/axiom in {p.relative_to(root)}")
print("\n".join(bad) or f"ok: {len(rows)} ledgered holes" + ("" if m else " (IrisHoles not defined yet)"))
sys.exit(1 if bad else 0)
