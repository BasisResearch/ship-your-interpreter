#!/usr/bin/env python3
"""Fail if IrisHoles fields and VsaIris/HOLES.md rows disagree, or if any VsaIris
file outside the design skeleton contains sorry/admit/axiom.

`structure IrisHoles` may live in the skeleton (`Interp/Specs.lean`). A field
`f : T` contributes `f.g` for each field `g` of `structure T`, following
`def T … : Prop := ∃ …, U …` to `structure U`; a field of type `True` is a
placeholder whose `f.*` rows are reported but not checked."""
import re, sys, pathlib
root = pathlib.Path(__file__).resolve().parent.parent
rows = set(re.findall(r'^\| `([\w.]+)` \|', (root/'VsaIris/HOLES.md').read_text(), re.M))
files = sorted((root/'VsaIris').rglob('*.lean'))
src = "\n".join(p.read_text() for p in files)
BODY = r'[^\n]*\n((?:  .*\n|\n)*)'

def fields_of(ty, depth=0):
    """Field names of structure `ty`, following `def ty … := ∃ …, U …`."""
    sub = re.search(rf'structure {re.escape(ty)}\b' + BODY, src)
    if sub:
        return re.findall(r'^  (\w+)\s*:', sub.group(1), re.M)
    d = re.search(rf'def {re.escape(ty)}\b[^\n]*:=\s*∃[^,]*,\s*([\w.]+)', src)
    if d and depth < 4:
        return fields_of(d.group(1).split('.')[-1], depth + 1)
    return []

m = re.search(r'structure IrisHoles' + BODY, src)
fields, placeholders = set(), set()
if m:
    for f, ty in re.findall(r'^  (\w+)\s*:\s*([\w.]+)', m.group(1), re.M):
        ty = ty.split('.')[-1]
        if ty == 'True':
            placeholders.add(f)
            continue
        fields |= {f"{f}.{s}" for s in fields_of(ty)} or {f}
checked = {r for r in rows if r.split('.')[0] not in placeholders}
bad = []
if m and fields != checked:
    bad.append(f"IrisHoles fields {sorted(fields - checked)} lack HOLES.md rows; "
               f"rows {sorted(checked - fields)} lack fields")
for p in files:
    if 'Interp/Specs.lean' in str(p): continue
    t = re.sub(r'/-.*?-/|--[^\n]*', '', p.read_text(), flags=re.S)
    if re.search(r'\b(sorry|admit)\b|^\s*axiom\s', t, re.M): bad.append(f"hole tactic/axiom in {p.relative_to(root)}")
note = "".join(f"; placeholder `{f} : True` ({len([r for r in rows if r.startswith(f + '.')])} rows unchecked)"
               for f in sorted(placeholders))
print("\n".join(bad) or f"ok: {len(rows)} ledgered holes" + ("" if m else " (IrisHoles not defined yet)") + note)
sys.exit(1 if bad else 0)
