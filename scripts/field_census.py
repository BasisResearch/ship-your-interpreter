#!/usr/bin/env python3
"""field_census.py — mechanically ask, for every `TermResidualsCore` field,
"does any landed theorem discharge this field's statement outright?"

For each field it emits a probe `example (L : Layout) : <type> := by exact?`
(mirroring TermAssembly.lean's opens) and runs `lake env lean` on it.
Outcomes: FOUND (exact? prints `Try this` — a one-term discharge EXISTS),
NOT_FOUND, TYPE_ERROR (extraction/context bug — fix here), TIMEOUT.

Writes experiments/field-census.tsv. Baseline 2026-09-01: 63/63 NOT_FOUND —
zero one-term discharges; every field needs marshalling (the t6 skeleton's
holes). RE-RUN after each RUN-1 lane merge: fields flipping to FOUND is the
trustworthy assembly burn-down metric (doc-comment status markers are not).

Usage: python3 scripts/field_census.py [-jN] (default -j4; be polite to
concurrently running agent lanes).
"""
import re, os, sys, subprocess, concurrent.futures
from collections import Counter

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROBEDIR = '/tmp/field_probes'
HEADER = '''import Vsa
open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows
open Vsa.Sim.ScaffoldRows
open Vsa.Sim.TermSimAssembly
open Vsa.Sim.InterpSimBundle (DivFamily ErrFamily)
open Vsa.Sim
local notation "SpecSt" => Vsa.While.St

'''

def extract_fields():
    s = open(os.path.join(ROOT, 'Vsa/Sim/TermAssembly.lean')).read()
    i = s.index('structure TermResidualsCore')
    # structure body ends at the next column-0 construct
    j = re.search(r'\n(?:/--|/-!|structure |theorem |def |abbrev |end )', s[i+10:])
    body = s[i:i+10+j.start()] if j else s[i:]
    pat = re.compile(r'^  (h\w+) :(.*?)(?=^  /--|^  h\w+ :|\Z)', re.S | re.M)
    out = []
    for m in pat.finditer(body):
        ty = re.sub(r'--[^\n]*', '', m.group(2)).strip()
        out.append((m.group(1), ty))
    return out

def run_probe(name):
    try:
        r = subprocess.run(['lake', 'env', 'lean', f'{PROBEDIR}/{name}.lean'],
                           capture_output=True, text=True, timeout=240, cwd=ROOT)
        out = r.stdout + r.stderr
        if 'Try this' in out:
            t = re.search(r'Try this:.*?exact ([^\n]*)', out)
            return (name, 'FOUND', t.group(1)[:100] if t else '')
        if 'could not close the goal' in out:
            return (name, 'NOT_FOUND', '')
        if 'error' in out:
            return (name, 'TYPE_ERROR', out.split('error', 1)[1][:100].replace('\n', ' '))
        return (name, 'UNKNOWN', out[:80])
    except subprocess.TimeoutExpired:
        return (name, 'TIMEOUT', '')

def main():
    jobs = 4
    for a in sys.argv[1:]:
        if a.startswith('-j'):
            jobs = int(a[2:])
    fields = extract_fields()
    os.makedirs(PROBEDIR, exist_ok=True)
    for name, ty in fields:
        with open(f'{PROBEDIR}/{name}.lean', 'w') as f:
            f.write(HEADER)
            f.write(f'-- field probe: TermResidualsCore.{name}\n')
            f.write(f'example (L : Layout) : {ty} := by exact?\n')
    with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
        results = sorted(ex.map(run_probe, [n for n, _ in fields]))
    tsv = os.path.join(ROOT, 'experiments/field-census.tsv')
    with open(tsv, 'w') as f:
        f.write('field\texact_probe\tdetail\n')
        for n, st, d in results:
            f.write(f'{n}\t{st}\t{d}\n')
    c = Counter(st for _, st, _ in results)
    print(dict(c))
    if c.get('TYPE_ERROR', 0):
        print('TYPE_ERROR rows are extraction bugs in THIS script — fix extract_fields().')
        sys.exit(1)

if __name__ == '__main__':
    main()
