#!/usr/bin/env python3
"""fleet_briefs.py — generate per-batch worker briefs for the field-discharge
fleet (one sequential worker per batch, one COW clone, one lean process).

Reads experiments/fleet/batches.tsv + the field statements out of
Vsa/Sim/TermAssembly.lean; writes experiments/fleet/briefs/<batch>.md.

Re-run any time (idempotent). Briefs embed the exact field statements so a
worker never has to parse the record itself.
"""
import csv, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

def extract_fields():
    s = open(os.path.join(ROOT, 'Vsa/Sim/TermAssembly.lean')).read()
    i = s.index('structure TermResidualsCore')
    j = re.search(r'\n(?:/--|/-!|structure |theorem |def |abbrev |end )', s[i+10:])
    body = s[i:i+10+j.start()] if j else s[i:]
    pat = re.compile(r'^  (h\w+) :(.*?)(?=^  /--|^  h\w+ :|\Z)', re.S | re.M)
    d = {m.group(1): re.sub(r'--[^\n]*', '', m.group(2)).strip()
         for m in pat.finditer(body)}
    # hDivCorr is the last field; the regex can overrun — pin it explicitly.
    if 'hDivCorr' in d:
        d['hDivCorr'] = 'Vsa.Sim.DivFamily.DivCorrFamily L'
    return d

PROTOCOL = '''
## Laws (CLAUDE.md governs; these WILL bite you)
- NEVER raise maxHeartbeats/timeouts. No sorry/axiom/native_decide/bv_decide.
- Verify ONLY with `lake env lean <your file>`. NEVER `lake build`, never LSP,
  NEVER `scripts/check_all.sh` (coordinator-only; it would crush the machine).
- Axioms of every theorem must be exactly ⊆ {propext, Classical.choice,
  Quot.sound} — end each file with `#print axioms <thm>` and CHECK it.
- Run `scripts/abs_inventory.sh` FIRST; reuse abstractions by name. Named-field
  structures only; never anonymous ∃/∧ towers; never .2.2.2 chains.
- A missing general fact → append to experiments/observations.md (format at its
  top) THE MOMENT you notice, then continue with the next field.

## Worker contract
- You are in a THROWAWAY CLONE of the repo. Work here only.
- ONE NEW FILE PER FIELD: `Vsa/Sim/rows/Field_<name>.lean`. It imports
  `Vsa.Sim.rows.AssemblySkeleton` and proves EXACTLY the skeleton hole:
  `theorem field_<name> (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelH<Name> L := ...`
  (the hole abbrev unfolds to the statement quoted below; the coordinator
  plugs your theorem into `termResidualsCore_of_skeleton`). Copy the opens
  from `AssemblySkeleton.lean`'s header.
- NEVER edit shared files (Vsa.lean, check_all.sh, existing rows, the record).
  The coordinator does all wiring later, from your new files only.
- Work the fields IN ORDER. After EACH field goes green: append a landing entry
  to `experiments/logs/fleet-<batch>.md` (this survives your death; your final
  message does not).
- STUCK on a field (missing supplier, unprovable as stated)? Write the
  machine-checked obstruction or the missing-supplier NAME into the log +
  observations.md, SKIP IT, move to the next field. Never work around it,
  never assert it, never touch the statement.
- First field of the batch is the TEMPLATE: spend the care there; the rest of
  the batch should consume your own template.
- Do NOT rm the clone or anything in it when done. Final message: per-field
  status table (green/skipped+why), nothing else.
'''

def main():
    fields = extract_fields()
    briefs = os.path.join(ROOT, 'experiments/fleet/briefs')
    os.makedirs(briefs, exist_ok=True)
    with open(os.path.join(ROOT, 'experiments/fleet/batches.tsv')) as f:
        rows = list(csv.DictReader(f, delimiter='\t'))
    for r in rows:
        b = r['batch']
        names = r['fields'].split(',')
        missing = [n for n in names if n not in fields]
        if missing:
            print(f"WARN {b}: fields not found in record: {missing}", file=sys.stderr)
        with open(os.path.join(briefs, f'{b}.md'), 'w') as f:
            f.write(f"# Fleet batch {b} — discharge these TermResidualsCore fields\n\n")
            f.write(f"Gating status: {r['gating']}. If a field's suppliers are "
                    f"missing, log + skip per the contract — do not force it.\n\n")
            f.write(f"Template pointers (read these files FIRST): {r['template_pointers']}\n")
            f.write("Also read: Vsa/Sim/rows/AssemblySkeleton.lean (your targets: the "
                    "SkelH* hole abbrevs), experiments/assembly_skeleton.tsv "
                    "(the work-list; supplier notes per field), and "
                    "experiments/field-census.tsv (baseline: no one-term "
                    "discharges — you are writing the marshalling).\n")
            f.write(PROTOCOL)
            f.write(f"\n## The fields ({len(names)}), in order\n")
            for n in names:
                f.write(f"\n### {n}\n```lean\n{fields.get(n, 'MISSING FROM RECORD')}\n```\n")
        print(f"wrote briefs/{b}.md ({len(names)} fields)")

if __name__ == '__main__':
    main()
