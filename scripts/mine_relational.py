#!/usr/bin/env python3
"""mine_relational.py — stage-4 relational (machine×spec) mining (ANALYSIS ONLY).

The core deliverable of experiments/invariant-gen-plan.md.  Pairs the machine
dispatch trace (gen_trace.py @ the exec_stmt dispatch PC, dumping s0=aStmt and
the 4-byte kind word at [s0]) with the spec exec trace
(experiments/spec_trace_brkcont.lean, dumping `kindOfStmt s` per exec-step), and
mines cross-side conjuncts:

    machine read32[aStmt] low byte  ==  spec kindOfStmt s        (the StmtRepr bridge)
    dispatch tag k                  ->  arm PC (7->brk, 8->cont)  (the StmtSlotPinned bridge)

Alignment is by the discriminating tag: for the relational-lite exec arms the
seam is a single dispatch point, so we align by KIND VALUE + COUNT (the spec
subset models one loop; the discriminating brk/cont tags are unambiguous).

Nothing here enters a proof.
"""
import json
import re
import subprocess
import sys
from collections import Counter

MACHINE = "/tmp/rl-trace/brkcont_trace.jsonl"
DISPATCH_PC = 0x80004014
ARM_PC = {0x80004098: 7, 0x800040b8: 8}   # brk arm, cont arm -> expected kind

# kindOfStmt tags (from Vsa/Sim/ExecDispatch.lean) — the spec ground truth.
KIND_NAME = {0: "expr", 1: "varDecl", 2: "block", 3: "ifStmt", 4: "whileStmt",
             5: "forStmt", 6: "ret", 7: "brk", 8: "cont"}


def machine_dispatch(path):
    rows = [json.loads(l) for l in open(path)]
    disp = [r for r in rows if r["pc"] == DISPATCH_PC]
    # machine kind = little-endian word of the 4 kind bytes; low byte = tag
    kinds = []
    for r in disp:
        w = (r.get("m0b0", 0) | (r.get("m0b1", 0) << 8)
             | (r.get("m0b2", 0) << 16) | (r.get("m0b3", 0) << 24))
        kinds.append(w & 0xff)
    # arm-entry confirmation
    arm_hits = {}
    for r in rows:
        if r["pc"] in ARM_PC:
            arm_hits[ARM_PC[r["pc"]]] = arm_hits.get(ARM_PC[r["pc"]], 0) + 1
    return kinds, arm_hits


def spec_kinds():
    r = subprocess.run(
        ["lake", "env", "lean", "experiments/spec_trace_brkcont.lean"],
        capture_output=True, text=True, timeout=400)
    ks = []
    for line in r.stdout.splitlines():
        m = re.match(r"SPEC kind=(\d+)", line)
        if m:
            ks.append(int(m.group(1)))
    return ks


def main():
    mkinds, arm_hits = machine_dispatch(MACHINE)
    skinds = spec_kinds()
    mc, sc = Counter(mkinds), Counter(skinds)

    print("# mine_relational — machine×spec exec-arm dispatch pilot\n")
    print(f"machine dispatch events: {len(mkinds)}   spec exec-steps: {len(skinds)}\n")
    print("kind | name     | machine cnt | spec cnt | arm-entry cnt")
    print("-----+----------+-------------+----------+--------------")
    for k in sorted(set(mc) | set(sc)):
        arm = arm_hits.get(k, "")
        print(f"  {k}  | {KIND_NAME.get(k,'?'):8} |    {mc.get(k,0):7}  |  {sc.get(k,0):6}  | {arm}")

    print("\n== MINED RELATIONAL CONJUNCTS ==")
    # The discriminating relation: for the single-seam brk/cont arms, machine
    # dispatch tag == spec kindOfStmt, and each routes to its arm PC.
    verdicts = []
    for pc, k in ARM_PC.items():
        mach = mc.get(k, 0)          # machine dispatch tags of this kind
        spec = sc.get(k, 0)          # spec kindOfStmt of this kind
        arm = arm_hits.get(k, 0)     # arm-entry hits
        agree = (mach == spec == arm) and mach > 0
        verdicts.append(agree)
        print(f"  * read32[aStmt] & 0xff = {k} = kindOfStmt (.{KIND_NAME[k]})"
              f"   [machine {mach} = spec {spec} = arm-entry {arm}]"
              f"   {'MATCH' if agree else 'MISMATCH'}")
        print(f"  * dispatch tag {k}  ->  armPC 0x{pc:x}"
              f"   (StmtSlotPinned {k} 0x{pc:x})")

    # cross-side kind agreement on ALL shared discriminating tags (brk/cont/if)
    disc = [7, 8, 3]
    ok = all(mc.get(k, 0) == sc.get(k, 0) for k in disc)
    print(f"\ncross-side discriminating-tag agreement (brk/cont/if): "
          f"{'PASS' if ok else 'PARTIAL'} "
          f"(machine {[mc.get(k,0) for k in disc]} vs spec {[sc.get(k,0) for k in disc]})")
    print(f"\nVERDICT: mined bridge for brk+cont arms "
          f"{'MATCHES landed StmtSlotPinned/kindOfStmt shape' if all(verdicts) else 'PARTIAL'}")


if __name__ == "__main__":
    main()
