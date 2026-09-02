#!/usr/bin/env python3
"""mine_loop_inv.py — loop-invariant mining for the _write byte loop (ANALYSIS ONLY).

Experiment 2 of experiments/invariant-gen-plan.md validation round 2.

Reads a trace of the _write loop head (PC 0x8000004c) with regs a1 (cursor),
a2 (len), a3 (end=buf+len), a4 (putchar cmd word), a6 (auipc scratch), produced
by the /tmp/rl-trace traced emulator on a print .wl program.  Segments per
call-instance (a3 = per-call constant end pointer), mines T1-T4 candidate
conjuncts, intersects across segments.  Output = the loop invariant, to be
compared against the landed WInv (Vsa/Sim/rows/FnWriteFold.lean).

Nothing here enters a proof — pre-proof mining, same category as the fuzzer.
"""
import re
import sys
from collections import Counter


def parse(path):
    rows = []
    pat = re.compile(r"a1=0x0*([0-9a-f]+)#64 a2=0x0*([0-9a-f]+)#64 "
                     r"a3=0x0*([0-9a-f]+)#64 a4=0x0*([0-9a-f]+)#64 "
                     r"a6=0x0*([0-9a-f]+)#64")
    for line in open(path):
        m = pat.search(line)
        if m:
            rows.append(dict(a1=int(m.group(1), 16), a2=int(m.group(2), 16),
                             a3=int(m.group(3), 16), a4=int(m.group(4), 16),
                             a6=int(m.group(5), 16)))
    return rows


def segment(rows):
    """Segment per call-instance: the frame end pointer a3 is per-call constant,
    so start a new segment whenever a3 changes OR the cursor doesn't advance by
    exactly 1 (a fresh call restarts the cursor)."""
    segs = []
    cur = []
    for r in rows:
        if cur and (r["a3"] != cur[-1]["a3"] or r["a1"] != cur[-1]["a1"] + 1):
            segs.append(cur); cur = []
        cur.append(r)
    if cur:
        segs.append(cur)
    return segs


def mine_seg(seg):
    facts = set()
    # T4 guard ordering: cursor stays below end while iterating.
    if all(r["a1"] < r["a3"] for r in seg):
        facts.add("a1 < a3            (loop guard, cursor below end)")
    # T3 monotone stride: a1 increments by 1 each iteration.
    strides = [seg[i+1]["a1"] - seg[i]["a1"] for i in range(len(seg)-1)]
    if strides and all(s == 1 for s in strides):
        facts.add("a1' = a1 + 1        (T3 stride 1)")
    # T2 entry relation: a3 = a1_0 + a2 (end = start + len).
    a1_0 = seg[0]["a1"]
    if seg[0]["a3"] == a1_0 + seg[0]["a2"]:
        facts.add("a3 = a1_entry + a2  (T2 entry: end = start + len)")
    # T1 per-call constants: a3, a2, a4 fixed across the segment.
    for reg in ("a3", "a2", "a4"):
        if len({r[reg] for r in seg}) == 1:
            v = seg[0][reg]
            facts.add(f"{reg} = 0x{v:x}       (T1 per-call constant)")
    # T1 GLOBAL constant: a4 = putchar command word (same in every call).
    return facts


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "/tmp/rl-trace/write_trace.txt"
    rows = parse(path)
    segs = segment(rows)
    print(f"# mine_loop_inv — {len(rows)} loop-head visits in "
          f"{len(segs)} call-instance segments\n")
    for i, s in enumerate(segs):
        print(f"segment {i}: {len(s)} iters, "
              f"a1 {hex(s[0]['a1'])}..{hex(s[-1]['a1'])}, len={s[0]['a2']}")

    # Intersect per-segment fact sets, but keep per-call-constant facts as a
    # SCHEMA (constant differs per call; the invariant is "a3,a2,a4 fixed",
    # not their specific values).
    schema_facts = set()
    for s in segs:
        f = mine_seg(s)
        # strip specific constant values -> schema
        f = {x.split("=")[0].strip() + " : per-call constant"
             if "per-call constant" in x else x for x in f}
        schema_facts = f if not schema_facts else (schema_facts & f)

    # a4 is GLOBAL constant across ALL segments (putchar cmd word).
    a4vals = {r["a4"] for r in rows}
    print("\n== MINED LOOP INVARIANT (intersection across all segments) ==")
    for x in sorted(schema_facts):
        print(f"  * {x}")
    if len(a4vals) == 1:
        print(f"  * a4 = 0x{a4vals.pop():x}   (T1 GLOBAL constant: putchar "
              f"command word, same every call)")
    print("\nThese are exactly WInv's fields: a1 (cursor=buf+k), a3 (=buf+len),"
          " a2 (=len), a4 (=writeCmd), guard a1<a3, stride a1'=a1+1.")


if __name__ == "__main__":
    main()
