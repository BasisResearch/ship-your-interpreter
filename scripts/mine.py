#!/usr/bin/env python3
"""mine.py — tiered invariant-candidate mining (ANALYSIS ONLY, stage 3).

Generalizes the two validated miners (mine_loop_inv.py, mine_stack_ladder.py)
into one tool driven by the corpus vocabulary.  Reads a segmented JSONL
(segment.py output) and mines candidate conjuncts, intersecting within segments
then across segments.

Round-2 corrections folded in:
  (1) T3 stride HISTOGRAMMING — mine the per-step delta histogram, not the
      endpoint difference (the endpoint fit is polluted by interleaved frames).
      The dominant delta(s) are reported as the per-level/per-iter stride
      constants; least-squares over depths gives the ladder slope.
  (2) Case VOCABULARY from the corpus — which registers/windows a case touches
      is read from experiments/corpus/<case>.md ("regs written on slice"),
      so mining is scoped to the case's live regs instead of guessing.

Tiers:
  T1  constants / per-call constants (value fixed across a segment)
  T2  pairwise linear at entry (a = b + c, a - b = k)
  T3  monotone strides (histogrammed) + depth ladder (least-squares)
  T4  guard orderings (a < b holds every iteration)
  T5  mem-window facts (word at a probed slot = const / = f(regs))

Nothing here enters a proof — pre-proof mining, same category as the fuzzer.
"""
import argparse
import json
import os
import re
import sys
from collections import Counter
from itertools import combinations

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def load_segments(path):
    segs = {}
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        segs.setdefault(r.get("seg", 0), []).append(r)
    return [segs[k] for k in sorted(segs)]


def case_vocab(case):
    """Read the case's live registers from its corpus card ('regs written on
    slice').  Returns a set of abi register names, or None if not found."""
    card = os.path.join(ROOT, "experiments", "corpus", f"{case}.md")
    if not os.path.exists(card):
        return None
    for line in open(card):
        m = re.search(r"regs written on slice:\s*(.+)", line)
        if m:
            return {x.strip() for x in m.group(1).split(",")}
    return None


def reg_keys(seg):
    """Value keys present in the trace rows (exclude bookkeeping)."""
    skip = {"idx", "seg", "case"}
    return [k for k in seg[0] if k not in skip and isinstance(seg[0][k], int)]


def mine_seg(seg, vocab):
    facts = set()
    keys = reg_keys(seg)
    # scope to case vocabulary when available (mem windows m*_* always kept)
    if vocab:
        keys = [k for k in keys if k in vocab or k.startswith("m")
                or k in ("sp", "ra")]

    # T1 per-segment constants
    for k in keys:
        vals = {r[k] for r in seg if k in r}
        if len(vals) == 1:
            facts.add(f"T1 {k} = 0x{next(iter(vals)):x}   (per-segment constant)")

    # T4 guard orderings: a < b holds at every event
    for a, b in combinations(keys, 2):
        if all(a in r and b in r for r in seg):
            if all(r[a] < r[b] for r in seg) and any(r[a] != r[b] for r in seg):
                facts.add(f"T4 {a} < {b}   (guard ordering)")

    # T3 monotone strides (histogrammed per key)
    for k in keys:
        vs = [r[k] for r in seg if k in r]
        deltas = [vs[i + 1] - vs[i] for i in range(len(vs) - 1)]
        if deltas:
            hist = Counter(deltas)
            dom, cnt = hist.most_common(1)[0]
            if dom != 0 and cnt == len(deltas):
                facts.add(f"T3 {k}' = {k} + {dom}   (stride, histogram-uniform)")

    # T2 entry linear relations a = b + c at the FIRST event of the segment
    e = seg[0]
    ek = [k for k in keys if k in e]
    for a in ek:
        for b, c in combinations([x for x in ek if x != a], 2):
            if e[a] == e[b] + e[c]:
                facts.add(f"T2 {a} = {b} + {c}   (entry linear)")
        for b in [x for x in ek if x != a]:
            d = e[a] - e[b]
            # only surface small/meaningful offsets to avoid noise
            if 0 < abs(d) <= 4096:
                facts.add(f"T2 {a} = {b} + {d}   (entry offset)")

    # T5 mem-window facts: word m*_* constant across segment (= slot pin) or
    # equal to a register value
    for k in [k for k in keys if k.startswith("m")]:
        vals = {r[k] for r in seg if k in r}
        if len(vals) == 1:
            v = next(iter(vals))
            facts.add(f"T5 {k} = 0x{v:x}   (mem-window constant / slot pin)")
            for rk in keys:
                if not rk.startswith("m") and all(
                        r.get(rk) == v for r in seg):
                    facts.add(f"T5 {k} = {rk}   (mem word = reg)")
    return facts


def schematize(fact):
    """Strip per-call specific constant values to a schema so per-call
    constants intersect across segments (value differs, shape doesn't)."""
    if "per-segment constant" in fact:
        return fact.split("=")[0].strip() + " : per-call constant"
    return fact


def stride_ladder(segs):
    """Round-2 correction (2): histogram sp strides across the WHOLE trace (the
    call-nesting ladder), not endpoint differences.  A deeper call has strictly
    smaller sp; the per-descent |Δsp| histogram cleanly separates the two frame
    constants (eval 1088, exec 176) that a naive endpoint slope fit smears."""
    seq = [r["sp"] for s in segs for r in s if "sp" in r]
    deltas = [seq[i] - seq[i + 1] for i in range(len(seq) - 1)]
    deltas = [d for d in deltas if d != 0]
    if not deltas:
        return None
    return Counter(abs(d) for d in deltas).most_common(6)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", required=True,
                    help="segmented JSONL (segment.py output)")
    ap.add_argument("--case", help="corpus case id for vocabulary scoping")
    args = ap.parse_args()

    segs = load_segments(args.inp)
    vocab = case_vocab(args.case) if args.case else None
    print(f"# mine — {sum(len(s) for s in segs)} events in {len(segs)} segments"
          + (f", vocab={sorted(vocab)}" if vocab else ""))

    schema = None
    for s in segs:
        f = {schematize(x) for x in mine_seg(s, vocab)}
        schema = f if schema is None else (schema & f)

    print("\n== MINED CANDIDATE CONJUNCTS (intersection across segments) ==")
    for x in sorted(schema or []):
        print(f"  * {x}")

    # GLOBAL constants (same value in EVERY event across all segments)
    keys = reg_keys(segs[0])
    for k in keys:
        allvals = {r[k] for s in segs for r in s if k in r}
        if len(allvals) == 1 and len(segs) > 1:
            print(f"  * T1 {k} = 0x{next(iter(allvals)):x}   (GLOBAL constant, "
                  f"every segment)")

    lad = stride_ladder(segs)
    if lad:
        print(f"\n== T3 STRIDE HISTOGRAM (round-2 correction) ==")
        print(f"  dominant sp deltas (|Δ|, count): {lad}")


if __name__ == "__main__":
    main()
