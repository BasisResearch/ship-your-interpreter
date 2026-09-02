#!/usr/bin/env python3
"""segment.py — call-instance segmentation (ANALYSIS ONLY, stage 2).

General mechanism from the plan: track sp (frame) at the traced PCs and segment
whenever the frame changes.  Validated heuristic (round 2): any per-call-constant
register works; sp is the principled one.  For pure loops with a per-call-constant
end pointer (io write), an explicit `--key` register also segments.

Reads the JSONL emitted by gen_trace.py; writes a segmented JSONL (each row gets
a `seg` index) and prints a segment summary.  Also usable as a library
(`load`, `segment`).

Nothing here enters a proof.
"""
import argparse
import json
import sys


def load(path):
    rows = []
    for line in open(path):
        line = line.strip()
        if line:
            rows.append(json.loads(line))
    return rows


def segment(rows, key="sp", stride_reg=None):
    """Segment on frame change.  key = the per-call-constant register (sp by
    default).  If stride_reg is given, ALSO split when it fails to advance by
    exactly 1 (a fresh call restarts a cursor) — the io-loop heuristic."""
    segs = []
    cur = []
    for r in rows:
        newseg = False
        if cur:
            if key in r and key in cur[-1] and r[key] != cur[-1][key]:
                newseg = True
            if (stride_reg and stride_reg in r and stride_reg in cur[-1]
                    and r[stride_reg] != cur[-1][stride_reg] + 1):
                newseg = True
        if newseg:
            segs.append(cur)
            cur = []
        cur.append(r)
    if cur:
        segs.append(cur)
    return segs


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--in", dest="inp", required=True)
    ap.add_argument("--out")
    ap.add_argument("--key", default="sp",
                    help="per-call-constant register to segment on (default sp)")
    ap.add_argument("--stride", default=None,
                    help="cursor register that advances by 1 per iter (io loops)")
    args = ap.parse_args()

    rows = load(args.inp)
    segs = segment(rows, key=args.key, stride_reg=args.stride)
    print(f"# segment — {len(rows)} events → {len(segs)} segments "
          f"(key={args.key}, stride={args.stride})")
    for i, s in enumerate(segs):
        span = ""
        if args.key in s[0]:
            span = f"{args.key}=0x{s[0][args.key]:x}"
        print(f"  segment {i}: {len(s)} events  {span}")

    if args.out:
        with open(args.out, "w") as f:
            for i, s in enumerate(segs):
                for r in s:
                    f.write(json.dumps(dict(seg=i, **r)) + "\n")
        print(f"# wrote segmented JSONL → {args.out}")


if __name__ == "__main__":
    main()
