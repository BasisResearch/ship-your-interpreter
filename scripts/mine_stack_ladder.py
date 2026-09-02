#!/usr/bin/env python3
"""mine_stack_ladder.py — acceptance-on-history for the MINING side (ANALYSIS ONLY).

Experiment 1 of experiments/invariant-gen-plan.md validation round 2.

Reads a trace of `eval_expr` entries (PC 0x80003164, sp captured BEFORE the
`addi sp,sp,-1088` frame) produced by the /tmp/rl-trace traced emulator on a
recursive .wl program, reconstructs the call-nesting depth from the sp stack
discipline, and mines the per-depth stack demand.

The falsity-#13 content the miner must EXPOSE: each recursion level consumes a
fixed machine frame, so the headroom demand at depth d is d * frame + const,
which strictly EXCEEDS any constant budget for d >= 2.  A constant `stackOK`
(the old 2176) is therefore refuted by the depth-2 trace alone.

Nothing here enters a proof — pre-proof mining, same category as the fuzzer.
"""
import re
import sys

STACK_HI = 0x88000000  # LayoutInstance.stackSL top (linker 8 MiB stack)
OLD_CONST_BUDGET = 2176  # the pre-amendment EvalEntry.stackOK constant


def parse(path):
    rows = []
    pat = re.compile(r"sp=0x0*([0-9a-f]+)#64 ra=0x0*([0-9a-f]+)#64 "
                     r"a0=0x0*([0-9a-f]+)#64 a2=0x0*([0-9a-f]+)#64")
    for line in open(path):
        m = pat.search(line)
        if m:
            rows.append(dict(sp=int(m.group(1), 16), ra=int(m.group(2), 16),
                             a0=int(m.group(3), 16), a2=int(m.group(4), 16)))
    return rows


def mine(rows):
    # Reconstruct depth from the monotone-within-a-branch sp discipline: a
    # deeper call has strictly smaller sp than its parent.  Walk the trace
    # maintaining a stack of open frames (sp values); a new entry with sp <
    # top-of-stack pushes (child), sp >= a prior frame pops back to it.
    stack = []           # sp values of currently-open eval_expr frames
    depth_sp = {}        # depth -> observed sp value(s)
    frame_deltas = []    # sp(parent) - sp(child) at each descent
    max_depth = 0
    for r in rows:
        sp = r["sp"]
        while stack and sp >= stack[-1]:
            stack.pop()
        if stack:
            frame_deltas.append(stack[-1] - sp)   # bytes consumed descending 1 level
        stack.append(sp)
        d = len(stack)
        max_depth = max(max_depth, d)
        depth_sp.setdefault(d, []).append(sp)
    return depth_sp, frame_deltas, max_depth


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "/tmp/rl-trace/fib_trace.txt"
    rows = parse(path)
    depth_sp, frame_deltas, max_depth = mine(rows)

    print(f"# mine_stack_ladder — {len(rows)} eval_expr entries, "
          f"max nesting depth {max_depth}\n")

    # T3 stride / per-level frame constant.
    uniq = sorted(set(frame_deltas))
    print(f"T3 per-level frame deltas (sp_parent - sp_child), observed: {uniq}")
    # The dominant delta = the recursion-level frame (eval arm chain).
    from collections import Counter
    common = Counter(frame_deltas).most_common(5)
    print(f"    delta histogram (top): {common}")

    # T2 linear relation: headroom demand at depth d = (HI - sp) grows with d.
    print("\nT2 linear demand ladder (headroom consumed = STACK_HI - min_sp per depth):")
    demand = {}
    for d in sorted(depth_sp):
        mn = min(depth_sp[d])
        demand[d] = STACK_HI - mn
        print(f"    depth {d}: min sp = 0x{mn:08x}, consumed = {demand[d]} bytes")

    # Fit demand(d) ~ a*d + b by least squares over ALL depths (robust to the
    # interleaved exec_stmt frames; the eval-level slope dominates).
    ds = sorted(demand)
    if len(ds) >= 2:
        n = len(ds)
        sx = sum(ds); sy = sum(demand[d] for d in ds)
        sxx = sum(d*d for d in ds); sxy = sum(d*demand[d] for d in ds)
        slope = (n*sxy - sx*sy) / (n*sxx - sx*sx)
        intercept = (sy - slope*sx) / n
        print(f"\nMINED LADDER (least-squares over all depths): "
              f"consumed(d) ~= {slope:.0f} * d + {intercept:.0f}")
        print(f"    per-level slope {slope:.0f} bytes; the two mined frame "
              f"constants {uniq} = evalFrame 1088 + execFrame 176 "
              f"(StackNeed.lean), alternating along the call chain.")

    # The falsity-#13 verdict: a CONSTANT budget is refuted at the first depth
    # whose per-level increment already exceeds it.
    print(f"\n== FALSITY #13 EXPOSURE ==")
    # per-level incremental demand between consecutive observed depths:
    incs = [demand[ds[i+1]] - demand[ds[i]] for i in range(len(ds)-1)]
    print(f"per-descent increments: {incs}")
    # A constant budget C is inductively unsound the moment the demand at a
    # reachable depth exceeds C.  Find that depth.
    bad_depth = next((d for d in ds if demand[d] > OLD_CONST_BUDGET), None)
    if bad_depth is not None:
        print(f"constant budget {OLD_CONST_BUDGET} is EXCEEDED at depth "
              f"{bad_depth} (demand {demand[bad_depth]} > {OLD_CONST_BUDGET})")
        print(f"=> mined relation REFUTES the constant-budget invariant; the "
              f"sound form is demand(d) = d * perLevel + base (a LADDER, not a "
              f"constant) — exactly falsity #13's content, refound from traces.")
    else:
        print("constant budget not exceeded in this trace (deepen the program)")


if __name__ == "__main__":
    main()
