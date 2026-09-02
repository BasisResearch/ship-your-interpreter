#!/usr/bin/env python3
"""mine_crux_ladder.py — closure-call depth-ladder miner for the hCallClosure crux.

ANALYSIS ONLY (pre-proof mining; same category as the fuzzer + emulator harness).
Nothing here enters a proof.

Extends the stack-ladder miner (mine_stack_ladder.py) to CLOSURE CALLS.  It reads
a multi-PC JSONL trace of the crux span produced by scripts/gen_trace.py:

  0x80003254 (callDispatchPC)   sp captured BEFORE the -1088 frame is committed
  0x8000329c (depth read/bump)   m0b0.. = call_depth word at 8(s2), post-bump
  0x800032bc (env_new call)      a0 = &closure_data (arity slot), a3 = fval
  0x800032dc (env_define fold)   s0 = frame env ptr, a3 = param node
  0x80003354 (callBodyLoopPC)    a0 = body-list head; the body handoff

Per closure-call depth level (d = the mined call_depth, matched to sp nesting):
  * sp delta per descent (bytes consumed by one eval_expr frame)
  * budget consumption vs StackNeed.perCallBudget / evalFrame / execFrame
  * frame-count growth (φ growth proxy) vs the depth counter d
  * the depth counter d vs the sp-reconstructed nesting depth (should agree)

Verdicts compare mined constants against Vsa/While/StackNeed.lean and the crux's
depth guard a_3 : d < maxCallDepth (maxCallDepth = 1000).
"""
import json
import sys
from collections import Counter, defaultdict

STACK_HI = 0x88000000       # LayoutInstance.stackSL top (linker 8 MiB stack)
EVAL_FRAME = 1088           # StackNeed.evalFrame (addi sp,sp,-1088)
EXEC_FRAME = 176            # StackNeed.execFrame
PER_CALL_BUDGET = 6144      # StackNeed.perCallBudget
MAX_CALL_DEPTH = 1000       # Vsa crux a_3

PC_DISPATCH = 0x80003254
PC_DEPTH    = 0x8000329c
PC_ENVNEW   = 0x800032bc
PC_ENVDEF   = 0x800032dc
PC_BODY     = 0x80003354


def load(path):
    rows = []
    for line in open(path):
        line = line.strip()
        if line:
            rows.append(json.loads(line))
    return rows


def le_word(row, n):
    """Assemble the little-endian mem word from m0b0..m0b{n-1} byte probes."""
    v = 0
    for i in range(n):
        b = row.get(f"m0b{i}", 0)
        v |= (b & 0xff) << (8 * i)
    return v


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else "/tmp/rl-trace/cruxDepth_trace.jsonl"
    rows = load(path)
    print(f"# mine_crux_ladder — {len(rows)} crux-span events\n")

    # Group each closure call by the DEPTH read event (PC_DEPTH), which carries
    # both the post-bump call_depth (m0b0..) and the current sp.  Each depth
    # event begins one closure-call frame at that depth.
    depth_events = []   # list of (idx, call_depth, sp)
    for r in rows:
        if r["pc"] == PC_DEPTH:
            depth_events.append((r["idx"], le_word(r, 4), r["x2"]))

    print(f"closure-call depth events (@0x8000329c, post-bump call_depth): "
          f"{len(depth_events)}")
    cds = [d for _, d, _ in depth_events]
    print(f"call_depth values observed: min={min(cds)} max={max(cds)}  "
          f"histogram={dict(sorted(Counter(cds).items()))}\n")

    # ---- Relation 1: sp delta per descent (parent frame -> child frame) ----
    # Reconstruct nesting from the sp discipline (a child call has strictly
    # smaller sp than its live parent), exactly the stack-ladder mechanism, but
    # keyed to the CLOSURE-CALL depth events so we can cross-check the counter.
    stack = []           # sp of currently-open eval frames
    sp_deltas = []       # sp(parent)-sp(child) at each descent
    depth_sp = defaultdict(list)   # reconstructed-depth -> sp values
    counter_vs_recon = []          # (call_depth counter, reconstructed depth)
    for _, cd, sp in depth_events:
        while stack and sp >= stack[-1]:
            stack.pop()
        if stack:
            sp_deltas.append(stack[-1] - sp)
        stack.append(sp)
        rd = len(stack)
        depth_sp[rd].append(sp)
        counter_vs_recon.append((cd, rd))

    uniq = sorted(set(sp_deltas))
    print("== R1: sp delta per closure-call descent (parent sp - child sp) ==")
    print(f"  observed deltas: {uniq}")
    print(f"  delta histogram: {Counter(sp_deltas).most_common(6)}")
    # Between two consecutive eval frames the machine committed at least one
    # eval_expr frame (1088) plus whatever exec_stmt/inner frames the arm chain
    # pushed.  The MINIMUM positive delta is the pure eval frame.
    pos = [d for d in uniq if d > 0]
    if pos:
        print(f"  minimum positive descent delta = {min(pos)} bytes "
              f"(matches evalFrame {EVAL_FRAME}: "
              f"{'YES' if min(pos) == EVAL_FRAME else 'NO — MISMATCH'})")

    # ---- Relation 2: budget consumption vs perCallBudget ----
    print("\n== R2: per-call-level budget vs StackNeed.perCallBudget ==")
    # The bytes consumed between successive closure-call frames = one call
    # level's whole chain (eval frames + exec frames for the body prologue up to
    # the next call).  Must be <= perCallBudget for the budget layer to be sound.
    print(f"  perCallBudget (StackNeed) = {PER_CALL_BUDGET}")
    max_level = max(pos) if pos else 0
    print(f"  max observed per-descent consumption = {max_level} bytes")
    if pos:
        ok = max_level <= PER_CALL_BUDGET
        print(f"  budget bound {max_level} <= {PER_CALL_BUDGET}: "
              f"{'HOLDS (validates perCallBudget)' if ok else 'VIOLATED — FALSITY CATCH'}")

    # ---- Relation 3: the machine call_depth counter IS the crux d ----
    print("\n== R3: call_depth counter (8(s2)) — the crux spec depth d ==")
    # The counter is post-bump and DECREMENTED on return (--call_depth), so it
    # is a RUNTIME quantity tracking the currently-active closure-call chain,
    # NOT the sp-static nesting (which also counts top-level println frames and
    # does not fall on sibling-call return).  So counter != sp-recon in general
    # (that is EXPECTED, not a falsity); within ONE recursion chain they move in
    # lockstep.  Isolate the clean recursion chain: a maximal run of depth events
    # whose call_depth strictly increases by 1 with strictly decreasing sp.
    chains = []
    cur = []
    prev_cd = prev_sp = None
    for _, cd, sp in depth_events:
        if prev_cd is not None and cd == prev_cd + 1 and sp < prev_sp:
            cur.append((cd, sp))
        else:
            if len(cur) >= 2:
                chains.append(cur)
            cur = [(cd, sp)]
        prev_cd, prev_sp = cd, sp
    if len(cur) >= 2:
        chains.append(cur)
    print(f"  isolated pure-recursion chains (d increments by 1, sp descends): "
          f"{len(chains)}")
    for ci, ch in enumerate(chains):
        deltas = [ch[i-1][1] - ch[i][1] for i in range(1, len(ch))]
        cdrange = f"{ch[0][0]}..{ch[-1][0]}"
        constd = len(set(deltas)) == 1
        print(f"  chain {ci}: call_depth {cdrange}, per-descent sp deltas={deltas}"
              f"  {'CONSTANT '+str(deltas[0])+' (= evalFrame+execFrame '+str(EVAL_FRAME+EXEC_FRAME)+')' if constd and deltas and deltas[0]==EVAL_FRAME+EXEC_FRAME else ('CONSTANT '+str(deltas[0]) if constd else 'VARIABLE')}")
    print("  NOTE: counter != sp-static-nesting across sibling calls is EXPECTED "
          "(--call_depth decrements on return); the crux d is the COUNTER.")

    # ---- Relation 4: demand ladder = d * frame + base (the crux invariant) ----
    print("\n== R4: headroom-demand ladder (STACK_HI - sp) vs d ==")
    demand = {}
    for rd in sorted(depth_sp):
        mn = min(depth_sp[rd])
        demand[rd] = STACK_HI - mn
        print(f"  recon-depth {rd}: min sp = 0x{mn:08x}, consumed = {demand[rd]} bytes")
    ds = sorted(demand)
    if len(ds) >= 2:
        n = len(ds)
        sx = sum(ds); sy = sum(demand[d] for d in ds)
        sxx = sum(d*d for d in ds); sxy = sum(d*demand[d] for d in ds)
        slope = (n*sxy - sx*sy) / (n*sxx - sx*sx)
        intercept = (sy - slope*sx) / n
        print(f"  MINED LADDER: consumed(d) ~= {slope:.0f}*d + {intercept:.0f}")
        print(f"  per-level slope {slope:.0f} bytes; the crux's budget must be a "
              f"LADDER d*perLevel+base, NOT a constant — the falsity-#13 form.")
        # The constant-budget refutation depth (falsity #13 acceptance test).
        OLD_CONST = 2176
        bad = next((d for d in ds if demand[d] > OLD_CONST), None)
        if bad is not None:
            print(f"  ACCEPTANCE TEST (falsity #13): constant budget {OLD_CONST} "
                  f"EXCEEDED at recon-depth {bad} (demand {demand[bad]}) "
                  f"— refound from closure-call traces.")

    # ---- Relation 5: depth guard a_3 : d < maxCallDepth ----
    print("\n== R5: crux depth guard a_3 : d < maxCallDepth ==")
    print(f"  maxCallDepth = {MAX_CALL_DEPTH}; max observed call_depth = {max(cds)}")
    print(f"  guard d < {MAX_CALL_DEPTH} holds on trace: "
          f"{'YES' if max(cds) < MAX_CALL_DEPTH else 'NO — guard boundary reached'}")

    # ---- Relation 6: env_new/env_define frame slot layout (arg-slot layout) ----
    print("\n== R6: env_new frame + env_define arg-slot layout ==")
    envnew = [r for r in rows if r["pc"] == PC_ENVNEW]
    envdef = [r for r in rows if r["pc"] == PC_ENVDEF]
    body   = [r for r in rows if r["pc"] == PC_BODY]
    print(f"  env_new calls: {len(envnew)}  env_define-fold entries: {len(envdef)}  "
          f"body-handoff entries: {len(body)}")
    # env_new is called once per closure call (one fresh frame / call level).
    print(f"  env_new-per-depth-event: {len(envnew)}/{len(depth_events)} "
          f"(one fresh frame per closure call: "
          f"{'YES' if len(envnew) == len(depth_events) else 'CHECK — bypass/empty-body routes'})")


if __name__ == "__main__":
    main()
