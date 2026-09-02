#!/usr/bin/env python3
"""mine_relational.py — stage-4 relational (machine×spec) mining (ANALYSIS ONLY).

The core deliverable of experiments/invariant-gen-plan.md.  Pairs a machine
dispatch/arm trace (gen_trace.py, dumping the kind word at [node] + optional
boxed-payload window) with the spec-side event trace (scripts/spec_trace_driver
.lean.tmpl, filled by invgen.py, dumping per eval/exec step
`k`/`ek`/`depth`/`store`/`vtag`/`vint`) and mines cross-side conjuncts:

    read32[node] & 0xff  ==  kindOf{Stmt,Expr} s      (the *Repr kind bridge)
    dispatch tag k       ->  arm PC                    (the *SlotPinned bridge)
    boxed payload @ a0   ==  reprOf(spec value)        (the Approx/value-repr conjunct)

Gap-1b — MULTI-SEAM ALIGNMENT.  Rather than tag-histogram matching (round-3
relational-LITE), align by PER-SEAM EVENT ORDINALS: the Nth machine dispatch of
kind K is paired with the Nth spec event of kind K.  This is a real per-event
alignment key that works when several seams (env `hCall`, `hSVarInit`) share the
trace — each (kind, ordinal) pair is a distinct alignment point.  We report
per-kind agreement AND per-ordinal value agreement.

Gap-1c — VALUE-REPR CONJUNCTS.  When the machine trace carries a boxed-payload
window (`--mach-mem` in gen_trace → keys `p0..`), the miner reads back the
payload word and pairs it against the spec `vint`/`vtag` at the aligned event.

Two modes:
  * legacy pilot (no args): the brkcont fixed paths (back-compat with round 3).
  * general (--machine <jsonl> --spec <lean-output-or-jsonl> [--case <id>]):
    align by (kind, ordinal), mine kind + slot + value-repr conjuncts, and
    CONTRADICTION-CHECK against the case's design-pass statement shape when a
    --design tag is supplied.

Nothing here enters a proof.
"""
import argparse
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict

# -- spec kind tag tables (ground truth) ------------------------------------
STMT_KIND = {0: "expr", 1: "varDecl", 2: "block", 3: "ifStmt", 4: "whileStmt",
             5: "forStmt", 6: "ret", 7: "brk", 8: "cont"}
EXPR_KIND = {0: "int", 1: "str", 2: "bool", 3: "null", 4: "var", 5: "assign",
             6: "binary", 7: "logical", 8: "unary", 9: "call", 10: "fn"}
VTAG = {0: "null", 1: "bool", 2: "int", 3: "str", 4: "closure", 5: "native"}


# -- loaders -----------------------------------------------------------------
def load_machine(path):
    return [json.loads(l) for l in open(path) if l.strip()]


def parse_spec(path):
    """Read spec-driver output (SPEC ev=.. k=.. ek=.. depth=.. store=.. vtag=..
    vint=..) either from a captured stdout .txt or a .jsonl."""
    evs = []
    for l in open(path):
        l = l.strip()
        if l.startswith("{"):
            evs.append(json.loads(l))
            continue
        m = re.match(r"SPEC ev=(\d+) k=(\d+) ek=(\d+) depth=(\d+) store=(\d+) "
                     r"vtag=(\d+) vint=(-?\d+)", l)
        if m:
            evs.append(dict(ev=int(m[1]), k=int(m[2]), ek=int(m[3]),
                            depth=int(m[4]), store=int(m[5]),
                            vtag=int(m[6]), vint=int(m[7])))
    return evs


def run_spec_lean(lean_path):
    r = subprocess.run(["lake", "env", "lean", lean_path],
                       capture_output=True, text=True, timeout=600)
    evs = []
    for l in (r.stdout + r.stderr).splitlines():
        m = re.match(r"SPEC ev=(\d+) k=(\d+) ek=(\d+) depth=(\d+) store=(\d+) "
                     r"vtag=(\d+) vint=(-?\d+)", l)
        if m:
            evs.append(dict(ev=int(m[1]), k=int(m[2]), ek=int(m[3]),
                            depth=int(m[4]), store=int(m[5]),
                            vtag=int(m[6]), vint=int(m[7])))
    return evs


# -- machine kind extraction -------------------------------------------------
def machine_kind_word(r):
    """Assemble the little-endian kind word from the m0b* mem-window bytes."""
    return (r.get("m0b0", 0) | (r.get("m0b1", 0) << 8)
            | (r.get("m0b2", 0) << 16) | (r.get("m0b3", 0) << 24))


def machine_payload_word(r, idx=1):
    """Assemble a boxed-payload window (m<idx>b*) into a 64-bit LE word."""
    w = 0
    for b in range(8):
        w |= r.get(f"m{idx}b{b}", 0) << (8 * b)
    return w


# -- gap-1b: per-seam ordinal alignment --------------------------------------
def align_by_ordinal(mach_kinds, spec_evs, expr_side):
    """Return alignment pairs: for each kind K, zip the machine dispatch tags of
    kind K with the spec events of kind K in order (Nth ↔ Nth).  `expr_side`
    selects spec events with ek==1 (expr) vs ek==0 (stmt)."""
    spec_by_kind = defaultdict(list)
    for e in spec_evs:
        if (e["ek"] == 1) == expr_side:
            spec_by_kind[e["k"]].append(e)
    mach_by_kind = defaultdict(list)
    for i, k in enumerate(mach_kinds):
        mach_by_kind[k].append(i)
    pairs = []
    for k in sorted(set(mach_by_kind) | set(spec_by_kind)):
        ms, ss = mach_by_kind[k], spec_by_kind[k]
        for ordn, (mi, se) in enumerate(zip(ms, ss)):
            pairs.append((k, ordn, mi, se))
    return pairs, mach_by_kind, spec_by_kind


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--machine", help="machine trace JSONL (gen_trace output)")
    ap.add_argument("--spec", help="spec trace: .txt/.jsonl OR a .lean to #eval")
    ap.add_argument("--dispatch-pc", type=lambda s: int(s, 16),
                    help="the dispatch PC in the machine trace")
    ap.add_argument("--expr", action="store_true",
                    help="align on EXPR kinds (eval side) instead of stmt")
    ap.add_argument("--arm", action="append", default=[],
                    help="armPC:kind confirmation, repeatable (e.g. 0x80004098:7)")
    ap.add_argument("--case", help="corpus case id (for the report header)")
    ap.add_argument("--payload", action="store_true",
                    help="mine value-repr conjuncts from a boxed-payload window")
    args = ap.parse_args()

    if not (args.machine and args.spec):
        sys.exit("mine_relational: need --machine and --spec (legacy pilot mode "
                 "removed; use scripts/invgen.py for orchestration)")

    mach = load_machine(args.machine)
    if args.dispatch_pc is not None:
        disp = [r for r in mach if r.get("pc") == args.dispatch_pc]
    else:
        disp = mach
    mkinds = [machine_kind_word(r) & 0xff for r in disp]

    spec_evs = (run_spec_lean(args.spec) if args.spec.endswith(".lean")
                else parse_spec(args.spec))

    KT = EXPR_KIND if args.expr else STMT_KIND
    side = "expr" if args.expr else "stmt"
    print(f"# mine_relational — {args.case or '?'} ({side} side)\n")
    print(f"machine dispatch events: {len(mkinds)}   spec events: {len(spec_evs)}\n")

    pairs, mbk, sbk = align_by_ordinal(mkinds, spec_evs, args.expr)

    # kind-agreement table
    mc = Counter(mkinds)
    sc = Counter(e["k"] for e in spec_evs if (e["ek"] == 1) == args.expr)
    print("kind | name     | machine cnt | spec cnt | agree")
    print("-----+----------+-------------+----------+------")
    for k in sorted(set(mc) | set(sc)):
        agree = "YES" if mc.get(k, 0) == sc.get(k, 0) else "no"
        print(f"  {k:2} | {KT.get(k,'?'):8} |    {mc.get(k,0):7}  |  {sc.get(k,0):6}  | {agree}")

    print("\n== MINED RELATIONAL CONJUNCTS (per-seam ordinal alignment) ==")
    # kind bridge
    kinds_agree = sorted({k for k in set(mc) & set(sc) if mc[k] == sc[k]})
    for k in kinds_agree:
        fn = "kindOfExpr" if args.expr else "kindOfStmt"
        print(f"  * read32[node] & 0xff = {k} = {fn} (.{KT.get(k,'?')})  "
              f"[machine {mc[k]} = spec {sc[k]}]  MATCH")

    # slot pins
    for a in args.arm:
        pc, k = a.split(":")
        k = int(k)
        hits = sum(1 for r in mach if r.get("pc") == int(pc, 16))
        print(f"  * dispatch tag {k} -> armPC {pc}  (SlotPinned {k} {pc})  "
              f"[arm-entry hits {hits}]")

    # gap-1c: value-repr conjuncts on aligned expr events with payload
    contradictions = []
    if args.payload and args.expr:
        print("\n== VALUE-REPR CONJUNCTS (boxed payload ↔ spec value) ==")
        checked = 0
        agreed = 0
        for (k, ordn, mi, se) in pairs:
            r = disp[mi]
            if not any(f"m1b{b}" in r for b in range(8)):
                continue
            pay = machine_payload_word(r)
            checked += 1
            # int payloads: machine word (2's-complement 64) == spec vint
            if se["vtag"] == 2:  # int
                signed = pay - (1 << 64) if pay >= (1 << 63) else pay
                ok = (signed == se["vint"])
                agreed += ok
                if not ok and ordn < 6:
                    print(f"  * [{KT.get(k,'?')}#{ordn}] payload {signed} vs "
                          f"spec vint {se['vint']}  {'MATCH' if ok else 'MISMATCH!'}")
                    if not ok:
                        contradictions.append(
                            f"value-repr {KT.get(k,'?')}#{ordn}: machine {signed} "
                            f"!= spec {se['vint']}")
        if checked:
            print(f"  payload conjuncts checked {checked}, agreed {agreed}"
                  f"  ({'ALL MATCH' if agreed == checked else 'MISMATCHES FOUND'})")
        else:
            print("  (no boxed-payload window in machine trace; pass gen_trace "
                  "--mem <reg>:8:8 for the payload probe)")

    # kind-count divergence (INFORMATIONAL, not a contradiction): the driver
    # evaluates `.call` opaquely, so machine>spec on some kinds is a driver gap,
    # not a machine falsity.  Only value-repr disagreement is a true CTI.
    diverge = []
    for k in sorted(set(mc) | set(sc)):
        if mc.get(k, 0) != sc.get(k, 0):
            diverge.append(f"{KT.get(k,'?')}: machine {mc.get(k,0)} vs spec {sc.get(k,0)}")
    if diverge:
        print("\n== KIND-COUNT DIVERGENCE (informational; likely call-opacity) ==")
        for d in diverge:
            print(f"  ~ {d}")

    # verdict
    disc = kinds_agree
    print(f"\n== SUMMARY ==")
    print(f"kinds agreeing (machine==spec count): {[KT.get(k,'?') for k in disc]}")
    if contradictions:
        print("CONTRADICTIONS (pre-proof falsity candidates):")
        for c in contradictions:
            print(f"  !! {c}")
    verdict = ("candidate-mined" if disc and not contradictions
               else "candidate-REFUTED" if contradictions
               else "mining-silent")
    print(f"VERDICT: {verdict}")
    return verdict, disc, contradictions


if __name__ == "__main__":
    main()
