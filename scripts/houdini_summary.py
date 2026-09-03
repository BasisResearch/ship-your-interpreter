#!/usr/bin/env python3
"""houdini_summary.py — mine the per-summary clause set, then validate the 52.

ORCHESTRATOR ONLY.  Every SMT term is produced by Lean (`#emit_campaign` in
`experiments/smt/ReflectResiduals.lean`); this script never parses Lean source.
It fills the `; @@ASSUME@@` / `; @@GOAL@@` / `; @@POST@@` injection points with
generic clause text and shells Z3.

The mining is a Houdini fixpoint over a candidate clause set C(sym):

  repeat
    for each summary sym, for each clause c still in C(sym):
      obligation = <sym body, one-step, self as sym_ih>
                 + assume C for every summary (sym itself supplied as sym_ih)
                 + negate c at (S0, fbody)
      Z3 unsat  => c survives this round
      otherwise => drop c from C(sym)
  until nothing was dropped.

Surviving clauses are inductive under assume-guarantee, so they hold of the real
summaries (induction on the execution).  Phase 2 then runs each residual query
with the surviving clauses asserted in place of the defining axioms — weaker
than the definitions, so an UNSAT there is an UNSAT under the definitions.

Usage:
  python3 scripts/houdini_summary.py <campaign-dir> [--timeout S] [-jN]
     [--rounds N] [--phase mine|check|both]
"""
import os, sys, subprocess, concurrent.futures, json, time
from collections import Counter

# ---------------------------------------------------------------- clause bank
# Each clause is (id, text-template).  `{f}` is the summary symbol.  Every
# clause is a closed `forall` over an arbitrary entry state `S`.
CLAUSES = [
    ("sp_restore",
     "(assert (forall ((S MState)) (= (select (rr ({f} S)) 2) (select (rr S) 2))))"),
    ("ra_restore",
     "(assert (forall ((S MState)) (= (select (rr ({f} S)) 1) (select (rr S) 1))))"),
    ("s0_restore",
     "(assert (forall ((S MState)) (= (select (rr ({f} S)) 8) (select (rr S) 8))))"),
    ("s1_restore",
     "(assert (forall ((S MState)) (= (select (rr ({f} S)) 9) (select (rr S) 9))))"),
    ("frame_1088",
     "(assert (forall ((S MState) (A Int)) (=> (< A (- (select (rr S) 2) 1088)) "
     "(= (select (mm ({f} S)) A) (select (mm S) A)))))"),
    ("frame_4096",
     "(assert (forall ((S MState) (A Int)) (=> (< A (- (select (rr S) 2) 4096)) "
     "(= (select (mm ({f} S)) A) (select (mm S) A)))))"),
    ("frame_65536",
     "(assert (forall ((S MState) (A Int)) (=> (< A (- (select (rr S) 2) 65536)) "
     "(= (select (mm ({f} S)) A) (select (mm S) A)))))"),
    ("frame_1e6",
     "(assert (forall ((S MState) (A Int)) (=> (< A (- (select (rr S) 2) 1000000)) "
     "(= (select (mm ({f} S)) A) (select (mm S) A)))))"),
    ("below_sl",
     "(assert (forall ((S MState) (A Int)) (=> (and (< A SL_lo) (< SL_lo (select (rr S) 2))) "
     "(= (select (mm ({f} S)) A) (select (mm S) A)))))"),
    ("stack_or_arena",
     "(assert (forall ((S MState) (X Int)) (=> (and (or (< X SL_lo) (>= X SL_hi)) "
     "(or (< X A_lo) (>= X A_hi))) (= (select (mm ({f} S)) X) (select (mm S) X)))))"),
]
CLAUSE_TEXT = dict(CLAUSES)
CLAUSE_IDS = [c for c, _ in CLAUSES]

# The negated clause, stated about the ONE-STEP body `fbody` at entry `S0`.
NEG = {
    "sp_restore": "(assert (not (= (select (rr fbody) 2) (select (rr S0) 2))))",
    "ra_restore": "(assert (not (= (select (rr fbody) 1) (select (rr S0) 1))))",
    "s0_restore": "(assert (not (= (select (rr fbody) 8) (select (rr S0) 8))))",
    "s1_restore": "(assert (not (= (select (rr fbody) 9) (select (rr S0) 9))))",
    "frame_1088": "(declare-const A Int)\n(assert (< A (- (select (rr S0) 2) 1088)))\n"
                  "(assert (not (= (select (mm fbody) A) (select (mm S0) A))))",
    "frame_4096": "(declare-const A Int)\n(assert (< A (- (select (rr S0) 2) 4096)))\n"
                  "(assert (not (= (select (mm fbody) A) (select (mm S0) A))))",
    "frame_65536": "(declare-const A Int)\n(assert (< A (- (select (rr S0) 2) 65536)))\n"
                   "(assert (not (= (select (mm fbody) A) (select (mm S0) A))))",
    "frame_1e6": "(declare-const A Int)\n(assert (< A (- (select (rr S0) 2) 1000000)))\n"
                 "(assert (not (= (select (mm fbody) A) (select (mm S0) A))))",
    "below_sl": "(declare-const A Int)\n(assert (< A SL_lo))\n(assert (< SL_lo (select (rr S0) 2)))\n"
                "(assert (not (= (select (mm fbody) A) (select (mm S0) A))))",
    "stack_or_arena": "(declare-const X Int)\n(assert (or (< X SL_lo) (>= X SL_hi)))\n"
                      "(assert (or (< X A_lo) (>= X A_hi)))\n"
                      "(assert (not (= (select (mm fbody) X) (select (mm S0) X))))",
}

# The residual POST conjuncts (negated), over `state_exit` / `s0`.
POSTS = {
    # frame: memory below the arm's own stack frame is preserved
    "frame": "(declare-const A Int)\n(assert (< A (- (select (rr s0) 2) 1000000)))\n"
             "(assert (not (= (select (mm state_exit) A) (select (mm s0) A))))",
    # StoreRepr survival: memory OUTSIDE the stack window is preserved, so every
    # FrameRepr/ClosureRepr/ValueRepr read in the arena reads the same byte.
    "storerepr": "(declare-const A Int)\n(assert (< A SL_lo))\n"
                 "(assert (< SL_lo (- (select (rr s0) 2) 1000000)))\n"
                 "(assert (not (= (select (mm state_exit) A) (select (mm s0) A))))",
    # sp discipline: the arm returns with sp restored
    "sp": "(assert (not (= (select (rr state_exit) 2) (select (rr s0) 2))))",
    # the honest whole-machine frame: every write lands in the stack window or the
    # heap arena, so EVERY `StoreRepr`/`ValueRepr`/`CString` read outside both
    # reads the same byte at exit as at entry (the `EvalEntry` survival clause).
    "outside_stack_arena":
        "(declare-const X Int)\n(assert (or (< X SL_lo) (>= X SL_hi)))\n"
        "(assert (or (< X A_lo) (>= X A_hi)))\n"
        "(assert (<= SL_lo (select (rr s0) 2)))\n(assert (<= (select (rr s0) 2) SL_hi))\n"
        "(assert (not (= (select (mm state_exit) X) (select (mm s0) X))))",
}


def z3(text, timeout):
    p = subprocess.run(["z3", "-smt2", "-in", f"-T:{timeout}"], input=text,
                       capture_output=True, text=True)
    o = (p.stdout + p.stderr).strip()
    if o.startswith("unsat"):
        return "unsat"
    if o.startswith("sat"):
        return "sat"
    return "unknown"


def assume_block(cset, syms, self_sym=None):
    """Clause assertions for every summary; `self_sym` is renamed to `<f>_ih`."""
    out = []
    for f in syms:
        name = f + "_ih" if f == self_sym else f
        for c in cset.get(f, []):
            out.append(CLAUSE_TEXT[c].format(f=name))
    return "\n".join(out)


def mine(d, syms, timeout, jobs, rounds):
    cset = {f: list(CLAUSE_IDS) for f in syms}
    reasons = {}
    bodies = {f: open(os.path.join(d, "obligations", f + ".smt2")).read() for f in syms}
    for rnd in range(rounds):
        tasks = [(f, c) for f in syms for c in cset[f]]
        def run(t):
            f, c = t
            txt = bodies[f].replace("; @@ASSUME@@", assume_block(cset, syms, self_sym=f)) \
                           .replace("; @@GOAL@@", NEG[c]) + "\n(check-sat)\n"
            return (f, c, z3(txt, timeout))
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
            res = list(ex.map(run, tasks))
        dropped = [(f, c, v) for f, c, v in res if v != "unsat"]
        if not dropped:
            print(f"  round {rnd}: fixpoint (nothing dropped)")
            return cset, True, reasons
        for f, c, v in dropped:
            if c in cset[f]:
                cset[f].remove(c)
            reasons[f + "/" + c] = v
        why = Counter(v for _, _, v in dropped)
        print(f"  round {rnd}: dropped {len(dropped)} clause(s)  {dict(why)}")
    return cset, False, reasons


def main():
    d = sys.argv[1]
    timeout, jobs, rounds, phase = 20, 8, 8, "both"
    a = sys.argv[2:]
    for i, x in enumerate(a):
        if x == "--timeout": timeout = int(a[i + 1])
        elif x.startswith("-j"): jobs = int(x[2:])
        elif x == "--rounds": rounds = int(a[i + 1])
        elif x == "--phase": phase = a[i + 1]

    syms = [l.strip() for l in open(os.path.join(d, "summaries.tsv")).read().splitlines()[1:] if l.strip()]
    deps = {}
    for l in open(os.path.join(d, "query-summaries.tsv")).read().splitlines()[1:]:
        if not l.strip(): continue
        parts = l.split("\t")
        deps[parts[0]] = [x for x in (parts[1].split(",") if len(parts) > 1 else []) if x]

    csetpath = os.path.join(d, "clauses.json")
    if phase in ("mine", "both"):
        print(f"== phase 1: Houdini over {len(syms)} summaries x {len(CLAUSE_IDS)} clauses")
        t0 = time.time()
        cset, fix, reasons = mine(d, syms, timeout, jobs, rounds)
        json.dump(reasons, open(os.path.join(d, "drop-reasons.json"), "w"), indent=1)
        json.dump(cset, open(csetpath, "w"), indent=1)
        surv = Counter(c for v in cset.values() for c in v)
        print(f"  fixpoint={fix}  ({time.time()-t0:.0f}s)  surviving: {dict(surv)}")
        for f in syms:
            print(f"    {f}: {cset[f]}")
    else:
        cset = json.load(open(csetpath))

    if phase in ("check", "both"):
        print(f"== phase 2: {len(deps)} residual queries x {len(POSTS)} post conjuncts")
        qs = {f: open(os.path.join(d, "queries", f + ".smt2")).read() for f in deps}
        tasks = [(f, pk) for f in sorted(deps) for pk in POSTS]
        def run(t):
            f, pk = t
            txt = qs[f].replace("; @@ASSUME@@", assume_block(cset, deps[f])) \
                       .replace("; @@POST@@", POSTS[pk]) + "\n(check-sat)\n"
            v = z3(txt, timeout)
            return (f, pk, {"unsat": "VALID", "sat": "REFUTED"}.get(v, "UNKNOWN"))
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
            res = list(ex.map(run, tasks))
        table = {}
        for f, pk, v in res:
            table.setdefault(f, {})[pk] = v
        out = os.path.join(d, "verdicts.tsv")
        keys = list(POSTS)
        with open(out, "w") as fh:
            fh.write("field\t" + "\t".join(keys) + "\n")
            for f in sorted(table):
                fh.write(f + "\t" + "\t".join(table[f][k] for k in keys) + "\n")
        for k in keys:
            print(f"  {k}: {dict(Counter(table[f][k] for f in table))}")
        print("wrote", out)


if __name__ == "__main__":
    main()
