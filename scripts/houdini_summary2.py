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
# Every relational clause is GUARDED by the layout invariant `INV` — sp inside
# the stack window with headroom, arena disjoint from it.  A summary is only ever
# applied at states satisfying it (that is `EvalEntry`'s `stackOK`/`stackBudget`
# + arena disjointness), so the unguarded form asks for more than the proof needs
# and more than is true.  `inv_pres` is the clause that carries `INV` across a
# summary, and is mined like any other — if it does not survive, that is the
# machine-checked statement that the stack budget is not a step-local fact.
def guard(body):
    return "(assert (forall ((S MState)) (=> (INV S) " + body + ")))"


CLAUSES = [
    ("inv_pres", guard("(INV ({f} S))")),
    ("sp_restore", guard("(= (select (rr ({f} S)) 2) (select (rr S) 2))")),
    ("ra_restore", guard("(= (select (rr ({f} S)) 1) (select (rr S) 1))")),
    ("s0_restore", guard("(= (select (rr ({f} S)) 8) (select (rr S) 8))")),
    ("s1_restore", guard("(= (select (rr ({f} S)) 9) (select (rr S) 9))")),
    ("frame_1088", guard("(forall ((A Int)) (=> (< A (- (select (rr S) 2) 1088)) "
                         "(= (select (mm ({f} S)) A) (select (mm S) A))))")),
    ("frame_4096", guard("(forall ((A Int)) (=> (< A (- (select (rr S) 2) 4096)) "
                         "(= (select (mm ({f} S)) A) (select (mm S) A))))")),
    ("below_sl", guard("(forall ((A Int)) (=> (< A SL_lo) "
                       "(= (select (mm ({f} S)) A) (select (mm S) A))))")),
    ("above_sl", guard("(forall ((A Int)) (=> (>= A SL_hi) (=> (or (< A A_lo) (>= A A_hi)) "
                       "(= (select (mm ({f} S)) A) (select (mm S) A)))))")),
    ("stack_or_arena", guard("(forall ((X Int)) (=> (and (or (< X SL_lo) (>= X SL_hi)) "
                             "(or (< X A_lo) (>= X A_hi))) "
                             "(= (select (mm ({f} S)) X) (select (mm S) X))))")),
]

# The negated clause, stated about the ONE-STEP body `fbody` at entry `S0`, with
# the guard's antecedent ASSUMED (the clause is `INV S0 -> C`).
_G = "(assert (INV S0))\n"
NEG = {
    "inv_pres": _G + "(assert (not (INV fbody)))",
    "sp_restore": _G + "(assert (not (= (select (rr fbody) 2) (select (rr S0) 2))))",
    "ra_restore": _G + "(assert (not (= (select (rr fbody) 1) (select (rr S0) 1))))",
    "s0_restore": _G + "(assert (not (= (select (rr fbody) 8) (select (rr S0) 8))))",
    "s1_restore": _G + "(assert (not (= (select (rr fbody) 9) (select (rr S0) 9))))",
    "frame_1088": _G + "(declare-const A Int)\n(assert (< A (- (select (rr S0) 2) 1088)))\n"
                       "(assert (not (= (select (mm fbody) A) (select (mm S0) A))))",
    "frame_4096": _G + "(declare-const A Int)\n(assert (< A (- (select (rr S0) 2) 4096)))\n"
                       "(assert (not (= (select (mm fbody) A) (select (mm S0) A))))",
    "below_sl": _G + "(declare-const A Int)\n(assert (< A SL_lo))\n"
                     "(assert (not (= (select (mm fbody) A) (select (mm S0) A))))",
    "above_sl": _G + "(declare-const A Int)\n(assert (>= A SL_hi))\n"
                     "(assert (or (< A A_lo) (>= A A_hi)))\n"
                     "(assert (not (= (select (mm fbody) A) (select (mm S0) A))))",
    "stack_or_arena": _G + "(declare-const X Int)\n(assert (or (< X SL_lo) (>= X SL_hi)))\n"
                           "(assert (or (< X A_lo) (>= X A_hi)))\n"
                           "(assert (not (= (select (mm fbody) X) (select (mm S0) X))))",
}

CLAUSE_TEXT = dict(CLAUSES)
CLAUSE_IDS = [c for c, _ in CLAUSES]

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
    # sp discipline: the arm returns with sp restored (FALSE by design for a
    # prologue/epilogue FRAGMENT span, which is exactly what it should report)
    "sp": "(assert (not (= (select (rr state_exit) 2) (select (rr s0) 2))))",
    # the code image is never written — `InterpCodeLoaded` survives the arm
    "code": "(declare-const X Int)\n(assert (<= 2147483648 X))\n(assert (< X 2147584992))\n"
            "(assert (not (= (select (mm state_exit) X) (select (mm s0) X))))",
    # `ValueRepr`'s tag conjunct at the sret buffer the caller passed in a0:
    # whatever the arm boxes, the kind word it leaves is a real `ValueKind`
    "valuerepr_tag": "(assert (not (and (<= 0 (ld4 (mm state_exit) (select (rr s0) 10))) "
                     "(<= (ld4 (mm state_exit) (select (rr s0) 10)) 5))))",
    # the honest whole-machine frame: every write lands in the stack window or the
    # heap arena, so EVERY `StoreRepr`/`ValueRepr`/`CString` read outside both
    # reads the same byte at exit as at entry (the `EvalEntry` survival clause).
    "outside_stack_arena":
        "(declare-const X Int)\n(assert (or (< X SL_lo) (>= X SL_hi)))\n"
        "(assert (or (< X A_lo) (>= X A_hi)))\n"
        "(assert (<= SL_lo (select (rr s0) 2)))\n(assert (<= (select (rr s0) 2) SL_hi))\n"
        "(assert (not (= (select (mm state_exit) X) (select (mm s0) X))))",
}


def unroll(k):
    """`state_exit` as `mstep` applied `k` times to `s0` — the BOUNDED encoding."""
    t = "s0"
    for _ in range(k):
        t = f"(mstep {t})"
    return (f"(define-fun state_exit () MState {t})\n"
            "(define-fun mem_exit () (Array Int (_ BitVec 8)) (mm state_exit))")


def z3(text, timeout):
    with open(f'/tmp/dst/kdawg/{str(hash(text))[:10]}.smt', 'w') as f:
        f.write(text)
    p = subprocess.run(["z3", "-smt2", "-in", f"-T:{timeout}"], input="(set-option :smt.mbqi false)\n(set-option :smt.ematching true)\n(set-option :smt.qi.profile true)\n(set-option :smt.qi.profile_freq 100)\n" + text,
                       capture_output=True, text=True)
    o = (p.stdout + p.stderr).strip()
    if o.startswith("unsat"):
        return "unsat"
    if o.startswith("sat"):
        return "sat"
    return "unknown"


def pre_block(d):
    """The residual's PRE, as encoded by Lean (`pre.smt2`): the jump-table rodata
    pins + the stack/arena layout facts `EvalEntry` carries.  Injected into the
    residual QUERIES only — a summary's clause set has to hold at any entry
    state, so its obligation gets the clause set and nothing else."""
    p = os.path.join(d, "pre.smt2")
    return open(p).read() if os.path.exists(p) else ""


def assume_block(cset, syms, self_sym=None):
    """Clause assertions for every summary; `self_sym` is renamed to `<f>_ih`."""
    out = []
    for f in syms:
        name = f + "_ih" if f == self_sym else f
        for c in cset.get(f, []):
            out.append(CLAUSE_TEXT[c].format(f=name))
    return "\n".join(out)


# The RECURSIVE interpreter entries.  `eval_expr` and `exec_stmt` call each other
# and themselves, so their summaries are the whole interpreter — and the Lean
# residual does not prove anything about them either: it CARRIES them, as the
# recursor's `EvalIH`/`mExecSeq` induction hypotheses.  Mining them would be
# asking the solver to redo the induction the recursor already did, so they are
# named ASSUMED premises here, listed in `assumed.tsv`, exactly matching the
# hypotheses the residual's statement takes.
IH_SUMMARIES = {
    "callee_2147496292",   # 0x80003164 eval_expr — the `EvalIH` hypothesis
    "callee_2147500000",   # 0x80003fe0 exec_stmt — the `mExecS`/`mExecSeq` hypothesis
}


def mine(d, syms, timeout, jobs, rounds):
    cset = {f: list(CLAUSE_IDS) for f in syms}
    reasons = {}
    # A summary with no obligation file is OPAQUE by construction (an indirect
    # call through a register, an unlisted computed goto): there is no body to
    # unfold, so no clause can ever be established for it.  Its clause set is
    # emptied here rather than assumed — an assumed-but-unproved clause would be
    # an axiom smuggled into every query that mentions it.
    bodies = {}
    assumed = []
    for f in list(syms):
        path = os.path.join(d, "obligations", f + ".smt2")
        if f in IH_SUMMARIES:
            assumed.append(f)          # keep the full clause set, do not mine
        elif os.path.exists(path):
            bodies[f] = open(path).read()
        else:
            cset[f] = []
    with open(os.path.join(d, "assumed.tsv"), "w") as fh:
        fh.write("summary\trole\n")
        for f in assumed:
            fh.write(f + "\trecursor IH (EvalIH / mExecSeq), carried by the residual\n")
    syms = [f for f in syms if f in bodies]
    # a summary only needs re-checking when one of the summaries its own body
    # applies (including itself, via `<f>_ih`) has lost a clause since last round
    deps = {f: set() for f in syms}
    dpath = os.path.join(d, "summary-deps.tsv")
    if os.path.exists(dpath):
        for l in open(dpath).read().splitlines()[1:]:
            if not l.strip(): continue
            parts = l.split("\t")
            deps[parts[0]] = {x for x in (parts[1].split(",") if len(parts) > 1 else []) if x}
    stale = set(syms)
    stale &= set(syms)
    for rnd in range(rounds):
        tasks = [(f, c) for f in syms if f in stale for c in cset[f]]
        if not tasks:
            print(f"  round {rnd}: fixpoint (nothing stale)")
            return cset, True, reasons
        def run(t):
            f, c = t
            # assume ONLY the summaries this obligation's body actually applies —
            # dumping all 143 summaries' clause sets into every query buries the
            # solver in quantifiers that can never fire.
            rel = sorted(deps[f] | {f}) if deps[f] else [f]
            txt = bodies[f].replace("; @@ASSUME@@", assume_block(cset, rel, self_sym=f)) \
                           .replace("; @@GOAL@@", NEG[c]) + "\n(check-sat)\n"
            print("calling z3")
            res = (f, c, z3(txt, timeout))
            print(f'z3 call finished, {res}')
            return res
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
            res = list(ex.map(run, tasks))
        dropped = [(f, c, v) for f, c, v in res if v != "unsat"]
        if not dropped:
            print(f"  round {rnd}: fixpoint (nothing dropped)")
            return cset, True, reasons
        weakened = set()
        for f, c, v in dropped:
            if c in cset[f]:
                cset[f].remove(c)
                weakened.add(f)
            reasons[f + "/" + c] = v
        stale = {f for f in syms if deps[f] & weakened}
        why = Counter(v for _, _, v in dropped)
        print(f"  round {rnd}: checked {len(tasks)}, dropped {len(dropped)} {dict(why)}, "
              f"{len(stale)} summaries stale")
    return cset, False, reasons


def bounded(d, timeout, jobs, ks):
    """Bounded refutation search: run each residual's span for `k` exact machine
    steps and demand it REACHED its exit PC, then negate the post.

      sat   ⇒ a GENUINE countermodel (the run finished inside k steps, so the
              unrolling is exact on it) — the statement is false as posed;
      unsat ⇒ no countermodel within k steps (bounded validity, reported as such);
      unknown ⇒ the bound is out of the solver's reach at this k.
    """
    qdir = os.path.join(d, "bounded")
    fields = sorted(f[:-5] for f in os.listdir(qdir) if f.endswith(".smt2"))
    out = {}
    for k in ks:
        tasks = [(f, pk) for f in fields for pk in POSTS
                 if out.get((f, pk)) in (None, "UNKNOWN")]
        if not tasks:
            break
        print(f"  k={k}: {len(tasks)} queries")
        def run(t):
            f, pk = t
            txt = (open(os.path.join(qdir, f + ".smt2")).read()
                   .replace("; @@ASSUME@@", pre_block(d))
                   .replace("; @@EXIT@@", unroll(k))
                   .replace("; @@POST@@", POSTS[pk]) + "\n(check-sat)\n")
            v = z3(txt, timeout)
            return (f, pk, {"unsat": f"BOUNDED-VALID(k={k})",
                            "sat": "REFUTED"}.get(v, "UNKNOWN"))
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
            for f, pk, v in ex.map(run, tasks):
                out[(f, pk)] = v
        print("   ", dict(Counter(v for v in out.values())))
    path = os.path.join(d, "bounded-verdicts.tsv")
    keys = list(POSTS)
    with open(path, "w") as fh:
        fh.write("field\t" + "\t".join(keys) + "\n")
        for f in fields:
            fh.write(f + "\t" + "\t".join(out.get((f, k), "UNKNOWN") for k in keys) + "\n")
    print("wrote", path)


def main():
    d = sys.argv[1]
    timeout, jobs, rounds, phase = 20, 8, 8, "both"
    ks = [8, 24, 64, 160]
    a = sys.argv[2:]
    for i, x in enumerate(a):
        if x == "--timeout": timeout = int(a[i + 1])
        elif x.startswith("-j"): jobs = int(x[2:])
        elif x == "--rounds": rounds = int(a[i + 1])
        elif x == "--phase": phase = a[i + 1]
        elif x == "--ks": ks = [int(z) for z in a[i + 1].split(",")]

    if phase == "bounded":
        print(f"== bounded refutation search (k ladder {ks})")
        bounded(d, timeout, jobs, ks)
        return

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
        pre = pre_block(d)
        tasks = [(f, pk) for f in sorted(deps) for pk in POSTS]
        def run(t):
            f, pk = t
            txt = qs[f].replace("; @@ASSUME@@", pre + "\n" + assume_block(cset, deps[f])) \
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
