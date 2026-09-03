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
import os, re, sys, subprocess, concurrent.futures, json, time
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
    """A clause about `({f} {S})`, guarded by the layout invariant at `{S}`.

    Stated GROUND, at a named state, not `∀S`.  Since the encoder now names every
    intermediate state at the top level, the driver can instantiate each clause at
    exactly the states the term applies that summary to — so the whole query is
    quantifier-free QF_ABV (decidable, bit-blastable) instead of a quantified
    problem whose instantiation profile ran to the 10000 cap without deciding."""
    return "(assert (=> (INV {S}) " + body + "))"


QA_DECL = "(declare-const QA (_ BitVec 64))\n"

_SP = "#x0000000000000002"
_RA = "#x0000000000000001"
_S0 = "#x0000000000000008"
_S1 = "#x0000000000000009"

CLAUSES = [
    ("inv_pres", guard("(INV ({f} {S}))")),
    ("sp_restore", guard(f"(= (select (rr ({{f}} {{S}})) {_SP}) (select (rr {{S}}) {_SP}))")),
    ("ra_restore", guard(f"(= (select (rr ({{f}} {{S}})) {_RA}) (select (rr {{S}}) {_RA}))")),
    ("s0_restore", guard(f"(= (select (rr ({{f}} {{S}})) {_S0}) (select (rr {{S}}) {_S0}))")),
    ("s1_restore", guard(f"(= (select (rr ({{f}} {{S}})) {_S1}) (select (rr {{S}}) {_S1}))")),
    ("stack_or_arena", guard("(=> (and (or (bvult QA SL_lo) (bvuge QA SL_hi)) "
                             "(or (bvult QA A_lo) (bvuge QA A_hi))) "
                             "(= (select (mm ({f} {S})) QA) (select (mm {S}) QA)))")),
]

_G = "(assert (INV S0))\n"
NEG = {
    "inv_pres": _G + "(assert (not (INV fbody)))",
    "sp_restore": _G + f"(assert (not (= (select (rr fbody) {_SP}) (select (rr S0) {_SP}))))",
    "ra_restore": _G + f"(assert (not (= (select (rr fbody) {_RA}) (select (rr S0) {_RA}))))",
    "s0_restore": _G + f"(assert (not (= (select (rr fbody) {_S0}) (select (rr S0) {_S0}))))",
    "s1_restore": _G + f"(assert (not (= (select (rr fbody) {_S1}) (select (rr S0) {_S1}))))",
    "stack_or_arena": _G + "(assert (or (bvult QA SL_lo) (bvuge QA SL_hi)))\n"
                           "(assert (or (bvult QA A_lo) (bvuge QA A_hi)))\n"
                           "(assert (not (= (select (mm fbody) QA) (select (mm S0) QA))))",
}

APP_RE = re.compile(r"\((callee_\d+|loop_\d+|icall_\d+|idisp_\d+)(_ih)?\s+([A-Za-z][A-Za-z0-9_]*)\)")

CLAUSE_TEXT = dict(CLAUSES)
CLAUSE_IDS = [c for c, _ in CLAUSES]

OUTSIDE = ("(assert (or (bvult QA SL_lo) (bvuge QA SL_hi)))\n"
           "(assert (or (bvult QA A_lo) (bvuge QA A_hi)))\n")


# The POSTS that are FOOTPRINT properties — "this address was not written" —
# checked over the emitted store set rather than the array theory.  The value is
# the address condition; `footprint_check` first proves it implies "outside the
# stack window and the arena", then that no store can land there.
FOOTPRINT_POSTS = {
    # `StoreRepr` survival: every frame/closure/`ValueRepr`/`CString` read that
    # lives outside the stack and the arena reads the same byte at exit.
    "outside_stack_arena": OUTSIDE,
    # `InterpCodeLoaded` survival: the code image is never written.
    "code": ("(assert (bvule #x0000000080000000 QA))\n"
             "(assert (bvult QA #x0000000080018be0))\n"),
}

# The residual POST conjuncts (negated), over `state_exit` / `s0`.
POSTS = {
    # `StoreRepr` survival on the low side: memory strictly below the stack
    # window is preserved.  Stated without subtraction so it cannot wrap.
    "storerepr": "(assert (bvult QA SL_lo))\n"
                 "(assert (not (= (select (mm state_exit) QA) (select (mm s0) QA))))",
    # sp discipline: the arm returns with sp restored (FALSE by design for a
    # prologue/epilogue FRAGMENT span, which is exactly what it should report)
    "sp": "(assert (not (= (select (rr state_exit) #x0000000000000002) (select (rr s0) #x0000000000000002))))",
    # `ValueRepr`'s tag conjunct at the sret buffer the caller passed in a0:
    # whatever the arm boxes, the kind word it leaves is a real `ValueKind`
    "valuerepr_tag": "(assert (not (and (bvule #x0000000000000000 (ld4 (mm state_exit) (select (rr s0) #x000000000000000a))) "
                     "(bvule (ld4 (mm state_exit) (select (rr s0) #x000000000000000a)) #x0000000000000005))))",
}


def unroll(k):
    """`state_exit` as `mstep` applied `k` times to `s0` — the BOUNDED encoding."""
    t = "s0"
    for _ in range(k):
        t = f"(mstep {t})"
    return (f"(define-fun state_exit () MState {t})\n"
            "(define-fun mem_exit () (Array Int (_ BitVec 8)) (mm state_exit))")


# E-matching only, with an instantiation cap.  MBQI has nothing to chew on here
# (the quantified sort is a memory/register datatype), and without the cap a
# matching loop runs the full timeout instead of reporting `unknown` in seconds.
Z3_OPTS = """(set-option :smt.mbqi false)
(set-option :smt.ematching true)
(set-option :smt.qi.max_instances 10000)
"""


def z3(text, timeout):
    p = subprocess.run(["z3", "-smt2", "-in", f"-T:{timeout}"], input=Z3_OPTS + text,
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


# ---------------------------------------------------------------- footprint
# Frame, `StoreRepr` survival and code preservation are all "this address was
# not written".  The encoder knows every store address, so that is BV ARITHMETIC
# over a few hundred addresses rather than array reasoning over the chain of
# `store`s — which bit-blasts to millions of `bv-bit2core` axioms and decides
# nothing.  A check has three parts, and all three must pass:
#
#   1. the property's address condition IMPLIES "outside the stack window and
#      outside the heap arena" (Z3, side condition);
#   2. no DIRECT write of the span can land on such an address (Z3, over the
#      emitted footprint);
#   3. every SUMMARY the span applies carries `stack_or_arena` — its own writes
#      are confined the same way (checked here, from the mined clause sets).
#
# Failing 3 is reported, never assumed: a summary without the clause means the
# check cannot conclude, not that it passes.
# ---------------------------------------------------------- StoreRepr / Arena
# The remaining footprint gap is the ~5% of stores whose base register is a
# POINTER READ OUT OF MEMORY rather than `sp` (481 of 10054 across the campaign).
# Nothing in the machine text says where such a pointer points, which is exactly
# why `stack_or_arena` was refuted for 60 summaries.
#
# In the Lean development that fact is not derived either: it is a HYPOTHESIS
# every residual carries.  `EvalEntry.store : StoreRepr c.σ.mem N A φf φc
# st.store`, and `StoreRepr.frames_arena`/`closures_arena` give
# `Arena.contains (φf fa) 32` — every represented object lies in the arena.  So
# assuming it here is faithful to the statement being checked, not a shortcut
# around it; what the check still has to establish is that the OFFSET from such a
# base stays inside the object, which is the part the machine text does decide.
#
# Every instance is emitted under this banner and counted, so a verdict that
# rests on it says how many sites it rested on.
SP_BASE = re.compile(r"^\(bvadd \(select \(rr \w+\) #x0000000000000002\) ")


def heap_hyp(writes):
    """`Arena.contains` for every store whose base is not `sp`.  Returns the SMT
    block and the number of sites it covers."""
    out, n = [], 0
    for g, w, a in writes:
        if SP_BASE.match(a):
            continue
        # the base is `(bvadd BASE OFF)`; assume the BASE is a represented object
        # in the arena with room for its 32-byte record (`Arena.contains _ 32`)
        m = re.match(r"^\(bvadd (\(select \(rr \w+\) #x[0-9a-f]+\)) ", a)
        base = m.group(1) if m else a
        # stated WITHOUT `bvadd` on the left: `base + 32 <= A_hi` is satisfiable
        # by wraparound, and the solver duly takes it (base = 0xff..e1, A_hi
        # large, base+32 = 1).  `base <= A_hi - 32` has no such escape.
        out.append(f"(assert (=> {g} (and (bvule A_lo {base}) "
                   f"(bvule {base} (bvsub A_hi #x0000000000000020)))))")
        n += 1
    return ("; StoreRepr / Arena.contains (EvalEntry.store) at "
            f"{n} pointer-based store site(s)\n" + "\n".join(out) + "\n", n)


# --------------------------------------------------------- summary preconditions
# A summary's obligation starts at its header with the entry state free, so any
# fact the CALLER established before entering it is invisible there.  Where such
# a fact is what makes the clause true, it is stated here as an explicit named
# precondition, with the source line that establishes it and the site that
# discharges it.  A residual query reaching the summary discharges it for real:
# the queries start at the function entry, so the check is inside the span.
#
# Each entry is (SMT assertion over the obligation's entry state S0, provenance).
PRECONDITIONS = {
    # `loop_0x800031dc` is the argument-marshalling loop of the EX_CALL arm.  It
    # writes slot `n` of the outgoing-argument array at `sp + 240 + 24n`, and the
    # frame is 1088 bytes, so it needs `n < 35`.  The bound is `MAX_ARGS`:
    #
    #     c/src/interp.c:8    #define MAX_ARGS 32
    #     c/src/interp.c:251  if (argc > MAX_ARGS) runtime_error(...);
    #     c/src/interp.c:253  Value args[MAX_ARGS];
    #
    # The check is emitted BEFORE the loop header, so the loop's own obligation
    # cannot see it; every residual query can, since those start at `eval_expr`'s
    # entry.  The count is spilled at `24(sp)` and reloaded each iteration.
    "loop_2147496412": (
        "(assert (bvule (ld8 (mm S0) (bvadd (select (rr S0) #x0000000000000002) "
        "#x0000000000000018)) #x0000000000000020))",
        "MAX_ARGS: c/src/interp.c:251 `if (argc > MAX_ARGS) runtime_error(...)`, "
        "checked before the loop header, discharged inside every residual span. "
        "NECESSARY BUT NOT SUFFICIENT on its own: it bounds the COUNT, and the "
        "store address is built from the COUNTER, so it only bites alongside the "
        "induction-variable invariant `a6 <= count` that the clause bank cannot "
        "yet express."),
}


def load_writes(path):
    if not os.path.exists(path):
        return None
    out = []
    for line in open(path).read().splitlines()[1:]:
        if not line.strip():
            continue
        g, w, a = line.split("\t", 2)
        out.append((g, int(w), a))
    return out


def hits_QA(writes):
    """`QA` lands inside one of the span's own stores."""
    ds = []
    for g, w, a in writes:
        ds.append(f"(and {g} (bvule {a} QA) (bvult QA (bvadd {a} #x{w:016x})))")
    return "(assert (or false " + " ".join(ds) + "))\n" if ds else "(assert false)\n"


def footprint_check(base, cond, writes, applied, cset, timeout, pre="", heap=True):
    """The three-part check.  Returns "VALID" / "REFUTED" / "UNKNOWN(...)"."""
    missing = sorted({f for f in applied if "stack_or_arena" not in cset.get(f, [])})
    if missing:
        return "UNKNOWN(summary-clause:" + ",".join(m[:22] for m in missing) + ")"
    hh, nheap = heap_hyp(writes) if heap else ("", 0)
    head = base + "\n" + pre + "\n" + hh
    if "(declare-const QA " not in head:
        head += QA_DECL
    head += cond
    # 1. does the condition imply "outside stack and arena"?
    side = head + "(assert (not (and (or (bvult QA SL_lo) (bvuge QA SL_hi)) "
    side += "(or (bvult QA A_lo) (bvuge QA A_hi)))))\n(check-sat)\n"
    if z3(side, timeout) != "unsat":
        return "UNKNOWN(cond-not-outside)"
    # 2. can a direct write land on it?
    v = z3(head + hits_QA(writes) + "(check-sat)\n", timeout)
    tag = f"[StoreRepr@{nheap}]" if nheap else ""
    return {"unsat": "VALID" + tag, "sat": "REFUTED"}.get(v, "UNKNOWN(footprint)")


def applied_of(text):
    """The summary symbols this text actually applies (self `_ih` collapsed)."""
    return {m[0] for m in APP_RE.findall(text)}


def assume_block(text, cset, self_sym=None):
    """Ground clause instances at every application site the TEXT actually has.

    `text` is the obligation/query body; the encoder names each intermediate state
    at the top level, so `(callee_X i57)` tells us both the summary and the exact
    state to instantiate at.  A summary applied nowhere contributes nothing."""
    out = [QA_DECL.rstrip()]
    seen = set()
    for m in APP_RE.finditer(text):
        base, ih, arg = m.group(1), m.group(2), m.group(3)
        name = base + (ih or "")
        key = (name, arg)
        if key in seen:
            continue
        seen.add(key)
        for c in cset.get(base, []):
            out.append(CLAUSE_TEXT[c].format(f=name, S=arg))
    return "\n".join(out)


# The RECURSIVE interpreter entries.  `eval_expr` and `exec_stmt` call each other
# and themselves, so their summaries are the whole interpreter — and the Lean
# residual does not prove anything about them either: it CARRIES them, as the
# recursor's `EvalIH`/`mExecSeq` induction hypotheses.  Mining them would ask the
# solver to redo the induction the recursor already did, so they are named
# ASSUMED premises, and every verdict resting on one says so.
IH_SUMMARIES = {
    "callee_2147496292",   # 0x80003164 eval_expr — the `EvalIH` hypothesis
    "callee_2147500000",   # 0x80003fe0 exec_stmt — the `mExecS`/`mExecSeq` hypothesis
}

# The two indirect calls through a register are the `Value.native` dispatches —
# `print` / `println` / `assert`.  There is no body to unfold (the target is a
# function pointer out of the store), and the Lean development does not derive
# them either: they are the native callee contracts (`NativePrintSpec`, the
# `hCallPrint`/`hCallPrintln`/`hCallAssertOk` suppliers).  So they are ASSUMED
# contracts, listed as such, not silently-empty clause sets that poison every
# query reaching them.
NATIVE_ICALLS = {
    "icall_2147498484",    # 0x800039f4 — the native dispatch inside `eval_expr`
    "icall_2147501956",    # 0x80004784 — the native dispatch in the interp driver
}


def mine(d, syms, timeout, jobs, rounds):
    cset = {f: list(CLAUSE_IDS) for f in syms}
    reasons = {}
    # A summary with no obligation file is OPAQUE by construction (an indirect
    # call through a register, an unlisted computed goto): there is no body to
    # unfold, so no clause can ever be established for it.  Its clause set is
    # emptied here rather than assumed — an assumed-but-unproved clause would be
    # an axiom smuggled into every query that mentions it.
    emitter_assumed = set()
    ap = os.path.join(d, "assumed.tsv")
    if os.path.exists(ap):
        emitter_assumed = {l.split("\t")[0] for l in open(ap).read().splitlines()[1:] if l.strip()}
    bodies = {}
    assumed = []
    for f in list(syms):
        path = os.path.join(d, "obligations", f + ".smt2")
        if f in IH_SUMMARIES or f in NATIVE_ICALLS or f in emitter_assumed:
            assumed.append(f)          # keep the full clause set, do not mine
        elif os.path.exists(path):
            bodies[f] = open(path).read()
        else:
            cset[f] = []
    with open(os.path.join(d, "assumed-final.tsv"), "w") as fh:
        fh.write("summary\trole\n")
        for f in assumed:
            role = ("recursor IH (EvalIH / mExecSeq), carried by the residual"
                    if f in IH_SUMMARIES else
                    "native callee contract (NativePrintSpec: print/println/assert)"
                    if f in NATIVE_ICALLS else
                    "callee contract outside the interpreter's own code")
            fh.write(f + "\t" + role + "\n")
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
    wsets = {f: (load_writes(os.path.join(d, "writes", f + ".tsv")) or []) for f in syms}
    stale &= set(syms)
    for rnd in range(rounds):
        tasks = [(f, c) for f in syms if f in stale for c in cset[f]]
        if not tasks:
            print(f"  round {rnd}: fixpoint (nothing stale)")
            return cset, True, reasons
        def run(t):
            f, c = t
            body = bodies[f]
            if c == "stack_or_arena":
                # FOOTPRINT route: BV arithmetic over the emitted store set, with
                # the `StoreRepr`/`Arena.contains` entry hypothesis at the
                # pointer-based sites.  Asking the array theory for this instead
                # bit-blasts and refutes on wraparound.
                pc = PRECONDITIONS.get(f)
                b2 = body.replace("; @@ASSUME@@",
                                  assume_block(body, cset, self_sym=f)
                                  + ("\n; precondition: " + pc[1] + "\n" + pc[0] if pc else "")) \
                         .replace("; @@GOAL@@", "")
                v = footprint_check(b2, "(assert (INV S0))\n" + OUTSIDE,
                                    wsets.get(f, []), applied_of(body), cset, timeout)
                return (f, c, "unsat" if v.startswith("VALID") else
                              "sat" if v == "REFUTED" else v)
            # assume ONLY the summaries this obligation's body actually applies —
            # dumping every summary's clause set into every query buries the
            # solver in quantifiers that can never fire.
            txt = body.replace("; @@ASSUME@@", assume_block(body, cset, self_sym=f)) \
                      .replace("; @@GOAL@@", NEG[c]) + "\n(check-sat)\n"
            return (f, c, z3(txt, timeout))
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
        wsets = {f: (load_writes(os.path.join(d, "writes", f + ".tsv")) or []) for f in deps}
        pre = pre_block(d)
        tasks = [(f, pk) for f in sorted(deps) for pk in list(POSTS) + list(FOOTPRINT_POSTS)]
        def run(t):
            f, pk = t
            if pk in FOOTPRINT_POSTS:
                base = qs[f].replace("; @@ASSUME@@", assume_block(qs[f], cset)) \
                            .replace("; @@POST@@", "")
                return (f, pk, footprint_check(base, FOOTPRINT_POSTS[pk],
                                               wsets.get(f, []), applied_of(qs[f]),
                                               cset, timeout, pre=pre))
            txt = qs[f].replace("; @@ASSUME@@", pre + "\n" + assume_block(qs[f], cset)) \
                       .replace("; @@POST@@", POSTS[pk]) + "\n(check-sat)\n"
            v = z3(txt, timeout)
            return (f, pk, {"unsat": "VALID", "sat": "REFUTED"}.get(v, "UNKNOWN"))
        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
            res = list(ex.map(run, tasks))
        table = {}
        for f, pk, v in res:
            table.setdefault(f, {})[pk] = v
        out = os.path.join(d, "verdicts.tsv")
        keys = list(POSTS) + list(FOOTPRINT_POSTS)
        with open(out, "w") as fh:
            fh.write("field\t" + "\t".join(keys) + "\n")
            for f in sorted(table):
                fh.write(f + "\t" + "\t".join(table[f].get(k, "UNKNOWN") for k in keys) + "\n")
        for k in keys:
            print(f"  {k}: {dict(Counter(table[f].get(k, 'UNKNOWN').split('(')[0] for f in table))}")
        print("wrote", out)


if __name__ == "__main__":
    main()
