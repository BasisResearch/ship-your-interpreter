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
import os, re, sys, subprocess, concurrent.futures, json, time, csv, threading
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
    # `G_lo`/`G_hi` — the image's WRITABLE STATIC region, emitted as ground
    # constants by `#emit_bmc` (`ReflectSpan.writableRegion`).  Without the
    # exemption this clause is FALSE of the C runtime and a trace refutes it on
    # every application: `malloc` writes its free-list head, `fputc` the stream
    # buffer, anything that can fail writes `errno` -- all in neither window, so
    # for the windows that do not happen to cover them the clause is a falsity,
    # and it propagated into the MINED `callee_eval_expr`/`callee_exec_stmt`.
    # `.text` and `.rodata` sit BELOW this region, so what the clause is used for
    # -- code and jump-table preservation -- is untouched.
    ("stack_or_arena", guard("(=> (and (or (bvult QA SL_lo) (bvuge QA SL_hi)) "
                             "(or (bvult QA A_lo) (bvuge QA A_hi)) "
                             "(or (bvult QA G_lo) (bvuge QA G_hi))) "
                             "(= (select (mm ({f} {S})) QA) (select (mm {S}) QA)))")),
    # the ABI fact: a callee writes its OWN frame, below its entry `sp`, plus the
    # heap.  Nothing at or above the entry `sp` and outside the arena is touched,
    # so the caller's spill slots survive the call.  True of functions, false of a
    # loop inside a frame (whose stores are at `sp + k`), and Houdini sorts them.
    ("above_sp", guard(f"(=> (and (bvuge QA (select (rr {{S}}) {_SP})) "
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
                           "(assert (or (bvult QA G_lo) (bvuge QA G_hi)))\n"
                           "(assert (not (= (select (mm fbody) QA) (select (mm S0) QA))))",
    "above_sp": _G + f"(assert (bvuge QA (select (rr S0) {_SP})))\n"
                     "(assert (or (bvult QA A_lo) (bvuge QA A_hi)))\n"
                     "(assert (not (= (select (mm fbody) QA) (select (mm S0) QA))))",
}

APP_RE = re.compile(r"\((callee_\d+|loop_\d+|icall_\d+|idisp_\d+)(_ih)?\s+([A-Za-z][A-Za-z0-9_]*)\)")

CLAUSE_TEXT = dict(CLAUSES)
CLAUSE_IDS = [c for c, _ in CLAUSES]

OUTSIDE = ("(assert (or (bvult QA SL_lo) (bvuge QA SL_hi)))\n"
           "(assert (or (bvult QA A_lo) (bvuge QA A_hi)))\n"
           "(assert (or (bvult QA G_lo) (bvuge QA G_hi)))\n")


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

# `eval_expr`'s entry: the region whose arms box a `Value` at the caller's a0,
# and so the only region on which `valuerepr_tag` says anything.
EVAL_REGION = "0x80003164"

# The residual POST conjuncts (negated), over `state_exit` / `s0`.
POSTS = {
    # `StoreRepr` survival on the low side: memory strictly below the stack
    # window is preserved.  Stated without subtraction so it cannot wrap.
    # Below the stack AND outside the arena.  `INV` permits the arena to sit
    # BELOW the stack window (`(or (bvult A_hi SL_lo) (bvugt A_lo SL_hi))`), so
    # without the arena exclusion an ordinary heap write refutes this -- which
    # is what "refuted" hInitStore, whose whole job is to initialise the store.
    # `StoreRepr` survival is a claim about memory outside BOTH regions; the
    # footprint route (`outside_stack_arena`) always said so, and this direct
    # memory-equality route is the cross-check on it, so it must say so too.
    # Below the stack, outside the arena, AND outside the writable statics.
    # The last exclusion was missing while `OUTSIDE` and the `stack_or_arena`
    # clause both had it, so this route refuted what the footprint route
    # permits.  `hInitStore` is the case: its whole job is to initialise the
    # interpreter's globals, and the countermodel put QA at 0x8001c01d, inside
    # [G_lo, G_hi) = [0x8001ad00, 0x8001c168), writing 0x00 -> 0x40.  Two routes
    # that check "the same" property have to state the same property; that was
    # already the lesson when this post forgot the ARENA.
    "storerepr": "(assert (bvult QA SL_lo))\n"
                 "(assert (or (bvult QA A_lo) (bvuge QA A_hi)))\n"
                 "(assert (or (bvult QA G_lo) (bvuge QA G_hi)))\n"
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


_DC = re.compile(r"^\(declare-const (\S+) (Bool|MState)\)$")
_BD = re.compile(r"^\(assert \(= (\S+) (.*)\)\)$")


def defunise(text):
    """`(declare-const X S)` immediately followed by `(assert (= X t))` becomes
    `(define-fun X () S t)`.

    The equational form makes every one of the ~600 state bindings an ARRAY
    EQUALITY atom, and z3's `solve-eqs` eliminates only about a third of them;
    the rest reach the array decision procedure and are answered with
    extensionality axioms (`array-ax2` 809154, `array-ext-ax` 8984 in 60s on
    one call-arm query).  As macros they are substituted and hash-consed and
    never become atoms at all.  Measured on two call-arm queries: 138s -> 10s
    and 107.5s -> 7.8s, and it applies to every query in the campaign.

    Runs here, inside `z3`, rather than at emit time because `slice_to` and
    `guard_of` key on the declare+assert form and must see it first."""
    lines = text.split("\n")
    out = list(lines)
    for i in range(len(lines) - 1):
        d, b = _DC.match(lines[i]), _BD.match(lines[i + 1])
        if d and b and d.group(1) == b.group(1):
            out[i] = f"(define-fun {d.group(1)} () {d.group(2)} {b.group(2)})"
            out[i + 1] = None
    return "\n".join(l for l in out if l is not None)


def z3(text, timeout):
    text = defunise(text)
    p = subprocess.run(["z3", "-smt2", "-in", f"-T:{timeout}"], input=Z3_OPTS + text,
                       capture_output=True, text=True)
    o = (p.stdout + p.stderr).strip()
    # A MALFORMED query is not an undecided one.  z3 prints `(error ...)` for an
    # unknown constant or a duplicate declaration and then carries on, so the
    # answer that follows is about a DIFFERENT problem than the one intended --
    # and folding that into "unknown" makes the miner silently drop the clause.
    # An encoder bug then looks exactly like a hard query.  This is how a state
    # name collision emptied all eleven loop clause sets and read as timeouts.
    if "(error" in o:
        sys.stderr.write("z3 ERROR (malformed query, NOT a verdict):\n  "
                         + "\n  ".join(l for l in o.splitlines()
                                       if l.startswith("(error"))[:600] + "\n")
        return "error"
    if o.startswith("unsat"):
        return "unsat"
    if o.startswith("sat"):
        return "sat"
    return "unknown"


def check_provenance(d):
    """Refuse to answer about artefacts a DIFFERENT encoder emitted.

    A campaign directory is read back long after it was written, and a second
    session regenerating it from another checkout of `ReflectSpan.lean` /
    `ReflectResiduals.lean` is not hypothetical — it happened, and a `--phase
    check` run reported five fields VACUOUS that the tree they were re-emitted
    from reports UNKNOWN.  `#emit_bmc` copies its sources into `<dir>/src/`;
    this compares them BYTE FOR BYTE with the tree, so a stale directory is a
    refusal rather than a verdict.  Bytes, not a hash: a hash has to be
    recomputed identically on this side, and that is one more thing that drifts.
    """
    src = os.path.join(d, "src")
    if not os.path.isdir(src):
        sys.stderr.write(f"houdini: {d} has no src/ provenance; re-emit with "
                         f"`#emit_bmc` before trusting these verdicts\n")
        return
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    stale = [nm for nm in ("ReflectSpan.lean", "ReflectResiduals.lean")
             if os.path.exists(os.path.join(src, nm))
             and open(os.path.join(src, nm), "rb").read()
             != open(os.path.join(root, "experiments", "smt", nm), "rb").read()]
    if stale:
        sys.exit(f"houdini: {d} was emitted from a DIFFERENT {', '.join(stale)} "
                 f"than the tree has.  Re-emit (`#emit_bmc \"{d}\" 60`) and re-mine; "
                 f"answering against these artefacts would be a verdict about "
                 f"another program.")


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
    for g, w, a in (writes or []):
        if w == 0 or SP_BASE.match(a):
            continue
        # the base is `(bvadd BASE OFF)`; assume the BASE is a represented object
        # in the arena with room for its 32-byte record (`Arena.contains _ 32`)
        m = re.match(r"^\(bvadd (\(select \(rr \w+\) #x[0-9a-f]+\)) ", a)
        base = m.group(1) if m else a
        # stated WITHOUT `bvadd` on the left: `base + 32 <= A_hi` is satisfiable
        # by wraparound, and the solver duly takes it (base = 0xff..e1, A_hi
        # large, base+32 = 1).  `base <= A_hi - 32` has no such escape.
        # DISJUNCTIVE, because the entry pin is.  `entryPinsSmt` states the
        # sret fact honestly as `a0 + 24 <= SL_lo \/ sp <= a0`, and asserting
        # only the arena branch is asserting one side of somebody else's
        # disjunction: measured over the campaign's write sets, 1722 of 26825
        # stores are pointer-based and their bases are `s2` = the env (830),
        # `s1` = the caller's sret buffer (711), `a4` (108), `a0` (72) -- the
        # sret buffer is in the CALLER'S FRAME, not the arena.  The vacuity gate
        # cannot see it either, since the arena branch is satisfiable on its own.
        # Stating the disjunction keeps the footprint check working (an address
        # outside BOTH windows is still unreachable by these stores) and is
        # strictly weaker, so it can only lose VALIDs, never manufacture one.
        out.append(f"(assert (=> {g} (or (and (bvule A_lo {base}) "
                   f"(bvule {base} (bvsub A_hi #x0000000000000020))) "
                   f"(and (bvule SL_lo {base}) "
                   f"(bvule {base} (bvsub SL_hi #x0000000000000020))))))")
        n += 1
    return ("; StoreRepr / Arena.contains (EvalEntry.store) at "
            f"{n} pointer-based store site(s)\n" + "\n".join(out) + "\n", n)


# --------------------------------------------------------- summary preconditions
# A summary's obligation starts at its header with the entry state FREE, so any
# fact the caller established before entering it is invisible there.  That is the
# same shape as the `s1 = sret` problem the residual spans hit, and it has the
# same two cures: start the span earlier, or state the precondition.
#
# Stating one is only honest if it is both PROVED INDUCTIVE and DISCHARGED:
#
#   * inductive — the obligation additionally checks `IV(S0) -> IV(body-once)`
#     at the summary's own recursive occurrence, so assuming it at the header is
#     assuming something the loop preserves;
#   * discharged — every residual query that APPLIES the summary must prove
#     `IV(arg)` at the application site.  The queries start at the function
#     entry, so the guard that establishes it is inside the span.
#
# A summary whose IV a query cannot discharge is reported, never waved through.
IV_INVARIANTS = {
    # `loop_0x800031dc`, the argument-marshalling loop of the EX_CALL arm, writes
    # slot `n` of the outgoing-argument array at `sp + 240 + 24n`; the 1088-byte
    # frame needs `n < 35`.  Two facts give it:
    #
    #   a6 < a5   the counter is below the count (a6 = 0 on entry, a6++ each
    #             iteration, `bne a6,a5` at 0x80003250 closes the loop)
    #   a5 <= 32  MAX_ARGS — c/src/interp.c:8 `#define MAX_ARGS 32`, checked at
    #             c/src/interp.c:251 `if (argc > MAX_ARGS) runtime_error(...)`
    #             and at c/src/interp.c:253 `Value args[MAX_ARGS]`
    #
    # a5 = x15, a6 = x16.
    "loop_2147496412": (
        "(and (bvsle #x0000000000000000 (select (rr {S}) #x0000000000000010)) "
        "(bvslt (select (rr {S}) #x0000000000000010) "
        "(select (rr {S}) #x000000000000000f)) "
        "(bvsle (select (rr {S}) #x000000000000000f) #x0000000000000020))",
        "0 <= a6 < a5 <= 32.  Every comparison the machine makes here is SIGNED "
        "(`blt a4,a5` at 0x800031c8 is the MAX_ARGS check, `bge zero,a5` at "
        "0x800031d8 skips an empty loop, `bne a6,a5` at 0x80003250 closes it), so "
        "the invariant is too: an unsigned reading lets a5 be 0x8000..0, which "
        "passes the signed check and blows the unsigned bound"),
}


# Every prefix the encoder generates: `g` guards, `m` merge/arrival states, `b`
# arrival snapshots, `i` per-instruction states, `s` reference-encoder states,
# `ra` the return-address write before a call, `u` an unmodelled-word step.
# A prefix missing HERE is not a slicing near-miss: `slice_to` drops the
# declaration while the term still references it, and z3 answers a query about
# an unknown constant.
GEN_VAR = re.compile(r"^(?:g\d+[qx]?|ra\d+|u\d+|[mbis]\d+)$")
DECL_RE = re.compile(r"^\(declare-const (\S+) (?:Bool|MState)\)$")
BIND_RE = re.compile(r"^\(assert \(= (\S+) (.*)\)\)$")
DEFN_RE = re.compile(r"^\(define-fun (\S+) \(\)")


def slice_to(text, target, extra=()):
    """The part of a query that `target` actually depends on.

    The encoder emits the state chain as top-level `declare-const` + equational
    `assert`, in order, so a backward walk from one state variable keeps only the
    bindings that feed it.  A function-entry span carries ~150 summaries because
    the prologue drags them in, and an invariant-discharge query at the loop
    header needs none of what happens after it: slicing is what brings a check
    that does not return in 400 s back under budget."""
    lines = text.split("\n")
    bind, decl, order = {}, {}, []
    for i, l in enumerate(lines):
        m = DECL_RE.match(l)
        if m and GEN_VAR.match(m.group(1)):
            decl[m.group(1)] = i
            continue
        m = BIND_RE.match(l)
        if m and GEN_VAR.match(m.group(1)):
            bind[m.group(1)] = (i, m.group(2))
            order.append(m.group(1))
    roots = [target] + [e for e in extra if e]
    # Any generated variable a PLAIN assertion mentions is a root too.  The kind
    # pin says which dispatch guard holds by naming those guards directly; slicing
    # their bindings away leaves the assertion referring to an undeclared
    # constant, the file fails to parse, and the check reads as a failure.
    for l in lines:
        if BIND_RE.match(l) or DECL_RE.match(l) or not l.startswith("(assert "):
            continue
        for w in re.findall(r"[A-Za-z][A-Za-z0-9_]*", l):
            if w in bind:
                roots.append(w)
    if not any(r in bind for r in roots):
        return text
    need, work = set(), list(roots)
    while work:
        v = work.pop()
        if v in need or v not in bind:
            continue
        need.add(v)
        for w in re.findall(r"[A-Za-z][A-Za-z0-9_]*", bind[v][1]):
            if w in bind and w not in need:
                work.append(w)
    drop = set()
    for v in bind:
        if v not in need:
            drop.add(bind[v][0])
            if v in decl:
                drop.add(decl[v])
    # `state_exit`/`mem_exit` name the span's OUTCOME, which a header-invariant
    # discharge does not need and which references guards the slice just dropped.
    for i, l in enumerate(lines):
        if l.startswith("(define-fun state_exit ") or l.startswith("(define-fun mem_exit "):
            drop.add(i)
    # Any OTHER `define-fun` left standing must not reference a binding the slice
    # removed, or the file does not parse and the check reads as a failure rather
    # than as the malformed query it is.  `fbody` is the one that bites: a loop
    # obligation's exit is a guarded merge of the direct exit and the
    # post-`loop_ih` one, so it names guards an IV-discharge slice does not keep.
    for i, l in enumerate(lines):
        m = DEFN_RE.match(l)
        if not m or m.group(1) == target or i in drop:
            continue
        if any(w in bind and w not in need
               for w in re.findall(r"[A-Za-z][A-Za-z0-9_]*", l)):
            drop.add(i)
    return "\n".join(l for i, l in enumerate(lines) if i not in drop)


def iv_assume(f, state="S0"):
    """The summary's own invariant, at a named state."""
    iv = IV_INVARIANTS.get(f)
    return f"; IV: {iv[1]}\n(assert {iv[0].format(S=state)})\n" if iv else ""


def guard_of(text, sym, arg):
    """The guard the encoder bound immediately before applying `sym` to `arg`.

    `bmcRound` emits a merged arrival as the pair `(gK …)`, `(mK (loop_h …))`, so
    the guard is the binding one line above the application."""
    lines = text.split("\n")
    pat = re.compile(r"^\(assert \(= (\S+) \(" + re.escape(sym) + r" " + re.escape(arg) + r"\)\)\)$")
    for i, l in enumerate(lines):
        if pat.match(l):
            for j in range(i - 1, max(-1, i - 4), -1):
                m = BIND_RE.match(lines[j])
                if m and m.group(1).startswith("g"):
                    return m.group(1)
    return None


def sp_delta(head, timeout):
    """`sp_exit - sp_entry` read off one countermodel, or None.

    Only a candidate: the caller must still PROVE the shifted equality holds on
    every path before reporting it."""
    q = (head.replace("; @@POST@@", "") + "\n(check-sat)\n"
         "(get-value ((bvsub (select (rr state_exit) #x0000000000000002) "
         "(select (rr s0) #x0000000000000002))))\n")
    p = subprocess.run(["z3", "-smt2", "-in", f"-T:{timeout}"],
                       input=Z3_OPTS + defunise(q), capture_output=True, text=True)
    m = re.search(r"#x([0-9a-f]{16})\)\s*\)\s*$", p.stdout.strip())
    return int(m.group(1), 16) if m else None


def iv_discharge(text, cset, timeout, pre, writes=None):
    """Every application of an IV-carrying summary must PROVE the invariant at
    its argument.  Returns None if all discharge, else the failing site.

    The query is SLICED to the argument first, and the clause block is then built
    from the slice, so it only instantiates at sites the slice still contains."""
    for m in APP_RE.finditer(text):
        f, arg = m.group(1), m.group(3)
        iv = IV_INVARIANTS.get(f)
        if iv is None:
            continue
        g = guard_of(text, f, arg)
        sl = slice_to(text, arg, extra=(g,))
        # under the arrival's OWN guard: a loop that control never enters has no
        # invariant to establish, and `for (i = 0; i < argc; i++)` with argc = 0
        # is exactly that case.  The emitter binds the guard immediately before
        # the summary application it guards.
        # Per-ADDRESS and per-BYTE, exactly as the mining path does.  This was
        # the ONLY `assume_block` caller that left the memory clauses standing
        # at the free constant `QA`, and with them there a spill-then-reload
        # across a call is unconstrained: the args loop spills a5/a6 to
        # 24(sp)/16(sp), calls eval_expr, reloads them, and the solver is free
        # to say the reload returned something else -- it does, a6 = -3 and
        # a5 = 2^63-1, refuting `0 <= a6 < a5 <= 32` in 0.1s.  Instantiating
        # `sp_restore` + `above_sp` at the two reload addresses over all eight
        # bytes closes it in 2.8s.  One byte at the base address is not enough:
        # `ld8` reads eight.
        alive = set(re.findall(r"^\(declare-const (\S+) ", sl, re.M))
        rd = [a for a in dedup_addrs(writes, cap=64, reads_only=True)
              if all(v in alive or not GEN_VAR.match(v)
                     for v in re.findall(r"[A-Za-z]\w*", a))]
        ab = (assume_block(sl, cset) + "\n"
              + assume_block(sl, cset, addrs=rd, byteexp=True, decl=False))
        head = (sl.replace("; @@ASSUME@@", ab)
                  .replace("; @@POST@@", "") + "\n" + pre + "\n")
        gq = (f"(assert {g})\n" if g else "")
        # an arrival the span cannot reach has no invariant to establish.  A
        # function-entry span explores every arm of the AST dispatch, so a query
        # whose kind is pinned to one arm carries the others with an UNSAT guard.
        if g and z3(head + gq + "(check-sat)\n", timeout) == "unsat":
            continue
        goal = "(assert (not " + iv[0].format(S=arg) + "))\n(check-sat)\n"
        if z3(head + gq + goal, timeout) == "unsat":
            continue
        # CUT AND RETRY.  Sliced from eval_expr's entry this is ~600 lines and
        # 127 states, and z3 answers nothing in 170s -- not the discharge, not
        # even plain reachability.  Cutting the chain at a block state upstream
        # of the argument, leaving it constrained by `INV` alone, takes it to
        # ~180 lines and a few seconds.
        #
        # The cut is a WEAKENING, so `unsat` after it still proves the goal --
        # but only if `INV` really does hold at the cut, which is why it is
        # PROVED from the uncut slice first rather than assumed.  With that
        # proof in hand the cut hypotheses are implied by the real ones, and
        # the discharge transfers.
        if cut_discharge(sl, cset, pre, gq, goal, timeout):
            continue
        return f"{f}@{arg}"
    return None


def cut_discharge(sl, cset, pre, gq, goal, timeout, tries=4, cap=120):
    """Retry a discharge with the state chain cut at a block state.

    Walks candidate cut points latest-first: a later cut drops more of the
    chain and gives a smaller query, an earlier one keeps more context.  Each
    candidate must have `INV` PROVED at it from the uncut slice before it is
    used, so this never assumes the invariant it needs."""
    cands = re.findall(r"^\(declare-const (m\d+) MState\)$", sl, re.M)
    base = (sl.replace("; @@ASSUME@@", assume_block(sl, cset))
              .replace("; @@POST@@", "") + "\n" + pre + "\n")
    # A cut that WORKS is fast -- the whole point is that it takes the query
    # from ~600 lines to ~180 -- so giving each attempt the full budget only
    # buys waiting.  Cap it, or a site that will never discharge costs
    # `2 * tries * timeout` on its own.
    budget = min(timeout, cap)
    for c in list(reversed(cands))[:tries]:
        if z3(base + f"(assert (not (INV {c})))\n(check-sat)\n", budget) != "unsat":
            continue                      # INV not established here: unusable
        cut = re.sub(rf"^\(assert \(= {c} .*\)\)$", f"(assert (INV {c}))",
                     sl, flags=re.M)
        cb = (cut.replace("; @@ASSUME@@", assume_block(cut, cset))
                 .replace("; @@POST@@", "") + "\n" + pre + "\n")
        if z3(cb + gq + goal, budget) == "unsat":
            return True
    return False


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
    """`QA` lands inside one of the span's own stores.  Width 0 marks a READ
    address, which is an instantiation site rather than part of the footprint."""
    ds = []
    for g, w, a in (writes or []):
        if w == 0:
            continue
        # `QA - a <u w`, NOT `a <=u QA < a + w`.  The second form is false when
        # `a + w` wraps, so the aggregate comes back unsat and the post reads
        # VALID over a store the check never considered.  `heap_hyp` fixed
        # exactly this shape and this one did not get the same treatment.
        ds.append(f"(and {g} (bvult (bvsub QA {a}) #x{w:016x}))")
    return "(assert (or false " + " ".join(ds) + "))\n" if ds else "(assert false)\n"


def write_roots(writes):
    """Every variable the write set mentions — the roots a footprint check needs.

    The check never looks at `state_exit`: it is about the guards and addresses
    of the stores, so slicing to those roots drops the whole tail of the span."""
    out = set()
    for g, _, a in (writes or []):
        out.add(g)
        out.update(re.findall(r"[A-Za-z][A-Za-z0-9_]*", a))
    return out


def footprint_check(base, cond, writes, applied, cset, timeout, pre="", heap=True,
                    clause="stack_or_arena", side=True):
    # AN OPAQUE STEP IS NOT A STORE-FREE STEP.  This route composes "no direct
    # store hits QA" with "every applied summary carries the memory clause", and
    # `applied_of` only sees `callee_`/`loop_`/`icall_`/`idisp_` (APP_RE).
    # `unmodelled_step` is an unconstrained memory transformer that neither leg
    # covers, so a span containing one would report VALID over a step that can
    # write anywhere.  Zero occurrences in this image, which is exactly why it
    # has to be a refusal rather than a silence.
    #
    # Test for an APPLICATION, not the name.  `unmodelled_step` is declared
    # unconditionally in `smtPreamble`, so a bare substring test matches every
    # query through its `(declare-fun ...)` line and refuses all of them: 36
    # footprint verdicts were returned as opaque steps over a symbol that is
    # declared and never applied (measured: 0 applications across all 52).
    if re.search(r"\(unmodelled_step\s", base):
        return "UNKNOWN(opaque-step:unmodelled_step)"
    # A MISSING footprint is not an empty one.  `hits_QA([])` is `(assert false)`,
    # which is unsat, which reads as VALID — so a campaign emitted without write
    # sets (`#emit_campaign` leaves `writes/` empty; only `#emit_bmc` fills it)
    # would silently mark every footprint post valid.  Absent means UNKNOWN.
    if writes is None:
        return "UNKNOWN(no-footprint-recorded)"
    """The three-part check.  Returns "VALID" / "REFUTED" / "UNKNOWN(...)".

    `clause` is the summary clause the composition goes through, and `side` says
    whether the address condition must be shown to imply "outside the stack and
    the arena" (true for the region posts, false for `above_sp`, whose addresses
    are deliberately inside the stack)."""
    missing = sorted({f for f in applied if clause not in cset.get(f, [])})
    if missing:
        return "UNKNOWN(summary-clause:" + ",".join(m[:22] for m in missing) + ")"
    hh, nheap = heap_hyp(writes) if heap else ("", 0)
    head = base + "\n" + pre + "\n" + hh
    if "(declare-const QA " not in head:
        head += QA_DECL
    head += cond
    # 1. does the condition imply "outside stack and arena"?
    if side:
        sq = head + "(assert (not (and (or (bvult QA SL_lo) (bvuge QA SL_hi)) "
        sq += "(or (bvult QA A_lo) (bvuge QA A_hi)))))\n(check-sat)\n"
        if z3(sq, timeout) != "unsat":
            return "UNKNOWN(cond-not-outside)"
    # 2. can a direct write land on it?
    #
    # Aggregate first: one query whose assertion is the disjunction over every
    # store.  That closes in well under a second on the spans where nothing is
    # near QA, so it stays the fast path.
    tag = f"[StoreRepr@{nheap}]" if nheap else ""
    v = z3(head + hits_QA(writes) + "(check-sat)\n", min(timeout, 15))
    if v in ("unsat", "sat"):
        return {"unsat": "VALID" + tag, "sat": "REFUTED"}[v]
    # PER-STORE fallback.  The disjunction makes the solver carry all ~39 stores'
    # guard chains at once, and it times out without saying anything; asked one
    # store at a time each closes in a few seconds, and a failure comes back
    # NAMED with a countermodel instead of as a non-answer.  Measured on
    # hSIfNone: 39 stores, 35.4s total, 4.5s worst, versus unknown at 180s.
    # Per-store budget, capped independently.  A store that resolves at all
    # resolves fast -- measured on hSIfNone: 39 stores, all unsat, 35.4s TOTAL
    # and 4.5s worst.  At the full per-post timeout one field's fallback is
    # `39 * timeout` on its own, which is what made a -j10 --timeout 120 run
    # take hours with nothing to show.
    per = min(timeout, 30)
    stores = [(g, w, a) for g, w, a in writes if w != 0]
    unknown = []
    for g, w, a in stores:
        one = (f"(assert (and {g} (bvult (bvsub QA {a}) "
               f"#x{w:016x})))\n(check-sat)\n")
        r = z3(head + one, per)
        if r == "sat":
            return f"REFUTED(store:{a[:40]})"
        if r != "unsat":
            unknown.append(a[:24])
    if unknown:
        return "UNKNOWN(footprint:" + ",".join(unknown[:3]) + ")"
    return "VALID" + tag


def dedup_addrs(writes, cap=40, reads_only=False):
    writes = writes or []
    """The distinct addresses a span touches — stores AND loads, capped.

    Instantiating a memory clause at each is what lets a spill-then-reload across
    a call resolve: the spill's address is written over the pre-call state and the
    reload's over the post-call one, and instantiation is syntactic, so both have
    to be present."""
    out = []
    for _, w, a in writes:
        if reads_only and w != 0:
            continue
        if a not in out:
            out.append(a)
        if len(out) >= cap:
            break
    return out


def applied_of(text):
    """The summary symbols this text actually applies (self `_ih` collapsed)."""
    return {m[0] for m in APP_RE.findall(text)}


MEM_CLAUSES = ("stack_or_arena", "above_sp")


def assume_block(text, cset, self_sym=None, addrs=(), byteexp=True, decl=True):
    """Ground clause instances at every application site the TEXT actually has.

    `text` is the obligation/query body; the encoder names each intermediate state
    at the top level, so `(callee_X i57)` tells us both the summary and the exact
    state to instantiate at.  A summary applied nowhere contributes nothing.

    The memory clauses are additionally instantiated at every ADDRESS the span
    stores to, not only at `QA`.  Without that they constrain a single address and
    cannot justify a read-back: the args loop spills its counter to `16(sp)`,
    calls `eval_expr`, and reloads it, and with the clause only at `QA` the solver
    is free to say the reload returned something else."""
    out = [QA_DECL.rstrip()] if decl else []
    seen = set()
    sites = []
    for m in APP_RE.finditer(text):
        base, ih, arg = m.group(1), m.group(2), m.group(3)
        name = base + (ih or "")
        if (name, arg) in seen:
            continue
        seen.add((name, arg))
        sites.append((base, name, arg))
        for c in cset.get(base, []):
            out.append(CLAUSE_TEXT[c].format(f=name, S=arg))
    # per BYTE, not per address.  Every link in a spill-then-reload chain was
    # provable except the last, and the reason was exactly this: `ld8` reads eight
    # bytes, and a clause instantiated at the base address covers one.
    for a in addrs:
        for j in range(8 if byteexp else 1):
            aj = a if j == 0 else f"(bvadd {a} #x{j:016x})"
            for base, name, arg in sites:
                for c in cset.get(base, []):
                    if c in MEM_CLAUSES:
                        out.append(CLAUSE_TEXT[c].format(f=name, S=arg).replace("QA", aj))
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
}
# 0x80004784 is NOT a native dispatch.  It sits inside `exit` (newlib): the word
# at `gp+1184` is an atexit-style hook, indirect-called on the way to `_exit`.
# Assuming a full clause set for an arbitrary function pointer there would be
# assuming something about code the campaign has never looked at, so it stays
# OPAQUE — no obligation, empty clause set, and any verdict resting on it says so.


def mine(d, syms, timeout, jobs, rounds, warm=False):
    # `warm` starts the fixpoint from the clause set already on disk rather than
    # from all-clauses.  It cannot wrongly KEEP a clause — every survivor is
    # re-checked — but it will not RECOVER one an earlier run dropped, so after an
    # ENCODER change it under-reports and a cold run is needed to see the gain.
    # Use it while iterating on a fix, cold for the run whose numbers get
    # committed.
    cset = {f: list(CLAUSE_IDS) for f in syms}
    wp = os.path.join(d, "clauses.json")
    if warm and os.path.exists(wp):
        stored = json.load(open(wp))
        for f in syms:
            if f in stored:
                cset[f] = list(stored[f])
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
    emitter_drop = {}
    dp = os.path.join(d, "clause-drop.tsv")
    if os.path.exists(dp):
        for l in open(dp).read().splitlines()[1:]:
            if not l.strip():
                continue
            f, c = l.split("\t")[:2]
            emitter_drop.setdefault(f, []).append(c)
    bodies = {}
    assumed = []
    for f in list(syms):
        path = os.path.join(d, "obligations", f + ".smt2")
        if f in IH_SUMMARIES or f in NATIVE_ICALLS or f in emitter_assumed:
            assumed.append(f)          # keep the clause set, do not mine
            # ...except `above_sp`, which is FALSE for a great many of these and
            # verified for NONE of them.  It says nothing at or above the entry
            # `sp` and outside the arena is touched -- but every callee that
            # writes through a CALLER-PASSED POINTER breaks it, because that
            # pointer lives in the caller's frame, at or above the callee's
            # entry `sp`, and in the stack rather than the arena.  `pre.smt2`
            # permits exactly that layout.  The assumed set is full of them:
            # memcpy, strcpy, snprintf, setjmp, and the whole
            # value_int/value_bool/value_str/value_null family, which box a
            # Value into the sret buffer the caller supplies -- plus eval_expr
            # and exec_stmt as the recursor IHs.
            #
            # A MINED clause set is checked by construction.  These were checked
            # by nobody.  Dropping the clause only weakens what can be proved;
            # assuming it proves things that are not true.
            cset[f] = [c for c in cset[f] if c != "above_sp"]
            # ...and whatever else the emitter's structural analysis says the
            # image itself contradicts (`clause-drop.tsv`; today that is
            # `ra_restore` for the libgcc division family, which returns through
            # a register it saved `ra` into and so does NOT preserve `ra`).
            for c in emitter_drop.get(f, ()):
                if c in cset[f]:
                    cset[f].remove(c)
        elif os.path.exists(path):
            body = open(path).read()
            # THE SAME GATE THE QUERIES GET.  An obligation whose frontier did
            # not empty drops paths from `fbody`, so a clause can be mined that
            # is false on the dropped ones and then ASSUMED in every query that
            # applies the summary.  The emitter writes the flag as a comment and
            # nothing read it.  All 25 are complete today; `--rounds` and the
            # emit bound are arguments, and nothing caught that.
            if "; complete=false" in body:
                sys.exit(f"houdini: obligation {f} is INCOMPLETE (the BMC frontier "
                         f"did not empty within the emit bound), so its `fbody` is "
                         f"missing paths and any clause mined from it would be "
                         f"assumed on paths it was never checked against.  Re-emit "
                         f"with more rounds.")
            bodies[f] = body
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
    wsets = {f: load_writes(os.path.join(d, "writes", f + ".tsv")) for f in syms}
    stale &= set(syms)
    for rnd in range(rounds):
        tasks = [(f, c) for f in syms if f in stale for c in cset[f]]
        if not tasks:
            print(f"  round {rnd}: fixpoint (nothing stale)")
            return cset, True, reasons
        def run(t):
            f, c = t
            body = bodies[f]
            if c in ("stack_or_arena", "above_sp"):
                # FOOTPRINT route: BV arithmetic over the emitted store set, with
                # the `StoreRepr`/`Arena.contains` entry hypothesis at the
                # pointer-based sites.  Asking the array theory for this instead
                # bit-blasts and refutes on wraparound.
                addrs = dedup_addrs(wsets.get(f, []))
                b2 = body.replace("; @@ASSUME@@",
                                  assume_block(body, cset, self_sym=f, addrs=addrs)
                                  + "\n" + iv_assume(f)) \
                         .replace("; @@GOAL@@", "")
                if f in IV_INVARIANTS:
                    # the IV is assumed at the header, so it must be PRESERVED at
                    # the recursive occurrence, or assuming it is assuming the
                    # conclusion
                    iv = IV_INVARIANTS[f][0]
                    for m in re.finditer(re.escape(f) + r"_ih\s+([A-Za-z][A-Za-z0-9_]*)\)", body):
                        arg = m.group(1)
                        # UNDER the back-edge guard.  The step is `a6+1 < a5`, and
                        # what rules out `a6+1 = a5` is precisely the `bne` that
                        # takes the back edge; without it the invariant is not
                        # inductive and should not be.
                        bg = guard_of(body, f + "_ih", arg)
                        # sliced, like the discharge: per-byte instantiation makes
                        # the assume block large, and the step only needs the
                        # chain feeding the back-edge state
                        slb = slice_to(body, arg, extra=(bg,))
                        wrb = wsets.get(f, [])
                        ab = (assume_block(slb, cset, self_sym=f,
                                            addrs=dedup_addrs(wrb), byteexp=False)
                              + "\n" + assume_block(slb, cset, self_sym=f,
                                            addrs=dedup_addrs(wrb, reads_only=True),
                                            byteexp=True, decl=False))
                        q = (slb.replace("; @@ASSUME@@", ab + "\n" + iv_assume(f))
                                .replace("; @@GOAL@@", "")
                             + "\n(assert (INV S0))\n"
                             + (f"(assert {bg})\n" if bg else "")
                             + "(assert (not " + iv.format(S=arg) + "))\n(check-sat)\n")
                        if z3(q, timeout) != "unsat":
                            return (f, c, "IV-NOT-INDUCTIVE@" + arg)
                cond = ("(assert (INV S0))\n" + OUTSIDE if c == "stack_or_arena" else
                        "(assert (INV S0))\n"
                        f"(assert (bvuge QA (select (rr S0) {_SP})))\n"
                        "(assert (or (bvult QA A_lo) (bvuge QA A_hi)))\n")
                v = footprint_check(b2, cond, wsets.get(f, []), applied_of(body),
                                    cset, timeout, clause=c,
                                    side=(c == "stack_or_arena"))
                return (f, c, "unsat" if v.startswith("VALID") else
                              "sat" if v == "REFUTED" else v)
            # assume ONLY the summaries this obligation's body actually applies —
            # dumping every summary's clause set into every query buries the
            # solver in quantifiers that can never fire.
            txt = body.replace("; @@ASSUME@@", assume_block(body, cset, self_sym=f)) \
                      .replace("; @@GOAL@@", NEG[c]) + "\n(check-sat)\n"
            return (f, c, z3(txt, timeout))
        # Print each task AS IT LANDS.  The summary at the end is no use while
        # a run is in flight: three multi-hour campaigns were waited out blind
        # because nothing is emitted until all 260 tasks finish.
        done_n = [0]
        prog_lock = threading.Lock()
        t_start = time.time()

        def run_logged(t):
            r = run(t)
            with prog_lock:
                done_n[0] += 1
                print(f"  [{done_n[0]:3d}/{len(tasks)}] {r[0]}.{r[1]} = {r[2]}"
                      f"  ({time.time()-t_start:.0f}s)", flush=True)
            return r

        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
            res = list(ex.map(run_logged, tasks))
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
    # Iterating on an ENCODER defect does not need the whole campaign.  Every
    # defect found so far was diagnosed on one summary or one residual; the full
    # pass is for producing the committed artefact, not for the fix loop.
    only, only_sum, warm = None, None, False
    a = sys.argv[2:]
    for i, x in enumerate(a):
        if x == "--timeout": timeout = int(a[i + 1])
        elif x.startswith("-j"): jobs = int(x[2:])
        elif x == "--rounds": rounds = int(a[i + 1])
        elif x == "--phase": phase = a[i + 1]
        elif x == "--ks": ks = [int(z) for z in a[i + 1].split(",")]
        elif x == "--only": only = set(a[i + 1].split(","))
        elif x == "--only-summary": only_sum = set(a[i + 1].split(","))
        elif x == "--warm": warm = True

    if phase == "bounded":
        print(f"== bounded refutation search (k ladder {ks})")
        bounded(d, timeout, jobs, ks)
        return

    check_provenance(d)
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
        if only_sum:
            syms = [f for f in syms if f in only_sum]
        cset, fix, reasons = mine(d, syms, timeout, jobs, rounds, warm=warm)
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
        spans = {}
        sp_path = os.path.join(d, "spans.tsv")
        if os.path.exists(sp_path):
            rdr = list(csv.DictReader(open(sp_path), delimiter="\t"))
            spans = {r["field"]: r for r in rdr}
        frag_cache = {}

        def is_fragment(f):
            """Does this span start somewhere other than its function's entry?

            `spans.tsv` carries both, so this needs no extra solving, and it is
            deliberately spans.tsv ONLY -- never a fact another post computes.
            The posts run in parallel, so marking a span from the sp verdict
            made the storerepr/valuerepr_tag answers depend on which finished
            first.  hInitStore, which starts at its entry but stops at the
            interpreter's loop head, is therefore checked for real rather than
            skipped, which is the better answer anyway: its storerepr is VALID.
            The old sp
            check below catches the other shape -- a span that starts at the
            entry but stops before the epilogue (hInitStore, which ends at the
            interpreter's loop head) -- via the delta the sp post already
            computed."""
            if f in frag_cache:
                return frag_cache[f]
            r = spans.get(f)
            v = bool(r) and r.get("entry") != r.get("region_lo")
            frag_cache[f] = v
            return v

        vac_cache = {}
        vac_lock = threading.Lock()

        def consistency(f, head, timeout):
            """Are this query's assumptions satisfiable?

            `unsat` means they contradict each other and every post is proved
            trivially.  `sat` is what makes a VALID mean anything.  `unknown` is
            neither, and is carried into the verdict rather than hidden: a
            VALID over assumptions nobody has shown to be consistent is exactly
            the shape of the 26 vacuous fields.

            Checked ONCE per field and memoised -- it is the same question for
            all five posts."""
            with vac_lock:
                if f in vac_cache:
                    return vac_cache[f]
            # Capped independently of the post budget.  A consistency check
            # that has not resolved in a minute is not going to, and the
            # verdict is tagged `consistency-unproved` either way -- so
            # spending the full per-post timeout on it just delays every
            # other task behind it.
            v = z3(head.replace("; @@POST@@", "") + "\n(check-sat)\n",
                   min(timeout, 60))
            with vac_lock:
                vac_cache[f] = v
            return v

        def in_eval(f):
            """Is this span inside `eval_expr`, the one function that boxes a
            `Value` at the caller's a0?  `EVAL_REGION` is its entry, the same
            address `armDispatch` repoints the eval arms to."""
            r = spans.get(f)
            return bool(r) and r.get("region_lo") == EVAL_REGION
        wsets = {f: load_writes(os.path.join(d, "writes", f + ".tsv")) for f in deps}
        pre = pre_block(d)
        tasks = [(f, pk) for f in sorted(deps) if not only or f in only
                 for pk in list(POSTS) + list(FOOTPRINT_POSTS)]
        def run(t):
            f, pk = t
            # The encoder records whether the BMC frontier EMPTIED within the
            # round bound.  If it did not, the reflected term covers only part of
            # the span and a post proved over it says nothing about the rest.
            # The column was emitted and never read.
            if spans.get(f, {}).get("complete") == "false":
                return (f, pk, "INCOMPLETE(frontier-not-empty)")
            # VACUITY GATE, before EITHER route.  `unsat` of PRE + clauses + exit
            # guard, with no post at all, means the assumptions contradict each
            # other -- and a query with contradictory assumptions proves EVERY
            # post.  Reporting that as VALID is the worst failure this driver can
            # have, because it is indistinguishable from a real result: 26 of 52
            # queries were in exactly this state (an over-eager dispatch pin
            # negating a nested dispatch's arms, and two spans whose declared
            # exit is unreachable) and all 26 reported VALID on all five posts.
            vhead = qs[f].replace("; @@ASSUME@@",
                                  pre + "\n" + assume_block(qs[f], cset))
            vac = consistency(f, vhead, timeout)
            if vac == "unsat":
                return (f, pk, "VACUOUS(assumptions-inconsistent)")
            if pk in FOOTPRINT_POSTS:
                # slice to what the footprint actually reads: the store guards and
                # addresses.  A function-entry span carries ~150 summaries and its
                # whole exit merge, none of which a footprint check looks at.
                wr = wsets.get(f, [])
                roots = sorted(write_roots(wr))
                sl = qs[f]
                for r in roots[:1]:
                    sl = slice_to(qs[f], r, extra=roots[1:])
                base = sl.replace("; @@ASSUME@@", assume_block(sl, cset)) \
                         .replace("; @@POST@@", "")
                bad = iv_discharge(qs[f], cset, timeout, pre, wr)
                if bad:
                    return (f, pk, "UNKNOWN(iv-undischarged:" + bad + ")")
                fv = footprint_check(base, FOOTPRINT_POSTS[pk], wr,
                                     applied_of(sl), cset, timeout, pre=pre)
                if fv.startswith("VALID") and vac != "sat":
                    fv += "(consistency-unproved)"
                return (f, pk, fv)
            head = vhead
            # `storerepr` and `valuerepr_tag` are stated over the pointer the
            # CALLER passed in a0 at the span's entry.  That is only the result
            # buffer for a span entered at its function's entry: a FRAGMENT
            # starts mid-arm, where a0 holds whatever the code is using it for.
            # On hFn -- the shared closure-allocation tail -- a0 at entry is 16,
            # the malloc size, so the post reads four bytes at address 16 and is
            # duly "refuted".  That is the post mis-fired, not a defect, and
            # reporting it as REFUTED sends the reader after a bug that is not
            # there.  A fragment is a span that does not start at its function's
            # entry, or one whose sp does not come back to its entry value.
            if pk in ("storerepr", "valuerepr_tag") and is_fragment(f):
                return (f, pk, "N/A(fragment)")
            # `valuerepr_tag` says the four bytes at the pointer the caller
            # passed in a0 are a `ValueKind`.  Only `eval_expr` boxes a Value
            # there.  `exec_stmt` returns a status and `interp_run` takes the
            # PROGRAM in a0, so on those spans the post reads four unrelated
            # bytes and "refutes" -- hInitStore is refuted exactly this way.
            if pk == "valuerepr_tag" and not in_eval(f):
                return (f, pk, "N/A(not-an-eval-arm)")
            txt = head.replace("; @@POST@@", POSTS[pk]) + "\n(check-sat)\n"
            v = z3(txt, timeout)
            if v == "sat" and pk == "sp":
                # A span that does not start at its function's entry begins
                # AFTER the prologue lowered sp, so "sp is restored to its
                # entry value" is the wrong statement for it -- the epilogue
                # raises sp by the frame and the span legitimately ends one
                # frame HIGHER.  Report what it does establish: read the delta
                # off the countermodel, then PROVE sp_exit = sp_entry + delta.
                # (hFn and hEpilogueSpill, delta = 0x440 = eval_expr's frame,
                # both unsat.)  A span that really loses sp fails this too and
                # is still reported REFUTED.
                delta = sp_delta(head, timeout)
                if delta is not None:
                    shifted = ("(assert (not (= (select (rr state_exit) "
                               "#x0000000000000002) (bvadd (select (rr s0) "
                               f"#x0000000000000002) #x{delta:016x}))))")
                    if z3(head.replace("; @@POST@@", shifted) + "\n(check-sat)\n",
                          timeout) == "unsat":
                        return (f, pk, f"VALID[sp+0x{delta:x}]")
            ok = {"unsat": "VALID", "sat": "REFUTED"}.get(v, "UNKNOWN")
            if ok == "VALID" and vac != "sat":
                ok = "VALID(consistency-unproved)"
            return (f, pk, ok)

        # Print each residual verdict AS IT LANDS.  The progress wrapper added
        # earlier attached to the MINING executor only, so phase 1 printed 275
        # lines while phase 2 ran silently for over an hour and looked wedged --
        # it was not, it just had nothing to say.  Both phases now report.
        p2_done = [0]
        p2_lock = threading.Lock()
        p2_t0 = time.time()

        def run_p2(t):
            r = run(t)
            with p2_lock:
                p2_done[0] += 1
                print(f"  [{p2_done[0]:3d}/{len(tasks)}] {r[0]}.{r[1]} = {r[2]}"
                      f"  ({time.time()-p2_t0:.0f}s)", flush=True)
            return r

        with concurrent.futures.ThreadPoolExecutor(max_workers=jobs) as ex:
            res = list(ex.map(run_p2, tasks))
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
