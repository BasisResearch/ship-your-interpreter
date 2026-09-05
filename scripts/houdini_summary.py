#!/usr/bin/env python3
"""houdini_summary.py — mine summary clauses, then check machine projections.

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
     [--rounds N] [--phase mine|check|both|projections]
     [--only FIELD,...] [--only-post POST,...] [--verdict-out PATH]
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
    ("output_restore", guard("(and (= (ol ({f} {S})) (ol {S})) "
                             "(= (oo ({f} {S})) (oo {S})))")),
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
    "output_restore": _G + "(assert (not (and (= (ol fbody) (ol S0)) "
                                  "(= (oo fbody) (oo S0)))))",
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
LOOP_INVALID_CLAUSES = {"ra_restore", "s0_restore", "s1_restore", "above_sp"}


def sanitize_clause_set(cset):
    """Remove ABI-callee clauses that are not predicates of intra-function loops."""
    for sym, clauses in cset.items():
        if sym.startswith("loop_"):
            cset[sym] = [c for c in clauses if c not in LOOP_INVALID_CLAUSES]
    return cset


def verdict_output_path(directory, only, only_post, explicit=None):
    """Keep scoped validation from clobbering full-campaign evidence."""
    if explicit:
        return explicit
    if not only and not only_post:
        return os.path.join(directory, "verdicts.tsv")
    parts = sorted(only or {"all"})
    if only_post:
        parts.extend(sorted(only_post))
    scope = "-".join(re.sub(r"[^A-Za-z0-9_.-]+", "_", part)
                     for part in parts)
    return os.path.join(directory, f"verdicts-{scope}.tsv")

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

# These instances have a summary-free selected route after their residual
# premises are asserted.  Checking memory equality directly lets Z3 discard
# dead reflected branches instead of requiring footprint clauses for summaries
# that occur only on those branches.
DIRECT_MEMORY_FOOTPRINT_FIELDS = {"hArgsNil"}

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

# These posts are discharged only by exact Lean-emitted certificate rows. They
# never enter an SMT query. Extending this registry requires a typed certificate
# in ReflectResiduals.lean; arbitrary campaign text is rejected.
LEAN_POST_CERTIFICATES = {
    ("hCallAssertOk", "abi_frame_x1"):
        "Vsa.Sim.nativeAssertInternalAbi_closed",
    ("hCallAssertOk", "abi_frame_x8"):
        "Vsa.Sim.nativeAssertInternalAbi_closed",
    ("hCallAssertOk", "abi_frame_x9"):
        "Vsa.Sim.nativeAssertInternalAbi_closed",
    ("hCallAssertOk", "abi_frame_x18"):
        "Vsa.Sim.nativeAssertInternalAbi_closed",
}
LEAN_POSTS = tuple(sorted({post for _, post in LEAN_POST_CERTIFICATES}))


def validate_lean_certificate_rows(rows):
    """Validate exact Lean-emitted certificate identities."""
    found = {}
    for row in rows:
        key = (row.get("residual", ""), row.get("post", ""))
        theorem = row.get("theorem", "")
        if key in found:
            raise ValueError(f"duplicate Lean certificate: {key[0]}.{key[1]}")
        if key not in LEAN_POST_CERTIFICATES:
            raise ValueError(f"unknown Lean certificate column: {key[0]}.{key[1]}")
        expected = LEAN_POST_CERTIFICATES[key]
        if theorem != expected:
            raise ValueError(
                f"wrong Lean certificate for {key[0]}.{key[1]}: "
                f"expected {expected}, got {theorem}")
        found[key] = theorem
    missing = set(LEAN_POST_CERTIFICATES) - set(found)
    if missing:
        names = ", ".join(f"{field}.{post}" for field, post in sorted(missing))
        raise ValueError(f"missing Lean certificates: {names}")
    return found


def load_lean_certificates(directory):
    path = os.path.join(directory, "lean-certificates.tsv")
    if not os.path.isfile(path):
        sys.exit(f"houdini: campaign manifest is incomplete: missing {path}")
    try:
        with open(path, newline="") as fh:
            return validate_lean_certificate_rows(
                csv.DictReader(fh, delimiter="\t"))
    except ValueError as err:
        raise SystemExit(
            f"houdini: malformed Lean certificate manifest: {err}") from err


def label_projection_verdict(post, verdict):
    """Attach solver provenance without relabelling Lean certificates."""
    if verdict.startswith("VALID[Lean:"):
        return verdict
    if not verdict.startswith("VALID"):
        return verdict
    label = "VALID-PROJECTION" if post == "residual_relation" else "VALID-MACHINE"
    return label + verdict[len("VALID"):]


def require_helper_trace_consistency(residual, verdict):
    """Require a real trace witness for the mixed helper projection."""
    if residual != "hCallAssertOk" or not verdict.startswith("VALID"):
        return verdict
    if "trace-pinned-consistency" in verdict:
        return verdict
    return "UNKNOWN(trace-pinned-consistency-required)"


def native_assert_machine_post():
    """The five SMT-proved native_assert observables; ABI frame is excluded."""
    sret = "(select (rr s0) #x000000000000000a)"
    clauses = [
        f"(= (ld4 (mm state_exit) {sret}) #x0000000000000000)",
        (f"(= (ld8 (mm state_exit) (bvadd {sret} "
         "#x0000000000000008)) #x0000000000000000)"),
        "(= (select (rr state_exit) #x0000000000000002) "
        "(select (rr s0) #x0000000000000002))",
        "(= (oo state_exit) (oo s0))",
        "(= (ol state_exit) (ol s0))",
    ]
    return "(assert (not (and " + " ".join(clauses) + ")))"


def _summary_input(campaign_dir, field, checkpoint_state, symbol):
    """Recover the unique call input feeding a checkpoint result state."""
    query_path = os.path.join(campaign_dir, "queries", field + ".smt2")
    if not checkpoint_state or not os.path.exists(query_path):
        return None
    text = open(query_path).read()
    aliases = dict(re.findall(
        r"^\(assert \(= ([A-Za-z][A-Za-z0-9_]*) "
        r"([A-Za-z][A-Za-z0-9_]*)\)\)$", text, re.MULTILINE))
    apps = {result: (callee, argument) for result, callee, argument in
            re.findall(
                r"^\(assert \(= ([A-Za-z][A-Za-z0-9_]*) "
                r"\((callee_\d+) ([A-Za-z][A-Za-z0-9_]*)\)\)\)$",
                text, re.MULTILINE)}
    state, seen = checkpoint_state, set()
    while state not in seen:
        seen.add(state)
        app = apps.get(state)
        if app is not None:
            return app[1] if app[0] == symbol else None
        if state not in aliases:
            return None
        state = aliases[state]
    return None


def residual_posts(campaign_dir):
    """Machine-level semantic projections keyed by the Lean residual field.

    These are obligations, never assumptions.  They check the concrete result
    component of a residual.  They do not encode its quantified simulation
    proposition in full.
    """
    path = os.path.join(campaign_dir, "residual-extensions.tsv")
    if not os.path.exists(path):
        return {}
    points = {}
    with open(path, newline="") as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            points.setdefault((row.get("query", row["field"]), row["point"]),
                              row["state"])

    def load(state, off, width=8):
        return (f"(ld{width} (mm {state}) (bvadd "
                f"(select (rr {state}) {_SP}) #x{off:016x}))")

    def truthy(state, off):
        kind = load(state, off, 4)
        bool_value = load(state, off + 8, 4)
        int_value = load(state, off + 8)
        return (f"(or (and (= {kind} #x0000000000000001) "
                f"(not (= {bool_value} #x0000000000000000))) "
                f"(and (= {kind} #x0000000000000002) "
                f"(not (= {int_value} #x0000000000000000))) "
                f"(= {kind} #x0000000000000003) "
                f"(= {kind} #x0000000000000004) "
                f"(= {kind} #x0000000000000005))")

    def value_post(kind, payload=None, payload_width=8):
        target = "(select (rr s0) #x000000000000000a)"
        clauses = [f"(= (ld4 (mm state_exit) {target}) {kind})"]
        if payload is not None:
            clauses.append(
                f"(= (ld{payload_width} (mm state_exit) "
                f"(bvadd {target} #x0000000000000008)) {payload})")
        return "(assert (not (and " + " ".join(clauses) + ")))"

    def status_post(status):
        return ("(assert (not (= (select (rr state_exit) "
                "#x000000000000000a) "
                f"#x{status:016x})))")

    def conjunction_post(clauses):
        return "(assert (not (and " + " ".join(clauses) + ")))"

    def preserved_registers(registers):
        return [
            (f"(= (select (rr state_exit) #x{register:016x}) "
             f"(select (rr s0) #x{register:016x}))")
            for register in registers
        ]

    def value_shadow_valid(state, address):
        """Concrete QF projection of ValueRepr; pointers are opaque IDs."""
        mem = f"(mm {state})"
        kind = f"(ld4 {mem} {address})"
        payload = f"(ld8 {mem} (bvadd {address} #x0000000000000008))"
        bool_payload = f"(ld4 {mem} (bvadd {address} #x0000000000000008))"
        aux = f"(ld8 {mem} (bvadd {address} #x0000000000000010))"
        return (
            f"(or (= {kind} #x0000000000000000) "
            f"(and (= {kind} #x0000000000000001) "
            f"(bvule {bool_payload} #x0000000000000001)) "
            f"(= {kind} #x0000000000000002) "
            f"(and (= {kind} #x0000000000000003) "
            f"(not (= {payload} #x0000000000000000))) "
            f"(and (= {kind} #x0000000000000004) "
            f"(not (= {payload} #x0000000000000000))) "
            f"(and (= {kind} #x0000000000000005) "
            f"(not (= {payload} #x0000000000000000)) "
            f"(not (= {aux} #x0000000000000000))))")

    def arg_vector_shadow_valid(state):
        count = f"(select (rr {state}) #x000000000000000f)"
        sp = f"(select (rr {state}) #x0000000000000002)"
        slots = []
        for index in range(32):
            idx = f"#x{index:016x}"
            address = (f"(bvadd (bvadd {sp} #x00000000000000f0) "
                       f"(bvmul {idx} #x0000000000000018))")
            slots.append(
                f"(=> (bvult {idx} {count}) "
                f"{value_shadow_valid(state, address)})")
        return "(and " + " ".join(slots) + ")"

    def store_bytes(mem, address, value, width):
        """Little-endian byte stores, matching ReflectSpan.storeBytes."""
        result = mem
        for byte in range(width):
            result = (f"(store {result} (bvadd {address} #x{byte:016x}) "
                      f"((_ extract {8 * byte + 7} {8 * byte}) {value}))")
        return result

    def print_post(newline):
        mem = "(mm s0)"
        args = "(select (rr s0) #x000000000000000d)"
        argc = "(select (rr s0) #x000000000000000c)"
        out0, len0 = "(oo s0)", "(ol s0)"
        rendered_len = f"(lean_print_args_len {mem} {args} {argc})"
        rendered_out = (
            f"(lean_print_args_out {mem} {args} {argc} {out0} {len0})")
        final_len = f"(bvadd {len0} {rendered_len})"
        if newline:
            rendered_out = f"(store {rendered_out} {final_len} #x0a)"
            final_len = f"(bvadd {final_len} #x0000000000000001)"
        sret = "(select (rr s0) #x000000000000000a)"
        clauses = [
            f"(= (oo state_exit) {rendered_out})",
            f"(= (ol state_exit) {final_len})",
            f"(= (ld4 (mm state_exit) {sret}) #x0000000000000000)",
            (f"(= (ld8 (mm state_exit) (bvadd {sret} "
             "#x0000000000000008)) #x0000000000000000)"),
        ]
        return "(assert (not (and " + " ".join(clauses) + ")))"

    expr = "(select (rr s0) #x000000000000000c)"
    expr4 = f"(ld4 (mm s0) (bvadd {expr} #x0000000000000008))"
    expr8 = f"(ld8 (mm s0) (bvadd {expr} #x0000000000000008))"
    out = {
        "hArgsNil": (
            "(assert (not (and "
            "(= (select (rr state_exit) #x000000000000000f) #x0000000000000000) "
            "(= (select (rr state_exit) #x0000000000000010) #x0000000000000000))))"),
        "hInt": value_post("#x0000000000000002", expr8),
        "hStr": value_post("#x0000000000000003", expr8),
        "hBool": value_post(
            "#x0000000000000001",
            f"(ite (= {expr4} #x0000000000000000) "
            "#x0000000000000000 #x0000000000000001)", 4),
        "hNull": value_post("#x0000000000000000", "#x0000000000000000"),
        # These are deliberately status-only projections.  The trace model can
        # independently observe a0.  It does not decode StoreRepr or OutRepr.
        # They correspond to constructors whose result status is fixed.  The
        # remaining statement constructors (ifTrue/ifFalse/block/forStart)
        # return a recursive child's status, so a sound projection for them
        # first needs that child ExecIH contract represented in SMT.
        "hSExpr": status_post(0),
        "hSRet": status_post(3),
        "hSRetNull": status_post(3),
        "hSVarInit": status_post(0),
        "hSVarNull": status_post(0),
        "hSIfNone": status_post(0),
        "hSWhileFalse": status_post(0),
        "hSBrk": status_post(1),
        "hSCont": status_post(2),
        "hCallAssertOk": native_assert_machine_post(),
        "hCallPrint": print_post(False),
        "hCallPrintln": print_post(True),
    }

    # `hArgsCons` is intentionally a machine projection, not an encoding of
    # EvalE/EvalArgs or ArgVecRepr.  The finite prefix exposes the first child
    # call and its return.  Relate those observable states to the slot that the
    # loop leaves behind, and record only the final counter fact.  Later child
    # calls remain opaque behind the loop summary.
    args_pre = points.get(("hArgsCons", "0x80003220"))
    args_ret = points.get(("hArgsCons", "0x80003224"))
    if args_pre and args_ret:
        sp = "(select (rr s0) #x0000000000000002)"
        index = "(select (rr s0) #x0000000000000010)"
        argc = "(select (rr s0) #x000000000000000f)"
        call = "(select (rr s0) #x0000000000000008)"
        env = "(select (rr s0) #x000000000000000d)"
        args_base = f"(ld8 (mm s0) (bvadd {call} #x0000000000000010))"
        arg = f"(ld8 (mm s0) (bvadd {args_base} (bvmul {index} #x0000000000000008)))"
        destination = (
            f"(bvadd (bvadd {sp} #x00000000000000f0) "
            f"(bvmul {index} #x0000000000000018))")
        source = f"(bvadd {sp} #x0000000000000040)"
        clauses = [
            f"(= (select (rr {args_pre}) #x0000000000000002) {sp})",
            (f"(= (select (rr {args_pre}) #x000000000000000a) "
             f"{source})"),
            (f"(= (select (rr {args_pre}) #x000000000000000b) "
             "(select (rr s0) #x0000000000000012))"),
            f"(= (select (rr {args_pre}) #x000000000000000c) {arg})",
            f"(= (select (rr {args_pre}) #x000000000000000d) {env})",
            (f"(= (select (rr state_exit) #x0000000000000010) "
             f"{argc})"),
        ]
        for offset in (0, 8, 16):
            off = f"#x{offset:016x}"
            clauses.append(
                f"(= (ld8 (mm state_exit) (bvadd {destination} {off})) "
                f"(ld8 (mm {args_ret}) (bvadd {source} {off})))")
        out["hArgsCons"] = (
            "(assert (not (and " + " ".join(clauses) + ")))")

    # The whole block-arm instance exposes env_new but cuts the sequence loop
    # at 0x800041a4.  Its post validates only the allocation seam.  The helper
    # relation is a named premise backed by env_new_spec and independent trace
    # checks; the Store.allocFrame ghost map remains outside this projection.
    env_pre = points.get(("hSBlock", "0x80004190"))
    env_ret = points.get(("hSBlock", "0x80004194"))
    env_setup = points.get(("hSBlock", "0x800041a0"))
    if env_pre and env_ret and env_setup:
        parent = "(select (rr s0) #x000000000000000c)"
        inner = f"(select (rr {env_ret}) #x000000000000000a)"
        clauses = [
            (f"(= (select (rr {env_pre}) #x000000000000000a) "
             f"{parent})"),
            f"(lean_env_new_frame (mm {env_ret}) {inner} {parent})",
            f"(= (oo {env_ret}) (oo {env_pre}))",
            f"(= (ol {env_ret}) (ol {env_pre}))",
            (f"(= (select (rr {env_setup}) #x0000000000000013) "
             f"{inner})"),
            (f"(= (select (rr {env_setup}) #x0000000000000010) "
             "#x0000000000000000)"),
            (f"(= (select (rr {env_setup}) #x0000000000000008) "
             "(select (rr s0) #x000000000000000b))"),
            (f"(= (select (rr {env_setup}) #x0000000000000009) "
             "(select (rr s0) #x000000000000000a))"),
            (f"(= (select (rr {env_setup}) #x0000000000000012) "
             "(select (rr s0) #x000000000000000d))"),
            f"(= (oo {env_setup}) (oo {env_ret}))",
            f"(= (ol {env_setup}) (ol {env_ret}))",
        ]
        out["hSBlock"] = (
            "(assert (not (and " + " ".join(clauses) + ")))" )

    # The iteration instance stops at the first recursive child's return.  It
    # validates call setup for every first iteration, independent of status.
    child_pre = points.get(("hSBlockIter", "0x800041c4"))
    child_ret = points.get(("hSBlockIter", "0x800041c8"))
    if child_pre and child_ret:
        index = "(select (rr s0) #x0000000000000010)"
        node = "(select (rr s0) #x0000000000000008)"
        stmts = f"(ld8 (mm s0) (bvadd {node} #x0000000000000008))"
        stmt = f"(ld8 (mm s0) (bvadd {stmts} (bvmul {index} #x0000000000000008)))"
        clauses = [
            (f"(= (select (rr {child_pre}) #x0000000000000002) "
             "(select (rr s0) #x0000000000000002))"),
            (f"(= (select (rr {child_pre}) #x000000000000000a) "
             "(select (rr s0) #x0000000000000009))"),
            f"(= (select (rr {child_pre}) #x000000000000000b) {stmt})",
            (f"(= (select (rr {child_pre}) #x000000000000000c) "
             "(select (rr s0) #x0000000000000013))"),
            (f"(= (select (rr {child_pre}) #x000000000000000d) "
             "(select (rr s0) #x0000000000000012))"),
        ]
        out["hSBlockIter"] = (
            "(assert (not (and " + " ".join(clauses) + ")))" )

    # These one-instruction suffixes make the child-status routing explicit.
    # Both are load/store free: the machine state, memory, and output stream
    # are transported unchanged from the child return to the selected target.
    status0 = "(select (rr s0) #x000000000000000a)"
    final_status = "(select (rr state_exit) #x000000000000000a)"
    route_clauses = [
        f"(= {final_status} {status0})",
        "(= (mm state_exit) (mm s0))",
        "(= (oo state_exit) (oo s0))",
        "(= (ol state_exit) (ol s0))",
    ]
    out["hSBlockNormal"] = (
        "(assert (not (and " + " ".join(route_clauses) + ")))" )
    out["hSBlockAbrupt"] = (
        "(assert (not (and " + " ".join(route_clauses) + ")))" )

    # The call residual is split at the four strict `CallArmStages`
    # boundaries.  The last two are genuinely zero-step typed bridges; their
    # posts transport the concrete Value/ArgVec shadows and the exact memory
    # and output arrays without pretending to reconstruct semantic ghost maps.
    call_arm = points.get(("hCallCallee", "0x800031b0"))
    call_pre_checkpoint = points.get(("hCallCallee", "0x800031bc"))
    # This checkpoint is the query stop.  Use the canonical exit state in the
    # post rather than its graph-level merge expression; route slicing then
    # need not prove that two syntactic names denote the same state.
    call_pre = "state_exit" if call_pre_checkpoint else None
    if call_arm and call_pre:
        sp_arm = f"(select (rr {call_arm}) #x0000000000000002)"
        expr_arm = f"(select (rr {call_arm}) #x0000000000000008)"
        env_arm = f"(select (rr {call_arm}) #x0000000000000013)"
        clauses = [
            f"(= (select (rr {call_pre}) #x0000000000000002) {sp_arm})",
            (f"(= (select (rr {call_pre}) #x000000000000000a) "
             f"(bvadd {sp_arm} #x0000000000000060))"),
            (f"(= (select (rr {call_pre}) #x000000000000000b) "
             f"(select (rr {call_arm}) #x0000000000000012))"),
            (f"(= (select (rr {call_pre}) #x000000000000000c) "
             f"(ld8 (mm {call_arm}) (bvadd {expr_arm} "
             "#x0000000000000008)))"),
            (f"(= (select (rr {call_pre}) #x000000000000000d) "
             f"{env_arm})"),
            *[
                (f"(= (select (rr {call_pre}) #x{register:016x}) "
                 f"(select (rr {call_arm}) #x{register:016x}))")
                for register in (1, 8, 9, 18, 19, 23)
            ],
            f"(= (mm {call_pre}) {store_bytes(f'(mm {call_arm})', sp_arm, env_arm, 8)})",
            f"(= (oo {call_pre}) (oo {call_arm}))",
            f"(= (ol {call_pre}) (ol {call_arm}))",
        ]
        out["hCallCallee"] = conjunction_post(clauses)

    # `EvalErr.callTooMany`: this slice starts after the callee's recursive
    # `eval_expr` has returned and stops at the concrete `jal runtime_error`.
    # The entry extensions pin a CALL node, 32 < argc < 2^31, and the returned
    # callee Value shadow.  The post checks the exact local route: runtime_error
    # receives `(interp, line, message, 0, 0)`, re-spills `s3..s7`, and produces
    # no output before the error call.  The
    # preceding typed callee IH and the jal-to-ErrHalts tail remain Lean bridges.
    sp0 = "(select (rr s0) #x0000000000000002)"
    expr0 = "(select (rr s0) #x0000000000000008)"
    too_many_mem = "(mm s0)"
    for register, offset in ((19, 1048), (20, 1040), (21, 1032),
                             (22, 1024), (23, 1016)):
        too_many_mem = store_bytes(
            too_many_mem,
            f"(bvadd {sp0} #x{offset:016x})",
            f"(select (rr s0) #x{register:016x})",
            8)
    out["hCallTooMany"] = conjunction_post([
        ("(= (select (rr state_exit) #x000000000000000a) "
         "(select (rr s0) #x0000000000000012))"),
        (f"(= (select (rr state_exit) #x000000000000000b) "
         f"(ld4s (mm s0) (bvadd {expr0} #x0000000000000004)))"),
        "(= (select (rr state_exit) #x000000000000000c) #x0000000080019470)",
        "(= (select (rr state_exit) #x000000000000000d) #x0000000000000000)",
        "(= (select (rr state_exit) #x000000000000000e) #x0000000000000000)",
        *preserved_registers((1, 2, 8, 9, 18, 19, 20, 21, 22, 23)),
        f"(= (mm state_exit) {too_many_mem})",
        "(= (oo state_exit) (oo s0))",
        "(= (ol state_exit) (ol s0))",
        value_shadow_valid("state_exit", f"(bvadd {sp0} #x0000000000000060)"),
    ])

    for query in ("hCallCalleeToArgsNil", "hCallCalleeToArgsCons"):
        count = ("(ld4 (mm s0) (bvadd (select (rr s0) "
                 "#x0000000000000008) #x0000000000000018))")
        sp0 = "(select (rr s0) #x0000000000000002)"
        env0 = f"(ld8 (mm s0) {sp0})"
        callee_addr = f"(bvadd {sp0} #x0000000000000060)"
        clauses = [
            f"(= (select (rr state_exit) #x000000000000000f) {count})",
            "(= (select (rr state_exit) #x0000000000000010) #x0000000000000000)",
            f"(= (select (rr state_exit) #x000000000000000d) {env0})",
            *preserved_registers((1, 2, 8, 9, 10, 11, 12, 18, 19, 23)),
            (f"(= (mm state_exit) {store_bytes('(mm s0)', f'(bvadd {sp0} #x00000000000003f8)', '(select (rr s0) #x0000000000000017)', 8)})"),
            "(= (oo state_exit) (oo s0))",
            "(= (ol state_exit) (ol s0))",
            value_shadow_valid("state_exit", callee_addr),
        ]
        out[query] = conjunction_post(clauses)

    count = "(select (rr s0) #x000000000000000f)"
    sp0 = "(select (rr s0) #x0000000000000002)"
    callee_addr = f"(bvadd {sp0} #x0000000000000060)"
    identity = [
        "(= (rr state_exit) (rr s0))",
        "(= (mm state_exit) (mm s0))",
        "(= (oo state_exit) (oo s0))",
        "(= (ol state_exit) (ol s0))",
    ]
    slot_transport = []
    for index in range(32):
        idx = f"#x{index:016x}"
        address = (f"(bvadd (bvadd {sp0} #x00000000000000f0) "
                   f"(bvmul {idx} #x0000000000000018))")
        for offset in (0, 8, 16):
            off = f"#x{offset:016x}"
            slot_transport.append(
                f"(=> (bvult {idx} {count}) "
                f"(= (ld8 (mm state_exit) (bvadd {address} {off})) "
                f"(ld8 (mm s0) (bvadd {address} {off}))))")
    out["hCallArgsToCall"] = conjunction_post([
        *identity,
        value_shadow_valid("state_exit", callee_addr),
        arg_vector_shadow_valid("state_exit"),
        *slot_transport,
    ])

    result_addr = "(select (rr s0) #x0000000000000009)"
    out["hCallCallToEpilogue"] = conjunction_post([
        *identity,
        value_shadow_valid("state_exit", result_addr),
        *[
            (f"(= (ld8 (mm state_exit) (bvadd {result_addr} "
             f"#x{offset:016x})) (ld8 (mm s0) (bvadd {result_addr} "
             f"#x{offset:016x})))")
            for offset in (0, 8, 16)
        ],
    ])

    # Recursive while constructors are factored at the same machine boundaries
    # as the Lean proof.  Call-setup cuts stop before the recursive call.  The
    # next cut starts at its return PC.  Nothing here assigns a semantic result
    # to eval_expr, exec_stmt, or the recursive while invocation.
    sp = "(select (rr s0) #x0000000000000002)"
    cond = "(ld8 (mm s0) (bvadd (select (rr s0) #x0000000000000008) #x0000000000000008))"
    body = "(ld8 (mm s0) (bvadd (select (rr s0) #x0000000000000008) #x0000000000000010))"
    no_store = [
        "(= (mm state_exit) (mm s0))",
        "(= (oo state_exit) (oo s0))",
        "(= (ol state_exit) (ol s0))",
    ]
    cond_setup = [
        f"(= (select (rr state_exit) #x000000000000000a) (bvadd {sp} #x0000000000000050))",
        "(= (select (rr state_exit) #x000000000000000b) (select (rr s0) #x0000000000000009))",
        f"(= (select (rr state_exit) #x000000000000000c) {cond})",
        "(= (select (rr state_exit) #x000000000000000d) (select (rr s0) #x0000000000000013))",
        *preserved_registers((1, 2, 8, 9, 18, 19)),
        *no_store,
    ]
    cond_truthy = [
        "(= (select (rr state_exit) #x000000000000000a) #x0000000000000001)",
        *(
            f"(= (ld8 (mm state_exit) (bvadd {sp} #x{dst:016x})) "
            f"(ld8 (mm s0) (bvadd {sp} #x{src:016x})))"
            for dst, src in ((16, 80), (24, 88), (32, 96))
        ),
        *preserved_registers((2, 8, 9, 18, 19)),
        "(= (oo state_exit) (oo s0))",
        "(= (ol state_exit) (ol s0))",
    ]
    body_setup = [
        "(= (select (rr state_exit) #x000000000000000a) (select (rr s0) #x0000000000000009))",
        f"(= (select (rr state_exit) #x000000000000000b) {body})",
        "(= (select (rr state_exit) #x000000000000000c) (select (rr s0) #x0000000000000013))",
        "(= (select (rr state_exit) #x000000000000000d) (select (rr s0) #x0000000000000012))",
        *preserved_registers((1, 2, 8, 9, 18, 19)),
        *no_store,
    ]
    route_frame = [
        *preserved_registers((1, 2, 8, 9, 18, 19)),
        *no_store,
    ]
    for field in ("hSWhileBreak", "hSWhileRet", "hSWhileLoop"):
        out[field + "CondSetup"] = conjunction_post(cond_setup)
        out[field + "CondTruthy"] = conjunction_post(cond_truthy)
        out[field + "BodySetup"] = conjunction_post(body_setup)
    for field in ("hSWhileRet", "hSWhileLoop"):
        out[field + "BodyReturn"] = conjunction_post([
            "(= (select (rr state_exit) #x000000000000000a) "
            "(select (rr s0) #x000000000000000a))",
            *route_frame,
        ])
    out["hSWhileBreakRoute"] = conjunction_post([
        "(= (select (rr state_exit) #x000000000000000a) #x0000000000000000)",
        *route_frame,
    ])
    out["hSWhileRetRoute"] = conjunction_post([
        "(= (select (rr state_exit) #x000000000000000a) #x0000000000000003)",
        *route_frame,
    ])
    out["hSWhileLoopRoute"] = conjunction_post([
        "(= (select (rr state_exit) #x000000000000000a) "
        "(select (rr s0) #x000000000000000a))",
        *route_frame,
    ])

    # The var/assign spans stop at the shared value-return tail.  Their
    # projections therefore state the exact successful helper boundary, not a
    # fabricated full EvalE/StoreRepr post.  `_summary_input` follows the
    # emitted state aliases back from the link-return checkpoint to the unique
    # helper application that produced it.
    var_ret = points.get(("hVar", "0x80003444"))
    if var_ret:
        call_pre = _summary_input(
            campaign_dir, "hVar", var_ret, "callee_2147494928")
        if call_pre:
            mem = f"(mm {call_pre})"
            env = f"(select (rr {call_pre}) #x000000000000000a)"
            name = f"(select (rr {call_pre}) #x000000000000000b)"
            destination = f"(select (rr {call_pre}) #x000000000000000c)"
            slot = f"(lean_env_lookup_slot {mem} {env} {name})"
            clauses = [
                "(= (select (rr state_exit) #x000000000000000a) "
                "#x0000000000000001)",
                f"(= (oo state_exit) (oo {call_pre}))",
                f"(= (ol state_exit) (ol {call_pre}))",
            ]
            for offset in (0, 8, 16):
                off = f"#x{offset:016x}"
                clauses.append(
                    f"(= (ld8 (mm state_exit) (bvadd {destination} {off})) "
                    f"(ld8 {mem} (bvadd {slot} {off})))")
            out["hVar"] = "(assert (not (and " + " ".join(clauses) + ")))"

    assign_ret = points.get(("hAssign", "0x800034b4"))
    if assign_ret:
        call_pre = _summary_input(
            campaign_dir, "hAssign", assign_ret, "callee_2147495132")
        if call_pre:
            mem = f"(mm {call_pre})"
            env = f"(select (rr {call_pre}) #x000000000000000a)"
            name = f"(select (rr {call_pre}) #x000000000000000b)"
            value = f"(select (rr {call_pre}) #x000000000000000c)"
            slot = f"(lean_env_lookup_slot {mem} {env} {name})"
            clauses = [
                "(= (select (rr state_exit) #x000000000000000a) "
                "#x0000000000000001)",
                f"(= (oo state_exit) (oo {call_pre}))",
                f"(= (ol state_exit) (ol {call_pre}))",
            ]
            for offset in (0, 8, 16):
                off = f"#x{offset:016x}"
                clauses.append(
                    f"(= (ld8 (mm state_exit) (bvadd {slot} {off})) "
                    f"(ld8 {mem} (bvadd {value} {off})))")
            out["hAssign"] = "(assert (not (and " + " ".join(clauses) + ")))"

    unary = points.get(("hNeg", "0x800035ec"))
    if unary:
        out["hNeg"] = value_post(
            "#x0000000000000002",
            f"(bvsub #x0000000000000000 {load(unary, 152)})")
    unary = points.get(("hNot", "0x800035ec"))
    if unary:
        out["hNot"] = value_post(
            "#x0000000000000001",
            f"(ite {truthy(unary, 144)} #x0000000000000000 "
            "#x0000000000000001)", 4)

    out["hAndFalse"] = value_post(
        "#x0000000000000001", "#x0000000000000000", 4)
    out["hOrTrue"] = value_post(
        "#x0000000000000001", "#x0000000000000001", 4)
    logical_right = {
        "hAndTrue": ("0x800035b0", 240),
        "hOrFalse": ("0x80003a10", 144),
    }
    for field, (point, offset) in logical_right.items():
        state = points.get((field, point))
        if state:
            out[field] = value_post(
                "#x0000000000000001",
                f"(ite {truthy(state, offset)} #x0000000000000001 "
                "#x0000000000000000)", 4)

    int_ops = {
        "hIAdd": lambda a, b: f"(bvadd {a} {b})",
        "hISub": lambda a, b: f"(bvsub {a} {b})",
        "hIMul": lambda a, b: f"(bvmul {a} {b})",
        "hIDiv": lambda a, b: f"(bvsdiv {a} {b})",
        "hIMod": lambda a, b: f"(bvsrem {a} {b})",
    }
    comparisons = {
        "hILt": "bvslt", "hILe": "bvsle",
        "hIGt": "bvsgt", "hIGe": "bvsge",
    }
    binary_points = {
        field: state
        for (field, point), state in points.items()
        if point == "0x8000351c"
    }
    for field, state in binary_points.items():
        left = f"(ld8 (mm {state}) (bvadd (select (rr {state}) {_SP}) #x0000000000000080))"
        right = f"(ld8 (mm {state}) (bvadd (select (rr {state}) {_SP}) #x0000000000000098))"
        if field in int_ops:
            expected = int_ops[field](left, right)
            out[field] = value_post("#x0000000000000002", expected)
        elif field in comparisons:
            expected = (f"(ite ({comparisons[field]} {left} {right}) "
                        "#x0000000000000001 #x0000000000000000)")
            out[field] = value_post("#x0000000000000001", expected, 4)
        elif field == "hDivOv":
            out[field] = value_post(
                "#x0000000000000002", "#x8000000000000000")

    # Equality is stated against the two represented Values before the helper
    # call.  `assume_block` supplies the helper-to-Lean ground contract at that
    # exact application; the local tail then boxes the related Boolean.
    eq_specs = {
        "hEq": ("0x80003720", False),
        "hNe": ("0x80003770", True),
    }
    for field, (point, negate) in eq_specs.items():
        result_state = points.get((field, point))
        if result_state:
            sp = f"(select (rr {result_state}) {_SP})"
            left = f"(bvadd {sp} #x0000000000000040)"
            right = f"(bvadd {sp} #x0000000000000020)"
            equal = (f"(lean_value_equal (mm {result_state}) "
                     f"{left} {right})")
            expected = (f"(ite (= {equal} #x0000000000000000) "
                        "#x0000000000000001 #x0000000000000000)"
                        if negate else equal)
            out[field] = value_post("#x0000000000000001", expected, 4)

    for field in ("hStrAddL", "hStrAddR"):
        state = points.get((field, "0x80003ac8"))
        if state:
            out[field] = value_post(
                "#x0000000000000003",
                f"(select (rr {state}) #x0000000000000008)")

    cmp_specs = {
        "hStrLt": "bvslt",
        "hStrLe": "bvsle",
        "hStrGt": "bvsgt",
        "hStrGe": "bvsge",
    }
    for field, relation in cmp_specs.items():
        result_state = points.get((field, "0x80003b1c"))
        if result_state:
            left = f"(select (rr {result_state}) #x0000000000000013)"
            right = f"(select (rr {result_state}) #x0000000000000011)"
            result = (f"(lean_cstring_cmp3 (mm {result_state}) "
                      f"{left} {right})")
            expected = (f"(ite ({relation} {result} #x0000000000000000) "
                        "#x0000000000000001 #x0000000000000000)")
            out[field] = value_post("#x0000000000000001", expected, 4)

    fn = points.get(("hFn", "0x800033d0"))
    if fn:
        closure = f"(select (rr {fn}) #x000000000000000a)"
        malloc_pre = _summary_input(
            campaign_dir, "hFn", fn, "callee_2147501968")
        if malloc_pre:
            fn_expr = (f"(select (rr {malloc_pre}) "
                       "#x0000000000000008)")
            env = (f"(select (rr {malloc_pre}) "
                   "#x000000000000000d)")
            target = "(select (rr s0) #x000000000000000a)"
            clauses = [
                f"(= (ld4 (mm state_exit) {target}) #x0000000000000004)",
                (f"(= (ld8 (mm state_exit) (bvadd {target} "
                 f"#x0000000000000008)) {closure})"),
                (f"(lean_malloc16_rel (mm {malloc_pre}) (mm {fn}) "
                 f"{closure})"),
                f"(= (ld8 (mm state_exit) {closure}) {fn_expr})",
                (f"(= (ld8 (mm state_exit) (bvadd {closure} "
                 f"#x0000000000000008)) {env})"),
            ]
            out["hFn"] = (
                "(assert (not (and " + " ".join(clauses) + ")))")
    return out


# These fixed-status projections are proved with every callee/loop summary left
# completely uninterpreted.  Their local tail overwrites a0, so importing frame
# clauses only makes the query slower and its consistency harder to establish;
# omitting them is a strictly stronger check.
SUMMARY_FREE_RESIDUAL_PROJECTIONS = {
    "hArgsNil",
    "hCallCallee", "hCallTooMany", "hCallCalleeToArgsNil", "hCallCalleeToArgsCons",
    "hCallArgsToCall", "hCallCallToEpilogue",
    "hSBlockIter", "hSBlockNormal", "hSBlockAbrupt",
    "hSExpr", "hSRet", "hSRetNull", "hSVarInit", "hSVarNull",
    "hSIfNone", "hSWhileFalse", "hSBrk", "hSCont",
    "hSWhileBreakCondSetup", "hSWhileBreakCondTruthy",
    "hSWhileBreakBodySetup", "hSWhileBreakRoute",
    "hSWhileRetCondSetup", "hSWhileRetCondTruthy",
    "hSWhileRetBodySetup", "hSWhileRetBodyReturn", "hSWhileRetRoute",
    "hSWhileLoopCondSetup", "hSWhileLoopCondTruthy",
    "hSWhileLoopBodySetup", "hSWhileLoopBodyReturn", "hSWhileLoopRoute",
}


def residual_pres(campaign_dir):
    """Machine facts corresponding to semantic premises of projected residuals.

    A successful integer `EvalE.binary` derivation entails that both recursive
    evaluations returned integer Values.  Without these facts the machine query
    also contains the interpreter's type-error exits, which are outside the Lean
    constructor being projected and make the formula both larger and false.
    """
    path = os.path.join(campaign_dir, "residual-extensions.tsv")
    if not os.path.exists(path):
        return {}
    points = {}
    with open(path, newline="") as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            points.setdefault((row.get("query", row["field"]), row["point"]),
                              row["state"])

    def load(state, off, width=8):
        return (f"(ld{width} (mm {state}) (bvadd "
                f"(select (rr {state}) {_SP}) #x{off:016x}))")

    out = {}

    env_ret = points.get(("hSBlock", "0x80004194"))
    if env_ret:
        call_pre = _summary_input(
            campaign_dir, "hSBlock", env_ret, "callee_2147494396")
        if call_pre:
            parent = f"(select (rr {call_pre}) #x000000000000000a)"
            inner = f"(select (rr {env_ret}) #x000000000000000a)"
            # Ground instance of the proved env_new contract.  This is a
            # modular helper premise, not a fact mined from the opaque summary.
            out["hSBlock"] = "\n".join((
                f"(assert (lean_env_new_frame (mm {env_ret}) {inner} {parent}))",
                f"(assert (= (oo {env_ret}) (oo {call_pre})))",
                f"(assert (= (ol {env_ret}) (ol {call_pre})))",
                *(
                    f"(assert (= (select (rr {env_ret}) #x{reg:016x}) "
                    f"(select (rr {call_pre}) #x{reg:016x})))"
                    for reg in (2, 8, 9, 18, 19)
                ),
            ))

    helper_success = {
        "hVar": ("0x80003444", "callee_2147494928"),
        "hAssign": ("0x800034b4", "callee_2147495132"),
    }
    for field, (point, symbol) in helper_success.items():
        link_return = points.get((field, point))
        if not link_return:
            continue
        call_pre = _summary_input(campaign_dir, field, link_return, symbol)
        if not call_pre:
            continue
        mem = f"(mm {call_pre})"
        env = f"(select (rr {call_pre}) #x000000000000000a)"
        name = f"(select (rr {call_pre}) #x000000000000000b)"
        out[field] = (
            f"(assert (lean_env_lookup_found {mem} {env} {name}))")

    int_fields = {
        "hIAdd", "hISub", "hIMul", "hIDiv", "hIMod",
        "hILt", "hILe", "hIGt", "hIGe", "hDivOv",
    }
    for field in int_fields:
        state = points.get((field, "0x8000351c"))
        if not state:
            continue
        clauses = [
            f"(= {load(state, 120, 4)} #x0000000000000002)",
            f"(= {load(state, 144, 4)} #x0000000000000002)",
        ]
        right = load(state, 152)
        if field in ("hIDiv", "hIMod"):
            clauses.append(f"(not (= {right} #x0000000000000000))")
        if field == "hIDiv":
            left = load(state, 128)
            clauses.append(
                f"(not (and (= {left} #x8000000000000000) "
                f"(= {right} #xffffffffffffffff)))")
        if field == "hDivOv":
            left = load(state, 128)
            clauses.extend([
                f"(= {left} #x8000000000000000)",
                f"(= {right} #xffffffffffffffff)",
            ])
        out[field] = "\n".join(f"(assert {clause})" for clause in clauses)

    unary = points.get(("hNeg", "0x800035ec"))
    if unary:
        out["hNeg"] = (
            f"(assert (= {load(unary, 144, 4)} #x0000000000000002))")

    def output_frame_premise(field, symbol):
        """Transport printArgs across unrelated prologue stack stores.

        `lean_print_args_same` denotes agreement only on the represented Values
        and their recursively read display data.  It is not whole-memory
        equality.  The two implications are the exact congruence properties of
        `Value.display`/`printArgs` under that footprint agreement.
        """
        query_path = os.path.join(campaign_dir, "queries", field + ".smt2")
        if not os.path.exists(query_path):
            return None
        query = open(query_path).read()
        matches = re.findall(
            r"\(" + re.escape(symbol) +
            r"(?:_ih)? ([A-Za-z][A-Za-z0-9_]*)\)", query)
        matches = list(dict.fromkeys(matches))
        if len(matches) != 1:
            raise RuntimeError(
                f"{field}: expected one {symbol} application, found {len(matches)}")
        snapshot = matches[0]
        base = "(select (rr s0) #x000000000000000d)"
        count = "(select (rr s0) #x000000000000000c)"
        same = (f"(lean_print_args_same (mm s0) (mm {snapshot}) "
                f"{base} {count})")
        left_len = f"(lean_print_args_len (mm s0) {base} {count})"
        right_len = f"(lean_print_args_len (mm {snapshot}) {base} {count})"
        left_out = (f"(lean_print_args_out (mm s0) {base} {count} "
                    "(oo s0) (ol s0))")
        right_out = (f"(lean_print_args_out (mm {snapshot}) {base} {count} "
                     "(oo s0) (ol s0))")
        zero_len = (f"(lean_print_args_len (mm s0) {base} "
                    "#x0000000000000000)")
        zero_out = (f"(lean_print_args_out (mm s0) {base} "
                    "#x0000000000000000 (oo s0) (ol s0))")
        return "\n".join((
            f"(assert {same})",
            f"(assert (=> {same} (= {left_len} {right_len})))",
            f"(assert (=> {same} (= {left_out} {right_out})))",
            f"(assert (= {zero_len} #x0000000000000000))",
            f"(assert (= {zero_out} (oo s0)))",
        ))

    print_frame = output_frame_premise("hCallPrint", PRINT_LOOP_SUMMARY)
    if print_frame:
        out["hCallPrint"] = print_frame
    println_frame = output_frame_premise("hCallPrintln", NATIVE_PRINT_CALLEE)
    if println_frame:
        out["hCallPrintln"] = println_frame

    def loop_exit_premise(field, header, target):
        """The reflected selector implied by a constructor's branch premise.

        `ifNone` and `whileFalse` fix the semantic condition to false.  In the
        finite machine model that fact is observed as the corresponding loop
        summary reaching its false-condition continuation.  Find the emitted
        guard by the stable machine PCs instead of relying on its generated
        `gNN` name.
        """
        query_path = os.path.join(campaign_dir, "queries", field + ".smt2")
        if not os.path.exists(query_path):
            return None
        query = open(query_path).read()
        symbol = f"loopexit_{header}"
        target_bv = f"#x{target:016x}"
        pattern = re.compile(
            r"^\(assert \(= (g\d+[qx]?) \(and .*\(= \(" +
            re.escape(symbol) + r" \S+\) " + re.escape(target_bv) +
            r"\)\)\)\)$", re.M)
        matches = pattern.findall(query)
        if len(matches) != 1:
            raise RuntimeError(
                f"{field}: expected exactly one loop-exit premise for "
                f"0x{header:x} -> 0x{target:x}, found {len(matches)}")
        return f"(assert {matches[0]})"

    # `ExecS.ifNone` and `ExecS.whileFalse` carry `v.truthy = false`.
    # Their residual bundle does not itself repeat that premise, but the
    # matching recursor constructor does; these are constructor projections.
    for field, header, target in (
            ("hSIfNone", 2147500060, 0x800042d4),
            ("hSWhileFalse", 2147500092, 0x80004090)):
        premise = loop_exit_premise(field, header, target)
        if premise is not None:
            out[field] = premise
    return out


# The integer rows deliberately expose these facts as their per-operation
# ``<Op>Resid`` candidate.  They are not consequences silently added to the
# whole Lean proposition: the specialised check below starts at the
# post-children checkpoint and validates the machine suffix *conditional on*
# this candidate.  Its verdict is therefore tagged ``[candidate-suffix]``.
# These facts require an independent differential-test target at the checkpoint.
_BIN_CARRY = {
    # field: (operator token, jump-table slot address, signed 32-bit slot word)
    "hIAdd": (11, 0x80019f84, 0xfffe9904),
    "hISub": (12, 0x80019f88, 0xfffe995c),
    "hIMul": (13, 0x80019f8c, 0xfffe98b0),
    "hIDiv": (14, 0x80019f90, 0xfffe9858),
    "hIMod": (15, 0x80019f94, 0xfffe9800),
    "hILt":  (20, 0x80019fa8, 0xfffe96a4),
    "hILe":  (21, 0x80019fac, 0xfffe96a4),
    "hIGt":  (22, 0x80019fb0, 0xfffe96a4),
    "hIGe":  (23, 0x80019fb4, 0xfffe96a4),
    "hDivOv": (14, 0x80019f90, 0xfffe9858),
}

def residual_suffixes(campaign_dir):
    """Checkpoint-local validation contexts for recursive arithmetic rows.

    A whole-function query retains both recursive calls and every other arm of
    ``eval_expr``.  That is the wrong granularity for checking the row's
    post-child candidate: the Lean row itself factors at ``TwoSubReturn``.  The
    contexts here mirror that factorisation.  ``semantic_pre`` contains only
    facts supplied by the child derivations; ``candidate_pre`` is exactly the
    carry bundle being validated (``x19``, the respilled left kind, operator
    token, and the selected jump-table word).
    """
    path = os.path.join(campaign_dir, "residual-extensions.tsv")
    if not os.path.exists(path):
        return {}
    points = {}
    with open(path, newline="") as fh:
        for row in csv.DictReader(fh, delimiter="\t"):
            points.setdefault((row["field"], row["point"]),
                              (row["guard"], row["state"]))

    semantic = residual_pres(campaign_dir)
    out = {}
    for field, (token, slot, word) in _BIN_CARRY.items():
        point = points.get((field, "0x8000351c"))
        if not point:
            continue
        guard, state = point
        sp = f"(select (rr {state}) {_SP})"
        mem = f"(mm {state})"
        sret = f"(select (rr {state}) #x0000000000000009)"
        left = (f"(ld8 {mem} (bvadd {sp} #x0000000000000080))")
        semantic_pre = semantic.get(field, "") + "\n" + (
            # EvalEntry.sret_stack_disjoint transported to TwoSubReturn.  The
            # checkpoint sp is the outer sp minus the 1088-byte eval frame.
            f"(assert (or (bvule (bvadd {sret} #x0000000000000018) {sp}) "
            f"(bvule (bvadd {sp} #x0000000000000440) {sret})))\n"
            f"(assert (bvule #x0000000080000000 {sp}))\n"
            f"(assert (bvule {sp} #x00000000fffffbc0))\n"
            f"(assert (bvule #x0000000080000000 {sret}))\n"
            f"(assert (bvule {sret} #x00000000ffffffe8))\n"
            f"(assert (INV {state}))")
        candidate = "\n".join((
            # AddResid.x19 + AddResid.wlbuf (and the corresponding field in
            # every other integer row).
            f"(assert (= (select (rr {state}) #x0000000000000013) {left}))",
            # <Op>Resid.kindresp: the left kind respilled at the bottom of the
            # current 1088-byte frame.
            f"(assert (= (ld8 {mem} {sp}) #x0000000000000002))",
            # <Op>Resid.gx8/opTok and <Op>Resid.slot.
            f"(assert (= (ld4 {mem} (bvadd (select (rr {state}) "
            f"#x0000000000000008) #x0000000000000008)) "
            f"#x{token:016x}))",
            f"(assert (= (ld4 {mem} #x{slot:016x}) #x{word:016x}))",
        ))
        out[field] = {
            "guard": guard,
            "state": state,
            "pre": semantic_pre + "\n" + candidate,
        }
    point = points.get(("hNeg", "0x800035ec"))
    if point:
        guard, state = point
        sp = f"(select (rr {state}) {_SP})"
        sret = f"(select (rr {state}) #x0000000000000009)"
        out["hNeg"] = {
            "guard": guard,
            "state": state,
            # Unlike binary <Op>Resid, the repaired NegResid needs no invented
            # carry: its child EvalIH supplies the represented integer directly.
            "pre": semantic.get("hNeg", "") + "\n" +
            f"(assert (or (bvule (bvadd {sret} #x0000000000000018) {sp}) "
            f"(bvule (bvadd {sp} #x0000000000000440) {sret})))\n"
            f"(assert (bvule #x0000000080000000 {sp}))\n"
            f"(assert (bvule {sp} #x00000000fffffbc0))\n"
            f"(assert (bvule #x0000000080000000 {sret}))\n"
            f"(assert (bvule {sret} #x00000000ffffffe8))\n"
            f"(assert (= (ld4 (mm {state}) (bvadd (select (rr {state}) "
            f"#x0000000000000008) #x0000000000000008)) "
            f"#x000000000000000c))\n"
            f"(assert (INV {state}))",
        }

    def add_suffix(field, pc, assertions, replacements=None):
        point = points.get((field, f"0x{pc:08x}"))
        if not point:
            return
        guard, state = point
        out[field] = {
            "guard": guard,
            "state": state,
            "pre": "\n".join(f"(assert {term(state)})" for term in assertions),
            "post_replacements": {
                old: new(state) for old, new in (replacements or {}).items()
            },
        }

    def reg(n):
        return lambda state: f"(select (rr {state}) #x{n:016x})"

    def load_reg(regno, offset, width=4):
        return lambda state: (
            f"(ld{width} (mm {state}) (bvadd "
            f"(select (rr {state}) #x{regno:016x}) #x{offset:016x}))")

    def truthy_at(state, offset):
        kind = f"(ld4 (mm {state}) (bvadd {reg(2)(state)} #x{offset:016x}))"
        bool_value = f"(ld4 (mm {state}) (bvadd {reg(2)(state)} #x{offset + 8:016x}))"
        int_value = f"(ld8 (mm {state}) (bvadd {reg(2)(state)} #x{offset + 8:016x}))"
        return (f"(or (and (= {kind} #x0000000000000001) "
                f"(not (= {bool_value} #x0000000000000000))) "
                f"(and (= {kind} #x0000000000000002) "
                f"(not (= {int_value} #x0000000000000000))) "
                f"(= {kind} #x0000000000000003) "
                f"(= {kind} #x0000000000000004) "
                f"(= {kind} #x0000000000000005))")

    def falsy_at(state, offset):
        kind = f"(ld4 (mm {state}) (bvadd {reg(2)(state)} #x{offset:016x}))"
        bool_value = f"(ld4 (mm {state}) (bvadd {reg(2)(state)} #x{offset + 8:016x}))"
        int_value = f"(ld8 (mm {state}) (bvadd {reg(2)(state)} #x{offset + 8:016x}))"
        return (f"(or (= {kind} #x0000000000000000) "
                f"(and (= {kind} #x0000000000000001) "
                f"(= {bool_value} #x0000000000000000)) "
                f"(and (= {kind} #x0000000000000002) "
                f"(= {int_value} #x0000000000000000)))")

    def sret_window(state):
        """The row-local `ValueRepr` window for the caller's result slot.

        This is not generic stack folklore.  EvalEntry places the 24-byte sret
        above the 16-byte HTIF window and below 2^32.  Without these facts Z3
        may alias value_bool's stores with tohost, where the machine model
        correctly treats them as MMIO instead of memory writes.
        """
        target = reg(9)(state)
        end = f"(bvadd {target} #x0000000000000018)"
        return [
            f"(bvule #x000000008001ad10 {target})",
            f"(bvule {target} {end})",
            f"(bvule {end} #x0000000100000000)",
        ]

    leaf_replacements = {
        "(mm s0)": lambda state: f"(mm {state})",
        "(select (rr s0) #x000000000000000c)": reg(12),
    }
    for field, pc, kind in (
            ("hInt", 0x80003408, 0), ("hStr", 0x80003414, 1),
            ("hBool", 0x80003420, 2), ("hNull", 0x8000342C, 3)):
        add_suffix(field, pc, [
            lambda state, kind=kind: (
                f"(= {load_reg(12, 0)(state)} #x{kind:016x})"),
            lambda state: f"(= {reg(10)(state)} {reg(9)(state)})",
        ], leaf_replacements)

    add_suffix("hNot", 0x800035EC, [
        lambda state: f"(= {load_reg(8, 8)(state)} #x0000000000000010)",
        lambda state: (
            f"(bvule (ld4 (mm {state}) (bvadd {reg(2)(state)} "
            "#x0000000000000090)) #x0000000000000005)"),
    ])
    for field, token, truth in (
            ("hAndFalse", 24, False), ("hOrTrue", 25, True)):
        pred = (lambda state, truth=truth:
                truthy_at(state, 120) if truth else falsy_at(state, 120))
        add_suffix(field, 0x8000356C, [
            lambda state, token=token: (
                f"(= {load_reg(8, 8)(state)} #x{token:016x})"), pred,
        ])

    for field, pc, token, offset in (
            ("hAndTrue", 0x800035B0, 24, 240),
            ("hOrFalse", 0x80003A10, 25, 144)):
        add_suffix(field, pc, [
            lambda state, token=token: (
                f"(= {load_reg(8, 8)(state)} #x{token:016x})"),
            lambda state, offset=offset: (
                f"(bvule (ld4 (mm {state}) (bvadd {reg(2)(state)} "
                f"#x{offset:016x})) #x0000000000000005)"),
            (lambda state: truthy_at(state, 120)) if field == "hAndTrue"
            else (lambda state: falsy_at(state, 120)),
        ])

    for field, pc, token in (
            ("hEq", 0x80003720, 19), ("hNe", 0x80003770, 17)):
        assertions = [
            lambda state: (
                f"(bvule (ld4 (mm {state}) (bvadd {reg(2)(state)} "
                "#x0000000000000040)) #x0000000000000005)"),
            lambda state: (
                f"(bvule (ld4 (mm {state}) (bvadd {reg(2)(state)} "
                "#x0000000000000020)) #x0000000000000005)"),
            lambda state: (
                f"(= {reg(10)(state)} (lean_value_equal (mm {state}) "
                f"(bvadd {reg(2)(state)} #x0000000000000040) "
                f"(bvadd {reg(2)(state)} #x0000000000000020)))"),
        ]
        assertions.extend(
            (lambda state, index=index: sret_window(state)[index])
            for index in range(3))
        add_suffix(field, pc, assertions)

    for field, token in (
            ("hStrLt", 20), ("hStrLe", 21),
            ("hStrGt", 22), ("hStrGe", 23)):
        assertions = [
            lambda state, token=token: (
                f"(= (ld4 (mm {state}) {reg(2)(state)}) #x{token:016x})"),
            lambda state: (
                f"(= (ld4 (mm {state}) (bvadd {reg(2)(state)} "
                "#x0000000000000078)) #x0000000000000003)"),
            lambda state: (
                f"(= (ld4 (mm {state}) (bvadd {reg(2)(state)} "
                "#x0000000000000090)) #x0000000000000003)"),
            lambda state: (
                f"(= (sign3 {reg(10)(state)}) "
                f"(lean_cstring_cmp3 (mm {state}) {reg(19)(state)} "
                f"{reg(17)(state)}))"),
        ]
        assertions.extend(
            (lambda state, index=index: sret_window(state)[index])
            for index in range(3))
        add_suffix(field, 0x80003B1C, assertions)

    add_suffix("hStrAddL", 0x80003AC8, [
        lambda state: (
            f"(= (ld4 (mm {state}) (bvadd {reg(2)(state)} "
            "#x0000000000000078)) #x0000000000000003)"),
    ])
    add_suffix("hStrAddR", 0x80003AC8, [
        lambda state: (
            f"(= (ld4 (mm {state}) (bvadd {reg(2)(state)} "
            "#x0000000000000090)) #x0000000000000003)"),
        lambda state: (
            f"(not (= (ld4 (mm {state}) (bvadd {reg(2)(state)} "
            "#x0000000000000078)) #x0000000000000003))"),
    ])

    add_suffix("hFn", 0x800033D0, [
        lambda state: f"(INV {state})",
        lambda state: f"(= {load_reg(8, 0)(state)} #x000000000000000a)",
        lambda state: f"(not (= {reg(10)(state)} #x0000000000000000))",
        lambda state: f"(bvule SL_lo {reg(9)(state)})",
        lambda state: (
            f"(bvule (bvadd {reg(9)(state)} #x0000000000000018) SL_hi)"),
        lambda state: (
            f"(bvule #x000000008001ad10 {reg(9)(state)})"),
        lambda state: f"(bvule A_lo {reg(10)(state)})",
        lambda state: (
            f"(bvule {reg(10)(state)} (bvadd {reg(10)(state)} "
            "#x0000000000000010))"),
        lambda state: (
            f"(bvule (bvadd {reg(10)(state)} #x0000000000000010) A_hi)"),
        lambda state: (
            f"(or (bvule (bvadd {reg(10)(state)} #x0000000000000010) "
            "#x000000008001ad00) "
            f"(bvule #x000000008001ad10 {reg(10)(state)}))"),
    ])
    fn_point = points.get(("hFn", "0x800033d0"))
    if fn_point and "hFn" in out:
        _guard, fn_state = fn_point
        malloc_pre = _summary_input(
            campaign_dir, "hFn", fn_state, MALLOC16_CALLEE)
        if malloc_pre:
            ptr = reg(10)(fn_state)
            out["hFn"]["post_replacements"].update({
                reg(8)(malloc_pre): reg(8)(fn_state),
                reg(13)(malloc_pre): (
                    f"(ld8 (mm {fn_state}) {reg(2)(fn_state)})"),
                (f"(lean_malloc16_rel (mm {malloc_pre}) (mm {fn_state}) "
                 f"{ptr})"): "true",
            })
            # This suffix validates the post-malloc machine tail.  The three
            # replacements are exactly the external MallocContract/ABI seam:
            # allocation transition, preserved fn/sret registers, and the env
            # spill at 0(sp).  They remain present in the full residual post;
            # the suffix does not pretend to prove the allocator contract.
            out["hFn"]["summary_free"] = True
    return out


def dependency_closure(roots, graph):
    """Return every summary reachable from the query's direct dependencies."""
    seen = set()
    pending = list(roots)
    while pending:
        sym = pending.pop()
        if sym in seen:
            continue
        seen.add(sym)
        pending.extend(graph.get(sym, ()))
    return seen


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


def z3(text, timeout, defunise_bindings=True):
    if defunise_bindings:
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


def z3_projection(text, timeout):
    """Solve a projection, retrying the equivalent raw binding form.

    `defunise` usually removes expensive array-equality atoms.  On small,
    bitvector-heavy exit cases it can instead force large macro expansion.  A
    timeout is not a verdict, so retry the original equational form.  Both
    inputs state the same formula; SAT and UNSAT remain ordinary Z3 verdicts.
    """
    verdict = z3(text, timeout)
    if verdict == "unknown":
        verdict = z3(text, timeout, defunise_bindings=False)
    return verdict


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
        sys.exit(f"houdini: {d} has no src/ provenance; re-emit with "
                 f"`#emit_bmc` before checking it")
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    required = {
        "ReflectSpan.lean": os.path.join(root, "experiments", "smt", "ReflectSpan.lean"),
        "ReflectResiduals.lean": os.path.join(root, "experiments", "smt", "ReflectResiduals.lean"),
        "NativeBodyAssert.lean": os.path.join(root, "Vsa", "Sim", "rows", "NativeBodyAssert.lean"),
        "EvalCallNative2.lean": os.path.join(root, "Vsa", "Sim", "EvalCallNative2.lean"),
        "proof.elf": os.path.join(root, "c", "while-riscv-htif.elf"),
    }
    missing = [nm for nm in required if not os.path.isfile(os.path.join(src, nm))]
    if missing:
        sys.exit(f"houdini: incomplete provenance in {d}: missing {', '.join(missing)}")
    stale = [nm for nm, current in required.items()
             if open(os.path.join(src, nm), "rb").read() != open(current, "rb").read()]
    if stale:
        sys.exit(f"houdini: {d} was emitted from a DIFFERENT {', '.join(stale)} "
                 f"than the tree has.  Re-emit (`#emit_bmc \"{d}\" 60`) and re-mine; "
                 f"answering against these artefacts would be a verdict about "
                 f"another program.")


def check_campaign_manifest(d):
    """Reject stale files and missing capability metadata in a reused directory."""
    spans_path = os.path.join(d, "spans.tsv")
    caps_path = os.path.join(d, "query-capabilities.tsv")
    residual_caps = os.path.join(d, "residual-capabilities.tsv")
    holes_path = os.path.join(d, "residual-holes.tsv")
    functional_path = os.path.join(d, "functional-callees.tsv")
    certificate_path = os.path.join(d, "lean-certificates.tsv")
    for path in (spans_path, caps_path, residual_caps, holes_path, functional_path,
                 certificate_path):
        if not os.path.isfile(path):
            sys.exit(f"houdini: campaign manifest is incomplete: missing {path}")
    expected_functional = {
        "0x80004640": ("__muldi3", "bvmul(a0,a1)"),
        "0x800046a4": ("__divdi3", "bvsdiv(a0,a1)"),
        "0x80004728": ("__moddi3", "bvsrem(a0,a1)"),
    }
    functional = {row["target"]: row for row in
                  csv.DictReader(open(functional_path), delimiter="\t")}
    if set(functional) != set(expected_functional):
        sys.exit("houdini: functional-callees.tsv has the wrong helper set")
    for target, (name, result) in expected_functional.items():
        row = functional[target]
        if row.get("name") != name or row.get("mode") != "ground-functional-post" \
                or row.get("result") != result or row.get("memory") != "read-only":
            sys.exit(f"houdini: malformed arithmetic helper contract for {target}")
    spans = list(csv.DictReader(open(spans_path), delimiter="\t"))
    caps = list(csv.DictReader(open(caps_path), delimiter="\t"))
    expected = {r["field"] for r in spans}
    if expected != {r["query"] for r in caps}:
        sys.exit("houdini: query-capabilities.tsv does not match spans.tsv")
    actual = {n[:-5] for n in os.listdir(os.path.join(d, "queries"))
              if n.endswith(".smt2")}
    if actual != expected:
        extra, missing = sorted(actual - expected), sorted(expected - actual)
        sys.exit("houdini: stale/incomplete query directory; re-emit into a fresh path; "
                 f"extra={extra} missing={missing}")


def pre_block(d):
    """The residual's PRE, as encoded by Lean (`pre.smt2`): the jump-table rodata
    pins + the stack/arena layout facts `EvalEntry` carries.  Injected into the
    residual QUERIES only — a summary's clause set has to hold at any entry
    state, so its obligation gets the clause set and nothing else."""
    p = os.path.join(d, "pre.smt2")
    return open(p).read() if os.path.exists(p) else ""


def projection_pre_block(d, query):
    """Drop entry facts whose ABI does not match an internal machine cut."""
    pre = pre_block(d)
    internal_while = (
        query.startswith(("hSWhileBreak", "hSWhileRet", "hSWhileLoop")))
    if query not in {
            "hSBlock", "hSBlockIter", "hSBlockNormal", "hSBlockAbrupt"} \
            and not internal_while:
        return pre
    # pre.smt2's final group describes eval_expr's a0 return buffer.  At an
    # exec_stmt entry a0 is the interpreter pointer; at 0x41c8 it is a status.
    # Retaining these facts made status=0 inconsistent and produced a vacuous
    # hSBlockNormal verdict.
    marker = "; `EvalEntry.sret_ram`"
    return pre.split(marker, 1)[0]


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
# A named typed premise, in the repo's idiom for a genuine gap (CLAUDE.md law 2:
# "a genuine gap is a NAMED typed premise with a doc comment saying what supplies
# it").  Its ONE entry is the args-loop invariant at the loop's own recursive
# occurrence, where FIVE distinct SMT routes are measured dead -- havoc-cut (19
# candidates, both orders), a two-step lemma (18 anchors), a reload-address cap
# sweep, relevance-selected reload addresses, and the clause-bank formulation in
# both quantified and ground forms.  The evidence is in observations.md under
# `smt-args-loop-IV-obstruction`.
#
# The invariant is NOT in doubt and is not an axiom about the program: it is the
# arm's own runtime guard (`if (argc > MAX_ARGS) runtime_error`, interp.c:251).
# What no solver route establishes is the TRANSPORT of that bound across the
# recursive `jal ra, eval_expr`, where a5/a6 cross through spill slots.  Two
# facts, both measured, say why: the guards that establish the bound cannot be
# weakened (dropping them REFUTES the invariant at 7 cut points), and the query
# is already minimal (484 lines sliced, still `unknown` at 150s).
#
# WHAT SUPPLIES IT: a Lean-side induction over the loop, which is the layer that
# can do the transport structurally.  Until that lands, a verdict resting on this
# says so -- it reports VALID[modulo <name>], never a bare VALID, and the premise
# is listed in `assumed-final.tsv` beside the callee contracts.
# The value is (name, independent?).  `independent` says whether the premise can
# be discharged WITHOUT the residuals this campaign is checking.  A callee
# contract (malloc, strcmp) is independent: it is about code the campaign never
# reflects.  This one is NOT -- `argsLoopBoundAcrossCall` is a frame property of
# one `eval_expr` activation, its route is `FrameMeta.memFrame_of_chain`, that
# needs a reflected chain for eval_expr's whole run, eval_expr is recursive, so
# the chain needs the recursor IH, and the recursor IH is a residual this
# campaign checks.  Citing it as though it were a side condition would let a
# reader take 68 verdicts as independently supported when they are deferred to
# the very body of work under test.  So the verdict says `deferred`, not
# `modulo`.  See observations.md, smt-args-loop-premise-is-not-independent.
IV_PREMISE = {
    "loop_2147496412": ("argsLoopBoundAcrossCall", False),
}

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
STATE_EXIT_RE = re.compile(
    r"^\(define-fun state_exit \(\) MState (.*)\)$")
EXIT_ITE_RE = re.compile(r"\(ite (g\d+x) (b\d+) ")

_EFFECT_FRAME_THEOREM = "Vsa.Sim.FrameGuarantee.refl"
_ABI_ROUTE_FRAME_THEOREM = "Vsa.Sim.execWhileLoopRouteRow_framed"
_EFFECT_ZERO_STEP_QUERIES = {
    "hCallArgsToCall", "hCallCallToEpilogue",
}
_EFFECT_ABI_ROUTE_QUERIES = {
    "hSWhileRetBodyReturn": "hSWhileRet",
    "hSWhileLoopBodyReturn": "hSWhileLoop",
}


def certified_effect_frames(effect):
    """Return only components certified by an exact query/theorem pair.

    Dynamic-effect inventory values are deliberately not negative facts.
    In particular, ``unsupported-dynamic`` never authorizes pruning.
    """
    if not effect:
        return set()
    query = effect.get("query")
    if query in _EFFECT_ZERO_STEP_QUERIES:
        theorem = _EFFECT_FRAME_THEOREM
        field = "hCall"
    elif query in _EFFECT_ABI_ROUTE_QUERIES:
        theorem = _ABI_ROUTE_FRAME_THEOREM
        field = _EFFECT_ABI_ROUTE_QUERIES[query]
    else:
        return set()
    if effect.get("field") != field or effect.get("theorem") != theorem or \
            effect.get("provenance") != f"Lean:{theorem}":
        return set()
    framed = set()
    if effect.get("register_writes") == "none":
        framed.add("registers")
    elif theorem == _ABI_ROUTE_FRAME_THEOREM and \
            effect.get("register_writes") == "preserves-abi":
        framed.add("abi-registers")
    if effect.get("direct_memory_writes") == "none" and \
            effect.get("direct_write_rows") == "0":
        framed.add("memory")
    if effect.get("output") == "preserved":
        framed.add("output")
    return framed


def load_query_effects(campaign_dir):
    """Load effect rows for optional, certificate-gated optimizations.

    Invalid or duplicate rows fail closed to no semantic pruning.  The
    post-specific backward slice itself remains purely syntactic.
    """
    path = os.path.join(campaign_dir, "query-effects.tsv")
    if not os.path.isfile(path):
        return {}
    rows = {}
    for row in csv.DictReader(open(path), delimiter="\t"):
        query = row.get("query", "")
        if not query or query in rows:
            return {}
        rows[query] = row
    return rows


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


def _generated_dependency_roots(query, expressions):
    """Find generated variables needed by expressions and nullary helpers."""
    definitions = {}
    for line in query.splitlines():
        match = DEFN_RE.match(line)
        if match:
            definitions[match.group(1)] = line
    pending = []
    roots = set()
    for expression in expressions:
        for word in re.findall(r"[A-Za-z][A-Za-z0-9_]*", expression):
            if GEN_VAR.match(word):
                roots.add(word)
            elif word in definitions:
                pending.append(word)
    seen_definitions = set()
    while pending:
        name = pending.pop()
        if name in seen_definitions:
            continue
        seen_definitions.add(name)
        for word in re.findall(
                r"[A-Za-z][A-Za-z0-9_]*", definitions[name]):
            if GEN_VAR.match(word):
                roots.add(word)
            elif word in definitions and word not in seen_definitions:
                pending.append(word)
    return roots


def post_specific_backward_slice(query, post, premises="", effect=None):
    """Keep the exact backward cone of one residual post and its exit.

    Plain assertions remain assumptions and therefore remain roots.  Only
    generated bindings outside the selected post/exit cone are removed.
    Effect metadata is checked fail-closed here but is not used to rewrite a
    post: theorem availability is not an SMT equality proof.
    """
    # Evaluate the gate even though this syntactic pass needs no semantic frame.
    # This prevents a later component-level optimization from interpreting an
    # unsupported inventory value as preservation.
    certified_effect_frames(effect)
    exit_lines = [
        line for line in query.splitlines()
        if line.startswith("(define-fun state_exit ")
        or line.startswith("(define-fun mem_exit ")
    ]
    expressions = [post, premises, *exit_lines]
    roots = _generated_dependency_roots(query, expressions)
    bindings = {
        match.group(1)
        for line in query.splitlines()
        if (match := BIND_RE.match(line)) and GEN_VAR.match(match.group(1))
    }
    bound_roots = sorted(roots & bindings)
    if not bound_roots:
        return query
    sliced = slice_to(query, bound_roots[0], extra=bound_roots[1:])
    missing_exit_lines = [line for line in exit_lines if line not in sliced]
    if missing_exit_lines:
        sliced = sliced.replace(
            "; @@POST@@", "\n".join(missing_exit_lines) + "\n; @@POST@@")
    return sliced


def exit_cases(text):
    """Return the guarded states in the emitter's ordered exit merge.

    The final state is the merge's else arm; its guard is the final member of
    the separately emitted reachability disjunction.  Keeping that guard is
    essential: the else arm is only an exit state when that last arrival is
    reachable, not a default state for every input missed by earlier arms.
    """
    body = None
    for line in text.splitlines():
        match = STATE_EXIT_RE.match(line)
        if match:
            body = match.group(1)
            break
    if body is None:
        return []
    pairs = EXIT_ITE_RE.findall(body)
    tail = re.search(r"\s(b\d+)\)+$", body)
    if not pairs or tail is None:
        return []
    guards = None
    expected = [guard for guard, _ in pairs]
    for line in text.splitlines():
        match = re.match(r"^\(assert \(or ((?:g\d+x ?)+)\)\)$", line)
        if not match:
            continue
        found = match.group(1).split()
        if found[:len(expected)] == expected and len(found) == len(pairs) + 1:
            guards = found
            break
    if guards is None:
        return []
    return list(zip(guards, [state for _, state in pairs] + [tail.group(1)]))


def without_exit_merge(text, guards):
    """Remove the global exit merge and its reachability disjunction.

    A case query supplies one of ``guards`` directly, which both establishes
    reachability and selects the corresponding arm.  Removing the disjunction
    before dependency slicing prevents every unrelated exit path becoming a
    root merely because its guard occurs in that disjunction.
    """
    guard_set = set(guards)
    out = []
    for line in text.splitlines():
        if (line.startswith("(define-fun state_exit ") or
                line.startswith("(define-fun mem_exit ")):
            continue
        match = re.match(r"^\(assert \(or ((?:g\d+x ?)+)\)\)$", line)
        if match and set(match.group(1).split()) == guard_set:
            continue
        out.append(line)
    return "\n".join(out)


def simplify_guarded_merges(text, true_guards=(), false_guards=()):
    """Eliminate CFG merge arms fixed by the current path case.

    The reflected CFG represents a state merge as ``(ite g left right)``.  A
    suffix case separately asserts its checkpoint and exit guards and sets the
    external incoming guard frontier to false.  Merely handing those facts to
    Z3 leaves both array-valued arms in the formula; on the shared comparison
    epilogue, the unreachable arm pulls several unrelated callees back into an
    otherwise straight-line suffix and makes even the SAT consistency check
    time out.

    This pass uses only Boolean constants and aliases already asserted in the
    query.  It does not reason about machine conditions.  Replacing an ITE whose
    guard is thereby known is ordinary constant propagation under the exact
    case assumptions, so the resulting case is equisatisfiable.
    """
    lines = text.splitlines()
    bindings = {}
    for line in lines:
        match = BIND_RE.match(line)
        if match:
            bindings[match.group(1)] = match.group(2)

    values = {guard: True for guard in true_guards}
    values.update({guard: False for guard in false_guards})

    def guard_value(rhs):
        if rhs == "true":
            return True
        if rhs == "false":
            return False
        if re.fullmatch(r"g\d+[qx]?", rhs):
            return values.get(rhs)
        match = re.fullmatch(r"\(not (g\d+[qx]?)\)", rhs)
        if match and match.group(1) in values:
            return not values[match.group(1)]
        match = re.fullmatch(r"\((or|and) ((?:g\d+[qx]? ?)+)\)", rhs)
        if match:
            operands = [values.get(g) for g in match.group(2).split()]
            if match.group(1) == "or":
                if True in operands:
                    return True
                if operands and all(v is False for v in operands):
                    return False
            else:
                if False in operands:
                    return False
                if operands and all(v is True for v in operands):
                    return True
        return None

    changed = True
    while changed:
        changed = False
        for name, rhs in bindings.items():
            if not re.fullmatch(r"g\d+[qx]?", name) or name in values:
                continue
            value = guard_value(rhs)
            if value is not None:
                values[name] = value
                changed = True

    out = []
    ite = re.compile(r"^\(ite (g\d+[qx]?) (\S+) (\S+)\)$")
    for line in lines:
        match = BIND_RE.match(line)
        if match:
            choice = ite.match(match.group(2))
            if choice and choice.group(1) in values:
                selected = choice.group(2) if values[choice.group(1)] \
                    else choice.group(3)
                line = f"(assert (= {match.group(1)} {selected}))"
        out.append(line)
    return "\n".join(out)


def projection_case_queries(query, post, premises=""):
    """Split a projection over the global exit merge into guarded path cases.

    This is a logical case split, not an abstraction: the emitted query asserts
    that at least one exit guard holds and defines ``state_exit`` as their
    ordered merge.  Proving the post for every guarded arm therefore proves the
    original post.  Each arm is dependency-sliced to its state plus every
    checkpoint state read by the projection and every emitted premise.
    """
    cases = exit_cases(query)
    if not cases:
        return []
    guards = [guard for guard, _ in cases]
    base = without_exit_merge(query, guards)
    post_roots = {
        word for word in re.findall(
            r"[A-Za-z][A-Za-z0-9_]*", post + "\n" + premises)
        if GEN_VAR.match(word)
    }
    out = []
    for guard, state in cases:
        sliced = slice_to(base, state, extra=sorted(post_roots | {guard}))
        exit_def = (
            f"\n(assert {guard})\n"
            f"(define-fun state_exit () MState {state})\n"
            "(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) "
            "(mm state_exit))\n"
        )
        sliced = sliced.replace("; @@POST@@", exit_def + "; @@POST@@")
        out.append((guard, state, sliced))
    return out


def single_exit_internal_case_queries(query, post, premises=""):
    """Split one state-valued merge feeding an otherwise single exit.

    Native print has a single function return but an internal zero/nonzero-argc
    merge.  Keeping both array-valued arms makes Z3 time out even though the
    merge guard is Boolean.  Splitting both truth values is exhaustive and lets
    dependency slicing discard the unselected arm.
    """
    match = next((STATE_EXIT_RE.match(line) for line in query.splitlines()
                  if STATE_EXIT_RE.match(line)), None)
    if match is None or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", match.group(1)):
        return []
    root = match.group(1)
    bindings = {}
    for line in query.splitlines():
        binding = BIND_RE.match(line)
        if binding:
            bindings[binding.group(1)] = binding.group(2)
    needed, work = set(), [root]
    while work:
        name = work.pop()
        if name in needed or name not in bindings:
            continue
        needed.add(name)
        work.extend(word for word in re.findall(
            r"[A-Za-z][A-Za-z0-9_]*", bindings[name]) if word in bindings)
    merge = None
    for name in needed:
        candidate = re.fullmatch(
            r"\(ite (g\d+[qx]?) ([A-Za-z][A-Za-z0-9_]*) "
            r"([A-Za-z][A-Za-z0-9_]*)\)", bindings[name])
        if candidate:
            merge = candidate.group(1)
            break
    if merge is None:
        return []
    semantic_roots = {
        word for word in re.findall(
            r"[A-Za-z][A-Za-z0-9_]*", post + "\n" + premises)
        if GEN_VAR.match(word)
    }
    out = []
    for value in (True, False):
        simplified = simplify_guarded_merges(
            query,
            true_guards=(merge,) if value else (),
            false_guards=() if value else (merge,))
        sliced = slice_to(
            simplified, root, extra=sorted(semantic_roots | {merge}))
        assertion = f"(assert {merge})" if value else f"(assert (not {merge}))"
        exit_def = (
            f"\n{assertion}\n"
            f"(define-fun state_exit () MState {root})\n"
            "(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) "
            "(mm state_exit))\n")
        sliced = sliced.replace("; @@POST@@", exit_def + "; @@POST@@")
        label = merge if value else f"(not {merge})"
        out.append((label, root, sliced, post))
    return out


def direct_single_exit_query(query, post, premises="", effect=None):
    """Slice a direct single exit to its actual backward dependency cone.

    Definitions in unselected sibling arms are conservative dead code, but
    attaching every recursive-summary contract to them makes a consistency
    witness solve those irrelevant array constraints.  The raw dead equations
    are definitions of fresh names and can always be extended after a model of
    the selected cone.  Proving the post over the sliced, broader cone is also
    conservative.
    """
    match = next((STATE_EXIT_RE.match(line) for line in query.splitlines()
                  if STATE_EXIT_RE.match(line)), None)
    if match is None or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", match.group(1)):
        return query
    return post_specific_backward_slice(query, post, premises, effect)


def consistency_pins_for_query(query, pins):
    """Drop trace pins for generated states removed by dependency slicing."""
    names = set()
    for line in query.splitlines():
        declaration = DECL_RE.match(line)
        if declaration:
            names.add(declaration.group(1))
        definition = DEFN_RE.match(line)
        if definition:
            names.add(definition.group(1))
    out = []
    for line in pins.splitlines():
        generated = {
            word for word in re.findall(r"[A-Za-z][A-Za-z0-9_]*", line)
            if GEN_VAR.match(word)
        }
        if generated <= names:
            out.append(line)
    return "\n".join(out) + ("\n" if out else "")


def projection_suffix_case_queries(query, post, context):
    """Split the CFG suffix rooted at a residual checkpoint.

    Shared epilogues merge arrivals from many AST arms.  Making only the
    checkpoint state free would leave those unrelated arrivals unconstrained.
    Compute the checkpoint's forward binding cone and set just its external
    incoming guard frontier to false.  This is a structural CFG slice, not an
    assumption about executions that start at the checkpoint.
    """
    cases = exit_cases(query)
    if not cases:
        return []
    base = without_exit_merge(query, [guard for guard, _ in cases])
    bindings = {}
    for line in base.splitlines():
        match = BIND_RE.match(line)
        if match and GEN_VAR.match(match.group(1)):
            bindings[match.group(1)] = match.group(2)

    root_guard, root_state = context["guard"], context["state"]
    marked = {root_guard, root_state}
    changed = True
    while changed:
        changed = False
        for name, rhs in bindings.items():
            if name in marked:
                continue
            if set(re.findall(r"[A-Za-z][A-Za-z0-9_]*", rhs)) & marked:
                marked.add(name)
                changed = True

    frontier = set()
    for name in marked:
        for word in re.findall(r"[A-Za-z][A-Za-z0-9_]*",
                               bindings.get(name, "")):
            if (word.startswith("g") and word in bindings and
                    word not in marked):
                frontier.add(word)

    lines = []
    for line in base.splitlines():
        match = BIND_RE.match(line)
        if match and match.group(1) in (root_guard, root_state):
            continue
        if match and match.group(1) in frontier:
            line = f"(assert (= {match.group(1)} false))"
        # Whole-function entry and dispatch pins are outside this suffix.  The
        # explicit row-local context replaces them below.
        if line.startswith("(assert "):
            binding = BIND_RE.match(line)
            if not binding or not GEN_VAR.match(binding.group(1)):
                continue
        lines.append(line)
    base = "\n".join(lines)

    entry_target = "(select (rr s0) #x000000000000000a)"
    local_target = f"(select (rr {root_state}) #x0000000000000009)"
    post = post.replace(entry_target, local_target)
    for old, new in context.get("post_replacements", {}).items():
        post = post.replace(old, new)
    semantic_roots = {
        word for word in re.findall(
            r"[A-Za-z][A-Za-z0-9_]*", post + "\n" + context.get("pre", ""))
        if GEN_VAR.match(word)
    }

    out = []
    for guard, state in cases:
        if guard not in marked:
            continue
        case_base = simplify_guarded_merges(
            base, true_guards=(root_guard, guard), false_guards=frontier)
        # The checkpoint itself is deliberately free, but semantic premises may
        # relate it to a named pre-call state (hFn's malloc input is the first
        # such case).  Retain those states and their backwards dependency cones;
        # otherwise the sliced formula refers to an undeclared constant.
        sliced = slice_to(
            case_base, state, extra=sorted(semantic_roots | {guard}))
        exit_def = (
            f"\n(assert {root_guard})\n(assert {guard})\n"
            f"(define-fun state_exit () MState {state})\n"
            "(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) "
            "(mm state_exit))\n")
        sliced = sliced.replace("; @@POST@@", exit_def + "; @@POST@@")
        out.append((guard, state, sliced, post))
    return out


def abstract_exit_feasibility(query, guards, timeout):
    """Over-approximate which exit guards can coexist with emitted guard pins.

    Every non-guard branch condition becomes an independent Boolean atom, with
    syntactically identical conditions sharing an atom and explicit negations
    sharing its complement.  This forgets bitvector and array facts, so it can
    only turn an infeasible concrete path into a feasible abstract one.  Thus an
    abstract ``unsat`` soundly discharges that case; ``sat`` merely means the
    concrete, dependency-sliced case still has to be sent to Z3.
    """
    guard_defs = {}
    pins = []
    for line in query.splitlines():
        match = re.match(r"^\(assert \(= (g\d+[qx]?) (.*)\)\)$", line)
        if match:
            guard_defs[match.group(1)] = match.group(2)
            continue
        match = re.match(r"^\(assert (g\d+[qx]?)\)$", line)
        if match:
            pins.append(match.group(1))
            continue
        match = re.match(r"^\(assert \(not (g\d+[qx]?)\)\)$", line)
        if match:
            pins.append(f"(not {match.group(1)})")

    atoms = {}
    equality_families = {}

    def atom(condition):
        negated = False
        core = condition
        while core.startswith("(not ") and core.endswith(")"):
            negated = not negated
            core = core[5:-1]
        name = atoms.setdefault(core, f"c{len(atoms)}")
        match = re.match(r"^\(= (.*) (#[xb][0-9a-fA-F]+)\)$", core)
        if match:
            equality_families.setdefault(match.group(1), {})[match.group(2)] = name
        return f"(not {name})" if negated else name

    def abstract(rhs):
        if rhs == "true" or re.fullmatch(r"g\d+[qx]?", rhs):
            return rhs
        match = re.match(r"^\(or ((?:g\d+[qx]? ?)+)\)$", rhs)
        if match:
            return f"(or {match.group(1)})"
        match = re.match(r"^\(and (g\d+[qx]?) (.*)\)$", rhs)
        if match:
            return f"(and {match.group(1)} {atom(match.group(2))})"
        return atom(rhs)

    lines = ["(set-logic QF_UF)"]
    names = sorted(set(guard_defs) | set(guards))
    lines.extend(f"(declare-const {name} Bool)" for name in names)
    equations = [(name, abstract(rhs)) for name, rhs in guard_defs.items()]
    lines.extend(f"(declare-const {name} Bool)" for name in atoms.values())
    lines.extend(f"(assert (= {name} {rhs}))" for name, rhs in equations)
    for values in equality_families.values():
        names = list(values.values())
        for i, left in enumerate(names):
            for right in names[i + 1:]:
                lines.append(f"(assert (not (and {left} {right})))")
    lines.extend(f"(assert {pin})" for pin in pins)
    for guard in guards:
        lines.extend(("(push)", f"(assert {guard})", "(check-sat)", "(pop)"))
    process = subprocess.run(
        ["z3", "-smt2", "-in", f"-T:{max(1, timeout)}"],
        input="\n".join(lines), capture_output=True, text=True)
    output = (process.stdout + process.stderr).strip()
    if "(error" in output:
        return {guard: "unknown" for guard in guards}
    answers = [line for line in output.splitlines()
               if line in ("sat", "unsat", "unknown")]
    if len(answers) != len(guards):
        return {guard: "unknown" for guard in guards}
    return dict(zip(guards, answers))


def projection_post_goals(candidate):
    """Split `(not (and ...))` into independently negated conjuncts.

    UNSAT for every member is exactly UNSAT for the original disjunction.
    Keeping this helper public also lets slow projections report the precise
    conjunct that Z3 could not decide.
    """
    prefix, suffix_text = "(assert (not (and ", ")))"
    text = candidate.strip()
    if not text.startswith(prefix) or not text.endswith(suffix_text):
        return [candidate]
    body = text[len(prefix):-len(suffix_text)].strip()
    terms, start, depth = [], 0, 0
    for index, char in enumerate(body):
        if char == "(":
            depth += 1
        elif char == ")":
            depth -= 1
        elif char.isspace() and depth == 0:
            term = body[start:index].strip()
            if term:
                terms.append(term)
            start = index + 1
    tail = body[start:].strip()
    if tail:
        terms.append(tail)
    return [f"(assert (not {term}))" for term in terms] or [candidate]


def check_projection_cases(query, post, cset, pre, timeout, premises="",
                           suffix=None, consistency_pins="", effect=None):
    """Decide a semantic projection by a sound case split over exit arrivals."""

    def projection_verdict(case, candidate, budget, case_pre,
                           summary_free=False):
        answers = []
        for goal in projection_post_goals(candidate):
            sliced = post_specific_backward_slice(
                case, goal, case_pre, effect)
            summary_assumptions = "" if summary_free else assume_block(sliced, cset)
            head = sliced.replace(
                "; @@ASSUME@@", case_pre + "\n" + summary_assumptions)
            answers.append(z3_projection(
                head.replace("; @@POST@@", goal) + "\n(check-sat)\n", budget))
        if "sat" in answers:
            return "sat"
        if all(answer == "unsat" for answer in answers):
            return "unsat"
        undecided = ",".join(str(index + 1) for index, answer in enumerate(answers)
                             if answer not in ("sat", "unsat"))
        return f"unknown[post-goals={undecided}]"

    def pinned_consistency(head, budget):
        """Try a concrete witness slice before the unconstrained SAT query.

        The pins are assertions produced only after differential execution has
        matched a real trace.  SAT of the stronger ``head ∧ pins`` entails SAT
        of ``head``.  UNSAT does not: it reports a bad or stale witness instead
        of being mistaken for vacuity of the original encoding.
        """
        if not consistency_pins:
            return None
        relevant_pins = consistency_pins_for_query(head, consistency_pins)
        candidate = (head.replace("; @@POST@@", "") + "\n" +
                     relevant_pins + "\n(check-sat)\n")
        return z3_projection(candidate, budget)

    internal_cases = False
    if suffix:
        cases = projection_suffix_case_queries(query, post, suffix)
    else:
        cases = [(guard, state, case, post) for guard, state, case in
                 projection_case_queries(query, post, premises)]
        if not cases:
            cases = single_exit_internal_case_queries(query, post, premises)
            internal_cases = bool(cases)
    if not cases:
        if suffix:
            return "UNKNOWN(no-exit-case-split)"
        # A single-exit query has no `ite` merge to split.  Its emitted
        # `state_exit` is already the sole case, so check it directly.
        if "(define-fun state_exit () MState " not in query:
            return "UNKNOWN(no-exit-case-split)"
        case_pre = suffix["pre"] if suffix else pre + "\n" + premises
        direct_query = direct_single_exit_query(query, post, case_pre, effect)
        head = direct_query.replace(
            "; @@ASSUME@@", case_pre + "\n" + assume_block(direct_query, cset))
        verdict = projection_verdict(
            direct_query, post, min(timeout, 20), case_pre)
        if verdict == "sat":
            return "REFUTED[single-exit]"
        if verdict != "unsat":
            return f"UNKNOWN(single-exit:{verdict})"
        pinned = pinned_consistency(head, min(timeout, 20))
        if pinned == "sat":
            return ("VALID[candidate-suffix,trace-pinned-consistency]" if suffix
                    else "VALID[trace-pinned-consistency]")
        if pinned == "unsat":
            return "UNKNOWN(trace-pins-inconsistent)"
        consistency = z3_projection(
            head.replace("; @@POST@@", "") + "\n(check-sat)\n", min(timeout, 20))
        if consistency == "sat":
            return "VALID[candidate-suffix]" if suffix else "VALID"
        if consistency == "unknown":
            return "UNKNOWN(consistency-single-exit)"
        return "VACUOUS(single-exit-inconsistent)"
    guards = [guard for guard, _state, _case, _post in cases]
    abstract = ({guard: "sat" for guard in guards} if suffix or internal_cases else
                abstract_exit_feasibility(query, guards, min(timeout, 5)))
    concrete = []
    budget = min(timeout, 20)
    for guard, _state, case, case_post in cases:
        if abstract.get(guard) == "unsat":
            continue
        case_pre = suffix["pre"] if suffix else pre + "\n" + premises
        summary_assumptions = (
            "" if suffix and suffix.get("summary_free")
            else assume_block(case, cset))
        head = case.replace(
            "; @@ASSUME@@", case_pre + "\n" + summary_assumptions)
        verdict = projection_verdict(
            case, case_post, budget, case_pre,
            summary_free=bool(suffix and suffix.get("summary_free")))
        concrete.append((guard, head, verdict))
        if verdict == "sat":
            return f"REFUTED[exit={guard}]"
    if not concrete:
        return "VACUOUS(all-exit-guards-infeasible)"
    unknown = [guard for guard, _head, verdict in concrete
               if verdict not in ("sat", "unsat")]
    if unknown:
        return "UNKNOWN(exit-cases:" + ",".join(unknown) + ")"

    # A SAT witness for the unsliced query proves that at least one exit case
    # is consistent.  This avoids replaying trace pins against case queries
    # whose dead binding chains have been removed.
    if consistency_pins and not suffix:
        full_head = query.replace(
            "; @@ASSUME@@", pre + "\n" + premises + "\n" +
            assume_block(query, cset))
        pinned = pinned_consistency(full_head, budget)
        if pinned == "sat":
            return "VALID[trace-pinned-consistency]"
        if pinned == "unsat":
            return "UNKNOWN(trace-pins-inconsistent)"

    # Every negated-post case is UNSAT.  Establish that at least one case's
    # assumptions are nevertheless satisfiable before calling the projection
    # valid; otherwise this would merely prove a contradictory encoding.
    consistency_unknown = []
    for guard, head, _verdict in concrete:
        verdict = z3_projection(
            head.replace("; @@POST@@", "") + "\n(check-sat)\n", budget)
        if verdict == "sat":
            return "VALID[candidate-suffix]" if suffix else "VALID"
        if verdict == "unknown":
            consistency_unknown.append(guard)
    if consistency_unknown:
        return ("UNKNOWN(consistency-cases:" +
                ",".join(consistency_unknown) + ")")
    return "VACUOUS(all-exit-cases-inconsistent)"


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
        # MEASURED DEAD for the only invariant this campaign carries, so it is
        # off by default: on hDivOv's `loop_0x800031dc@m297`, all NINETEEN cut
        # candidates were tried with `INV` PROVED at each -- 8 came back `sat`
        # and 11 `unknown`, none discharged.  A `sat` says the cut is not merely
        # too weak but drops facts the invariant needs, and that is the whole
        # story: the bounds `0 <= a6` and `a5 <= 32` come from BRANCH GUARDS
        # (`blt a4,a5`, `bge zero,a5`, `a6 := 0`), whose `g` bindings reference
        # upstream states, so havocking a state strips the guards' definitions
        # along with it.  No cut point both shrinks the query and keeps the
        # bounds.  Left in, behind a flag, because the mechanism is sound where
        # the needed facts are re-derivable from `INV` alone.
        if os.environ.get("HOUDINI_CUT") == "1" and \
                cut_discharge(sl, cset, pre, gq, goal, timeout):
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
    # EARLIEST first, not latest.  Havocking a state drops everything upstream
    # of it, so a LATE cut is the aggressive one -- and for this invariant the
    # facts that establish `0 <= a6 < a5 <= 32` (the `blt`/`bge` bounds checks
    # and `a6 := 0`) all sit UPSTREAM of the loop.  Cutting late threw exactly
    # those away: `INV` was provable at the two latest candidates in ~1s and the
    # discharge then failed for want of the bounds.  An early cut keeps them and
    # still drops the long prefix that makes the query unanswerable.
    for c in cands[:tries]:
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


# Exact functional posts for the three compiler-runtime arithmetic helpers in
# the loaded RV64 image.  These are deliberately ground, per application-site
# facts rather than universal axioms.  The arithmetic is the RISC-V M-extension
# result, including its specified division-by-zero and MIN/-1 behavior (which
# SMT-LIB's bvsdiv/bvsrem share).  The implementations are pure.  Registers not
# listed as clobbered are preserved exactly; the remaining caller-saved
# registers stay unconstrained because their closed forms are irrelevant to the
# ABI and pretending that they were preserved would be unsound.
ARITH_FUNCTIONAL_CALLEES = {
    "callee_2147501632": ("__muldi3", "bvmul", {10, 11, 12, 13}),
    "callee_2147501732": ("__divdi3", "bvsdiv", {1, 5, 10, 11, 12, 13}),
    "callee_2147501864": ("__moddi3", "bvsrem", {1, 5, 10, 11, 12, 13}),
}

# Ground semantic contracts for the two helpers whose result is defined by a
# Lean relation rather than a closed bitvector expression.  The CStr functions
# are abstract symbols declared by the Lean emitter.  This avoids bounding
# string length while exposing the exact Value.equal / lexicographic result to
# the caller query.  The cited Lean helper theorems discharge these contracts;
# the independent trace fuzzer checks their executable instances.
SEMANTIC_FUNCTIONAL_CALLEES = {
    "callee_2147493980": ("value_equal", {1, 2, 5, 6, 7, 10, 11, 12, 13, 14, 15}),
    "callee_2147511968": ("strcmp", {5, 6, 7, 10, 11, 12, 13, 14, 15}),
    "callee_2147494928": ("env_get", {1, 5, 6, 7, *range(10, 18), 28, 29, 30, 31}),
    "callee_2147495132": ("env_set", {1, 5, 6, 7, *range(10, 18), 28, 29, 30, 31}),
}

# The closure arm's 16-byte malloc is an external semantic boundary.  The
# predicate denotes the successful/failing `AInv` transition of
# `Vsa.Alloc.MallocContract`; it is ground at each concrete size-16 call site.
# Header writes remain in the reflected caller and are never assumed here.
MALLOC16_CALLEE = "callee_2147501968"

# Exact output relations carried by the existing ValuePrint/NativePrint
# contracts.  They constrain output only.  They intentionally claim neither
# whole-memory preservation nor a finite bound on rendered strings.
VALUE_PRINT_CALLEE = "callee_2147494140"     # 0x800028fc
NATIVE_PRINT_CALLEE = "callee_2147495636"    # 0x80002ed4
FPUTC_CALLEE = "callee_2147508960"           # 0x800062e0
PRINT_LOOP_SUMMARY = "loop_2147495708"        # 0x80002f1c
OUTPUT_SEMANTIC_SUMMARIES = {
    VALUE_PRINT_CALLEE, NATIVE_PRINT_CALLEE, FPUTC_CALLEE,
    PRINT_LOOP_SUMMARY,
}
OUTPUT_ABI_PRESERVED = {2, 3, 4, 8, 9, *range(18, 28)}


def arithmetic_functional_posts(sites):
    """Sound ABI/memory facts for arithmetic-helper applications in a query."""
    out = []
    for base, name, arg in sites:
        contract = ARITH_FUNCTIONAL_CALLEES.get(base)
        if contract is None:
            continue
        _label, op, clobbered = contract
        post = f"({name} {arg})"
        a0 = f"(select (rr {arg}) #x000000000000000a)"
        a1 = f"(select (rr {arg}) #x000000000000000b)"
        out.append(f"(assert (= (mm {post}) (mm {arg})))")
        out.append(
            f"(assert (= (select (rr {post}) #x000000000000000a) "
            f"({op} {a0} {a1})))")
        for reg in range(32):
            if reg not in clobbered:
                idx = f"#x{reg:016x}"
                out.append(
                    f"(assert (= (select (rr {post}) {idx}) "
                    f"(select (rr {arg}) {idx})))")
    return out


def semantic_functional_posts(sites):
    """Helper-to-Lean facts, instantiated only at concrete call terms."""
    out = []
    for base, name, arg in sites:
        post = f"({name} {arg})"
        mem = f"(mm {arg})"
        out0, len0 = f"(oo {arg})", f"(ol {arg})"

        def print_args(base_ptr, count):
            rendered = f"(lean_print_args_len {mem} {base_ptr} {count})"
            out.append(
                f"(assert (= (oo {post}) (lean_print_args_out {mem} "
                f"{base_ptr} {count} {out0} {len0})))")
            out.append(
                f"(assert (= (ol {post}) (bvadd {len0} {rendered})))")

        if base == VALUE_PRINT_CALLEE:
            print_args(
                f"(select (rr {arg}) #x000000000000000a)",
                "#x0000000000000001")
        elif base == FPUTC_CALLEE:
            byte = (f"((_ extract 7 0) "
                    f"(select (rr {arg}) #x000000000000000a))")
            out.extend([
                f"(assert (= (oo {post}) (store {out0} {len0} {byte})))",
                f"(assert (= (ol {post}) "
                f"(bvadd {len0} #x0000000000000001)))",
            ])
        elif base == NATIVE_PRINT_CALLEE:
            sret = f"(select (rr {arg}) #x000000000000000a)"
            print_args(
                f"(select (rr {arg}) #x000000000000000d)",
                f"(select (rr {arg}) #x000000000000000c)")
            out.extend([
                f"(assert (= (ld4 (mm {post}) {sret}) "
                "#x0000000000000000))",
                f"(assert (= (ld8 (mm {post}) (bvadd {sret} "
                "#x0000000000000008)) #x0000000000000000))",
            ])
        elif base == PRINT_LOOP_SUMMARY:
            index = f"(select (rr {arg}) #x0000000000000009)"
            argc = f"(select (rr {arg}) #x0000000000000013)"
            remaining = f"(bvsub {argc} {index})"
            condition = (f"(and (bvule {index} {argc}) "
                         f"(bvule {argc} #x0000000000000020))")
            base_ptr = f"(select (rr {arg}) #x0000000000000008)"
            rendered = f"(lean_print_args_len {mem} {base_ptr} {remaining})"
            has_more = f"(bvult {index} {argc})"
            needs_space = (f"(and {has_more} (not (= {index} "
                           "#x0000000000000000)))")
            prefix_out = (f"(ite {needs_space} (store {out0} {len0} #x20) "
                          f"{out0})")
            prefix_len = (f"(ite {needs_space} (bvadd {len0} "
                          f"#x0000000000000001) {len0})")
            out.extend([
                f"(assert (=> {condition} (= (oo {post}) "
                f"(lean_print_args_out {mem} {base_ptr} {remaining} "
                f"{prefix_out} {prefix_len}))))",
                f"(assert (=> {condition} (= (ol {post}) "
                f"(bvadd {prefix_len} {rendered}))))",
            ])
            # The native_print loop keeps its frame and loop inputs in
            # callee-saved registers.  In particular x20 is the caller's sret
            # pointer and is used immediately after the loop.  This is the
            # control-state half of the printed-prefix loop invariant.
            for register in (2, 18, 19, 20):
                index_bv = f"#x{register:016x}"
                out.append(
                    f"(assert (= (select (rr {post}) {index_bv}) "
                    f"(select (rr {arg}) {index_bv})))")
            out.append(
                f"(assert (=> {condition} (= (select (rr {post}) "
                f"#x0000000000000009) {argc})))")
            out.append(
                f"(assert (=> {condition} (= (select (rr {post}) "
                f"#x0000000000000008) (ite {has_more} "
                f"(bvadd {base_ptr} (bvmul (bvsub {remaining} "
                f"#x0000000000000001) #x0000000000000018)) "
                f"{base_ptr}))))")

        if base in {VALUE_PRINT_CALLEE, NATIVE_PRINT_CALLEE, FPUTC_CALLEE}:
            # These are ordinary RV64 ABI calls.  The caller relies on x8/x9
            # across value_print/fputc, and println relies on x8 across both
            # nested calls.  Leaving those registers unconstrained admits
            # spurious HTIF aliases in the reflected caller.  State only the
            # ABI-fixed/callee-saved set; caller-saved registers remain free.
            for register in sorted(OUTPUT_ABI_PRESERVED):
                index = f"#x{register:016x}"
                out.append(
                    f"(assert (= (select (rr {post}) {index}) "
                    f"(select (rr {arg}) {index})))")

        if base == MALLOC16_CALLEE:
            request = f"(select (rr {arg}) #x000000000000000a)"
            result = f"(select (rr {post}) #x000000000000000a)"
            out.append(
                f"(assert (=> (= {request} #x0000000000000010) "
                f"(lean_malloc16_rel (mm {arg}) (mm {post}) {result})))")
        contract = SEMANTIC_FUNCTIONAL_CALLEES.get(base)
        if contract is None:
            continue
        label, clobbered = contract
        a0 = f"(select (rr {arg}) #x000000000000000a)"
        a1 = f"(select (rr {arg}) #x000000000000000b)"
        # `value_equal`, env_get, and env_set have real stack frames and leave
        # spill bytes changed.  Only strcmp is store-free.  Generic mined
        # footprint clauses cover the former; whole-memory equality is false.
        if label == "strcmp":
            out.append(f"(assert (= (mm {post}) {mem}))")
        out.extend([
            f"(assert (= (oo {post}) (oo {arg})))",
            f"(assert (= (ol {post}) (ol {arg})))",
        ])
        if label == "value_equal":
            out.append(
                f"(assert (= (select (rr {post}) #x000000000000000a) "
                f"(lean_value_equal {mem} {a0} {a1})))")
        elif label == "strcmp":
            cmp3 = f"(lean_cstring_cmp3 {mem} {a0} {a1})"
            out.append(
                f"(assert (or (= {cmp3} #xffffffffffffffff) "
                f"(= {cmp3} #x0000000000000000) "
                f"(= {cmp3} #x0000000000000001)))")
            out.append(
                f"(assert (= (sign3 (select (rr {post}) "
                f"#x000000000000000a)) {cmp3}))")
        elif label in ("env_get", "env_set"):
            found = f"(lean_env_lookup_found {mem} {a0} {a1})"
            slot = f"(lean_env_lookup_slot {mem} {a0} {a1})"
            value = f"(select (rr {arg}) #x000000000000000c)"
            out.append(
                f"(assert (=> {found} (= (select (rr {post}) "
                "#x000000000000000a) #x0000000000000001)))")
            out.append(
                f"(assert (=> (not {found}) (= (select (rr {post}) "
                "#x000000000000000a) #x0000000000000000)))")
            # env_get copies the selected Value to a2.  env_set copies the
            # Value at a2 into the selected slot.  Compare all three words;
            # ValueRepr alone deliberately leaves inactive padding free.
            dst = value if label == "env_get" else slot
            src = slot if label == "env_get" else value
            for offset in (0, 8, 16):
                off = f"#x{offset:016x}"
                out.append(
                    f"(assert (=> {found} (= (ld8 (mm {post}) "
                    f"(bvadd {dst} {off})) (ld8 {mem} (bvadd {src} {off})))))")
        for reg in range(32):
            if reg not in clobbered:
                idx = f"#x{reg:016x}"
                out.append(
                    f"(assert (= (select (rr {post}) {idx}) "
                    f"(select (rr {arg}) {idx})))")
    return out


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
    out.extend(arithmetic_functional_posts(sites))
    out.extend(semantic_functional_posts(sites))
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
        # A loop summary is an intra-function control-flow region, not an ABI
        # call.  It may legitimately leave `ra`, `s0`, and `s1` changed, and it
        # writes the current function's frame at addresses above its entry sp.
        # Applying the callee templates to loops produced inductive-looking but
        # concretely false claims.  Do not offer those templates to Houdini.
        if f.startswith("loop_"):
            cset[f] = [c for c in cset[f] if c not in LOOP_INVALID_CLAUSES]
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
        # The IV premise is an assumption too, and belongs in the same list --
        # an assumed clause set that is not written down is an axiom smuggled
        # into every query that mentions it.
        for sym, (nm, indep) in IV_PREMISE.items():
            role = ("NAMED PREMISE (independent side condition)"
                    if indep else
                    "NAMED PREMISE (NOT INDEPENDENT -- deferred to the residuals "
                    "under test: it is a frame property of one eval_expr "
                    "activation, and eval_expr's chain needs the recursor IH, "
                    "which is itself a residual this campaign checks)")
            fh.write(nm + "\t" + role + ": the args-loop bound transported across "
                     "the recursive call in " + sym + "; statement in "
                     "Vsa/Sim/ArgsLoopSpillResid.lean, five SMT routes measured "
                     "dead (observations.md)\n")
        for sym in sorted(OUTPUT_SEMANTIC_SUMMARIES):
            fh.write(
                sym + "\tNAMED OUTPUT SEMANTIC PREMISE: exact output-only "
                "ValuePrint/NativePrint relation; memory footprint is not "
                "assumed and machine discharge remains explicit\n")
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
    only, only_sum, only_post, warm = None, None, None, False
    verdict_out, consistency_pins_dir = None, None
    a = sys.argv[2:]
    for i, x in enumerate(a):
        if x == "--timeout": timeout = int(a[i + 1])
        elif x.startswith("-j"): jobs = int(x[2:])
        elif x == "--rounds": rounds = int(a[i + 1])
        elif x == "--phase": phase = a[i + 1]
        elif x == "--ks": ks = [int(z) for z in a[i + 1].split(",")]
        elif x == "--only": only = set(a[i + 1].split(","))
        elif x == "--only-summary": only_sum = set(a[i + 1].split(","))
        elif x == "--only-post": only_post = set(a[i + 1].split(","))
        elif x == "--verdict-out": verdict_out = a[i + 1]
        elif x == "--consistency-pins": consistency_pins_dir = a[i + 1]
        elif x == "--warm": warm = True

    if phase == "artifact-selfcheck":
        assert verdict_output_path("/tmp/c", None, None) == \
            "/tmp/c/verdicts.tsv"
        assert verdict_output_path("/tmp/c", {"hSBlock"},
                                   {"residual_relation"}) == \
            "/tmp/c/verdicts-hSBlock-residual_relation.tsv"
        assert verdict_output_path("/tmp/c", {"b", "a"}, None) == \
            "/tmp/c/verdicts-a-b.tsv"
        assert verdict_output_path("/tmp/c", {"x"}, None, "/tmp/v.tsv") == \
            "/tmp/v.tsv"
        assert projection_post_goals(
            "(assert (not (and (= a b) (= c d))))") == [
                "(assert (not (= a b)))", "(assert (not (= c d)))"]
        certificate_rows = [
            {"residual": field, "post": post, "theorem": theorem}
            for (field, post), theorem in LEAN_POST_CERTIFICATES.items()
        ]
        assert validate_lean_certificate_rows(certificate_rows) == \
            LEAN_POST_CERTIFICATES
        for bad_rows in (
            certificate_rows[:-1],
            certificate_rows + [certificate_rows[0]],
            certificate_rows + [{"residual": "hCallAssertOk",
                                  "post": "unknown", "theorem": "bogus"}],
            [dict(row, theorem="bogus") if index == 0 else row
             for index, row in enumerate(certificate_rows)],
        ):
            try:
                validate_lean_certificate_rows(bad_rows)
            except ValueError:
                pass
            else:
                raise AssertionError("malformed Lean certificate was accepted")
        assert label_projection_verdict(
            "abi_frame_x1", "VALID[Lean:Vsa.Sim.nativeAssertInternalAbi_closed]") == \
            "VALID[Lean:Vsa.Sim.nativeAssertInternalAbi_closed]"
        assert label_projection_verdict("sp", "VALID") == "VALID-MACHINE"
        machine_goals = projection_post_goals(native_assert_machine_post())
        assert len(machine_goals) == 5
        assert all("#x0000000000000001) (select" not in goal
                   and "#x0000000000000008) (select" not in goal
                   and "#x0000000000000009) (select" not in goal
                   and "#x0000000000000012) (select" not in goal
                   for goal in machine_goals)
        assert require_helper_trace_consistency("hCallAssertOk", "VALID") == \
            "UNKNOWN(trace-pinned-consistency-required)"
        assert require_helper_trace_consistency(
            "hCallAssertOk", "VALID[trace-pinned-consistency]") == \
            "VALID[trace-pinned-consistency]"
        direct_fixture = "\n".join((
            "(declare-fun callee_1 (MState) MState)",
            "(declare-const s0 MState)",
            "(declare-const b1 MState)",
            "(assert (= b1 (callee_1 s0)))",
            "(declare-const b2 MState)",
            "(assert (= b2 s0))",
            "(define-fun state_exit () MState b2)",
            "(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) "
            "(mm state_exit))",
            "; @@ASSUME@@", "; @@POST@@",
        ))
        direct_slice = direct_single_exit_query(
            direct_fixture, "(assert (= state_exit b2))")
        assert "callee_1 s0" not in direct_slice
        assert "(assert (= b2 s0))" in direct_slice
        assert "(define-fun state_exit () MState b2)" in direct_slice
        branch_fixture = "\n".join((
            "(declare-fun callee_1 (MState) MState)",
            "(declare-fun callee_2 (MState) MState)",
            "(declare-const s0 MState)",
            "(declare-const b1 MState)",
            "(assert (= b1 (callee_1 s0)))",
            "(declare-const g2 Bool)",
            "(assert (= g2 true))",
            "(declare-const b2 MState)",
            "(assert (= b2 s0))",
            "(declare-const b3 MState)",
            "(assert (= b3 (ite g2 b2 b1)))",
            "(declare-const b4 MState)",
            "(assert (= b4 (callee_2 s0)))",
            "(define-fun state_exit () MState b3)",
            "(define-fun mem_exit () (Array (_ BitVec 64) (_ BitVec 8)) "
            "(mm state_exit))",
            "; @@ASSUME@@", "; @@POST@@",
        ))
        post_slice = post_specific_backward_slice(
            branch_fixture, "(assert (= state_exit b3))")
        assert "callee_2 s0" not in post_slice
        assert "(assert (= g2 true))" in post_slice
        assert "(assert (= b3 (ite g2 b2 b1)))" in post_slice
        unsupported_effect = {
            "query": "hInt",
            "field": "hInt",
            "register_writes": "unsupported-dynamic",
            "direct_memory_writes": "unsupported-dynamic",
            "direct_write_rows": "0",
            "output": "unsupported-dynamic",
            "theorem": _EFFECT_FRAME_THEOREM,
            "provenance": f"Lean:{_EFFECT_FRAME_THEOREM}",
        }
        assert not certified_effect_frames(unsupported_effect)
        assert post_specific_backward_slice(
            branch_fixture, "(assert (= state_exit b3))",
            effect=unsupported_effect) == post_slice
        zero_step_effect = dict(
            unsupported_effect,
            query="hCallArgsToCall", field="hCall",
            register_writes="none", direct_memory_writes="none",
            output="preserved")
        assert certified_effect_frames(zero_step_effect) == {
            "registers", "memory", "output"}
        abi_route_effect = dict(
            unsupported_effect,
            query="hSWhileLoopBodyReturn", field="hSWhileLoop",
            register_writes="preserves-abi", direct_memory_writes="none",
            theorem=_ABI_ROUTE_FRAME_THEOREM,
            provenance=f"Lean:{_ABI_ROUTE_FRAME_THEOREM}",
            output="preserved")
        assert certified_effect_frames(abi_route_effect) == {
            "abi-registers", "memory", "output"}
        filtered_pins = consistency_pins_for_query(
            direct_slice,
            "(assert (= (select (rr s0) #x00) #x00))\n"
            "(assert (= (select (rr b1) #x00) #x00))\n")
        assert "rr s0" in filtered_pins and "rr b1" not in filtered_pins
        print("[selfcheck] scoped artifacts, projection splitting, and Lean certificates: ok")
        return

    if phase == "bounded":
        print(f"== bounded refutation search (k ladder {ks})")
        bounded(d, timeout, jobs, ks)
        return

    check_provenance(d)
    check_campaign_manifest(d)
    if phase == "projections":
        # A separate process exposes the production SMT formulas as the system
        # under test.  The differential tester does not import this module or
        # use these formulas as its concrete oracle.
        print(json.dumps(residual_posts(d), sort_keys=True))
        return
    if phase == "premises":
        # Like ``projections``, this is consumed out-of-process so the concrete
        # differential oracle never imports production formula builders.
        print(json.dumps(residual_pres(d), sort_keys=True))
        return
    syms = [l.strip() for l in open(os.path.join(d, "summaries.tsv")).read().splitlines()[1:] if l.strip()]
    deps = {}
    for l in open(os.path.join(d, "query-summaries.tsv")).read().splitlines()[1:]:
        if not l.strip(): continue
        parts = l.split("\t")
        deps[parts[0]] = [x for x in (parts[1].split(",") if len(parts) > 1 else []) if x]
    summary_deps = {}
    deps_path = os.path.join(d, "summary-deps.tsv")
    if os.path.exists(deps_path):
        for row in csv.DictReader(open(deps_path), delimiter="\t"):
            summary_deps[row["summary"]] = {
                sym for sym in row.get("deps", "").split(",") if sym
            }
    closed_deps = {query: dependency_closure(syms_, summary_deps)
                   for query, syms_ in deps.items()}

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
        cset = sanitize_clause_set(json.load(open(csetpath)))

    if phase in ("check", "both"):
        print(f"== phase 2: {len(deps)} residual queries x {len(POSTS)} post conjuncts")
        qs = {f: open(os.path.join(d, "queries", f + ".smt2")).read() for f in deps}
        query_caps = {r["query"]: r for r in
                      csv.DictReader(open(os.path.join(d, "query-capabilities.tsv")),
                                     delimiter="\t")}
        query_effects = load_query_effects(d)
        hole_rows = list(csv.DictReader(open(os.path.join(d, "residual-holes.tsv")),
                                        delimiter="\t"))
        holes_by_field = {}
        for row in hole_rows:
            holes_by_field.setdefault(row["field"], []).append(row["dimension"])
        assumed_syms = (set(IH_SUMMARIES) | set(NATIVE_ICALLS)
                        | set(OUTPUT_SEMANTIC_SUMMARIES))
        ap = os.path.join(d, "assumed.tsv")
        if os.path.exists(ap):
            assumed_syms |= {r["summary"] for r in csv.DictReader(open(ap), delimiter="\t")
                             if r["summary"].startswith(("callee_", "loop_", "icall_", "idisp_"))}
        op = os.path.join(d, "opaque.tsv")
        opaque_syms = ({r["summary"] for r in csv.DictReader(open(op), delimiter="\t")}
                       if os.path.exists(op) else set())
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
        per_residual_posts = residual_posts(d)
        per_residual_pres = residual_pres(d)
        per_residual_suffix = residual_suffixes(d)
        lean_certificates = load_lean_certificates(d)
        missing_certificate_queries = {
            field for field, _ in lean_certificates if field not in deps
        }
        if missing_certificate_queries:
            sys.exit("houdini: Lean certificate residual has no emitted query: " +
                     ", ".join(sorted(missing_certificate_queries)))
        pre = pre_block(d)

        def selected(f):
            return (not only or f in only
                    or query_caps.get(f, {}).get("field") in only)

        tasks = [(f, pk) for f in sorted(deps) if selected(f)
                 for pk in list(POSTS) + list(FOOTPRINT_POSTS)
                 if not only_post or pk in only_post]
        tasks += [(f, "residual_relation") for f in sorted(per_residual_posts)
                  if f in deps and selected(f) and
                  (not only_post or "residual_relation" in only_post)]
        tasks += [(f, post) for f, post in sorted(lean_certificates)
                  if f in deps and selected(f) and
                  (not only_post or post in only_post)]
        def run(t):
            f, pk = t
            certificate = lean_certificates.get((f, pk))
            if certificate is not None:
                return (f, pk, f"VALID[Lean:{certificate}]")
            # The encoder records whether the BMC frontier EMPTIED within the
            # round bound.  If it did not, the reflected term covers only part of
            # the span and a post proved over it says nothing about the rest.
            # The column was emitted and never read.
            if spans.get(f, {}).get("complete") == "false":
                return (f, pk, "INCOMPLETE(frontier-not-empty)")
            if pk == "residual_relation":
                premise = per_residual_pres.get(f, "")
                verdict = check_projection_cases(
                    qs[f], per_residual_posts[f],
                    {} if f in SUMMARY_FREE_RESIDUAL_PROJECTIONS else cset,
                    projection_pre_block(d, f), timeout, premise,
                    per_residual_suffix.get(f),
                    (open(os.path.join(consistency_pins_dir, f + ".smt2")).read()
                     if consistency_pins_dir and os.path.exists(
                         os.path.join(consistency_pins_dir, f + ".smt2"))
                     else ""),
                    query_effects.get(f))
                projection_dependencies = {
                    "hSBlock": "execBlockA,env_new_spec",
                    "hCallCallee": (
                        "EvalEntry.stack_win,StackOK,execBlockA"),
                    "hCallTooMany": (
                        "ExprRepr.call,EvalIH(callee),argc-signed-i32,ErrorSiteJal"),
                    "hCallCalleeToArgsNil": (
                        "ArgsChildReturn.StackBounds,ValueRepr"),
                    "hCallCalleeToArgsCons": (
                        "ArgsChildReturn.StackBounds,ValueRepr"),
                    "hCallArgsToCall": "ArgVecRepr,ValueRepr",
                    "hCallCallToEpilogue": "OutRepr,StoreRepr,ValueRepr",
                }
                if f in projection_dependencies and verdict.startswith("VALID"):
                    verdict = f"VALID[{projection_dependencies[f]}]"
                verdict = require_helper_trace_consistency(
                    query_caps[f]["field"], verdict)
                return (f, pk, verdict)
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
                if f in DIRECT_MEMORY_FOOTPRINT_FIELDS:
                    qa_decl = "" if "(declare-const QA " in vhead else QA_DECL
                    direct_post = (
                        qa_decl + FOOTPRINT_POSTS[pk] +
                        "(assert (not (= (select (mm state_exit) QA) "
                        "(select (mm s0) QA))))\n")
                    direct = vhead.replace("; @@POST@@", direct_post) + \
                        "\n(check-sat)\n"
                    dv = z3_projection(direct, timeout)
                    verdict = {"unsat": "VALID", "sat": "REFUTED"}.get(
                        dv, "UNKNOWN(direct-memory)")
                    if verdict == "VALID" and vac != "sat":
                        verdict += "(consistency-unproved)"
                    return (f, pk, verdict)
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
                    sym = bad.split("@")[0]
                    if sym not in IV_PREMISE:
                        return (f, pk, "UNKNOWN(iv-undischarged:" + bad + ")")
                    # falls through: the verdict is qualified below, not silent
                    iv_premise, iv_indep = IV_PREMISE[sym]
                else:
                    iv_premise, iv_indep = None, True
                fv = footprint_check(base, FOOTPRINT_POSTS[pk], wr,
                                     applied_of(sl), cset, timeout, pre=pre)
                if fv.startswith("VALID") and vac != "sat":
                    fv += "(consistency-unproved)"
                if fv.startswith("VALID") and iv_premise:
                    # `deferred` for a premise that is NOT independent of the
                    # residuals under test; `modulo` only for a genuine side
                    # condition.
                    fv += (f"[modulo {iv_premise}]" if iv_indep
                           else f"[deferred:{iv_premise}]")
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
            post = (per_residual_posts[f] if pk == "residual_relation"
                    else POSTS[pk])
            txt = head.replace("; @@POST@@", post) + "\n(check-sat)\n"
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
            r = (r[0], r[1], label_projection_verdict(r[1], r[2]))
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
        out = verdict_output_path(d, only, only_post, verdict_out)
        keys = list(POSTS) + list(FOOTPRINT_POSTS) + ["residual_relation"] + \
            list(LEAN_POSTS)
        with open(out, "w") as fh:
            fh.write("query\tresidual\tinstance\tcapability\tassumed_dependencies\t"
                     "opaque_dependencies\tunencoded_dimensions\t" +
                     "\t".join(keys) + "\n")
            for f in sorted(table):
                cap = query_caps[f]
                assumed_deps = ",".join(sorted(closed_deps.get(f, set()) & assumed_syms))
                opaque_deps = ",".join(sorted(closed_deps.get(f, set()) & opaque_syms))
                unencoded = ",".join(holes_by_field.get(cap["field"], ()))
                fh.write("\t".join((f, cap["field"], cap["instance"], cap["capability"],
                                    assumed_deps, opaque_deps, unencoded)) + "\t" +
                         "\t".join(table[f].get(k, "N/A") for k in keys) + "\n")
        for k in keys:
            print(f"  {k}: {dict(Counter(table[f].get(k, 'N/A').split('(')[0] for f in table))}")
        print("wrote", out)


if __name__ == "__main__":
    main()
