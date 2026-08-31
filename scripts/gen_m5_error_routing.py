#!/usr/bin/env python3
"""gen_m5_error_routing.py — emit the M5 error-family routing file.

Every one of the 42 `errFamily_of_sites` minor premises (InterpSimBundle.lean)
has the shape

    ∀ (c : Config) <args...> <hyps...> → ErrHalts c

and is discharged UNIFORMLY by one `errRow` application (ErrorSiteRows.lean),
exactly as `ErrorSiteApplied.row_hNegType_applied` discharges `hNegType`:

    fun _ ... _ =>
      errRow g inp ra0 s0v..spv m0 SC out HT
        (SitePre := JalErrPre g inp m0 <pc> <b0> <b1> <b2> <b3>)
        (errSite_<pc> g inp m0) c (hsite <intros>)

i.e. `SitePre` is pinned to the site's `JalErrPre`, `T` is supplied by the
generated `errSite_<pc>` (proved unconditionally by `#derive_error_site`), and
the ONLY per-premise residual is `hsite` — the M4 caller-linkage that config `c`
is parked at this error node's `jal runtime_error`.

This generator reads the premise *signatures* verbatim from InterpSimBundle.lean
(the c-explicit form) and the premise→site assignment from
scripts/m5_error_routing.tsv, and emits Vsa/Sim/rows/ErrorRouting.lean:

  * `ErrShared` — the shared L7/L8 bundle (g/inp/callee-saveds/m0/SC/out/HT),
    the SAME for all 42 rows.
  * one `route_<premise>` theorem per premise: takes `ErrShared`, the config `c`,
    and the per-premise reachability `hsite`, produces the premise conclusion.
  * `errFamilyClosed` — feeds all 42 into `errFamily_of_sites` ⇒ `ErrFamily L`,
    modulo ONLY the shared bundle + the 42 reachability links.

NOTE ON THE PC ASSIGNMENT: `errRow` is polymorphic in `SitePre`, so ANY proven
`errSite_<pc>` closes ANY premise given a matching `hsite`.  The tsv distributes
the 19 proven sites across the 42 premises structurally; the precise semantic
premise→PC map is the M4 caller-linkage that `hsite` abstracts.

NO sorry/axiom/native_decide/bv_decide; no Mathlib.
"""
import re, sys, os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genseg.lib import Emitter, le_bytes as _lib_le_bytes  # shared plumbing

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUNDLE = os.path.join(ROOT, "Vsa/Sim/InterpSimBundle.lean")
TSV = os.path.join(ROOT, "scripts/m5_error_routing.tsv")
OUT = os.path.join(ROOT, "Vsa/Sim/rows/ErrorRouting.lean")

# The two "passthrough" premises: they are NOT `jal runtime_error` sites, so they
# carry no PC / `JalErrPre`, no `errSite_<pc>` Triple, and no `route_<name>`
# wrapper.  `errFamily_of_sites` (InterpSimBundle.lean) threads them straight
# through to the underlying `stuck_of_bigStepErrFull`, so `errFamilyClosed`/the
# wiring `example` take them as raw `hsite_<name>` premises and pass them
# UN-WRAPPED (no `S`).  Their hsite type IS the premise's own body — recorded
# here verbatim (with `Vsa.While.`-qualified names, the hand-patched form) so
# regeneration reproduces the landed file.  See:
#   * `hBadClosure` — 43rd site: dangling closure address (`CallErr.badClosure`),
#     `ErrorSimFull.errorSim_of_sites`; between `hNotCallable` and `hArity`.
#   * `hTopAbrupt`  — top-level abrupt → exit 70 (`TopAbrupt p`),
#     `ErrorSimFull.errorSimFull`; the LAST premise.
PASSTHROUGH = {
    "hBadClosure": (
        "∀ (c : Config) (st : SpecSt) (d : Nat) (a : Vsa.While.Addr)\n"
        "      (vs : List Vsa.While.Value), st.store.closures[a]? = none → ErrHalts c"
    ),
    "hTopAbrupt": (
        "∀ (p : Vsa.While.Program) (c : Config),\n"
        "      Vsa.While.TopAbrupt p → ErrHalts c"
    ),
}


def parse_premises():
    """Return ordered list of (name, sig_body) where sig_body is the premise
    type AS WRITTEN in InterpSimBundle (the c-explicit `∀ (c : Config) ... `)."""
    txt = open(BUNDLE).read()
    start = txt.index("theorem errFamily_of_sites")
    end = txt.index("ErrFamily L := by")
    block = txt[start:end]
    idxs = [m.start() for m in re.finditer(r'\n    \(h[A-Za-z]+ :', block)]
    idxs.append(len(block))
    prems = []
    for k in range(len(idxs) - 1):
        seg = block[idxs[k]:idxs[k + 1]]
        # Drop full-line `--` comments: the bundle interleaves doc comments
        # (e.g. before `hBadClosure`/`hTopAbrupt`) which would otherwise be
        # swallowed into the PRECEDING premise's body text.
        seg = "\n".join(ln for ln in seg.split("\n")
                        if not ln.lstrip().startswith("--"))
        name = re.search(r'\((h[A-Za-z]+) :', seg).group(1)
        # body = everything after "(hName :" up to the matching close paren.
        body = seg[seg.index(':') + 1:]
        # The last premise's segment runs up to the "ErrFamily L := by" boundary,
        # so it may carry a trailing "):" the others don't.  Cut at the LAST ") "
        # that closes this premise's binder: the body proper ends at the ")" that
        # balances the opening "(hName :".  Simplest robust rule: rstrip ws, then
        # drop a trailing ":" (from the errFamily_of_sites signature colon) and the
        # single balancing ")".
        body = body.rstrip()
        if body.endswith(':'):
            body = body[:-1].rstrip()
        if body.endswith(')'):
            body = body[:-1]
        body = body.strip()
        # In the c-explicit form the first binder is "(c : Config)"; the errRow
        # residual takes c explicitly, so we KEEP the ∀ closure verbatim.
        prems.append((name, body))
    return prems


# PC → 32-bit jal word, read from the proved errSite batches (ground truth so the
# JalErrPre little-endian bytes ALWAYS match the generated errSite_<pc> Triple).
SITE_WORD = {
    "0x80002e90": 0xf19ff0ef, "0x80002ebc": 0xeedff0ef, "0x800034e4": 0x8c5ff0ef,
    "0x80003950": 0xc58ff0ef, "0x80003b54": 0xa54ff0ef, "0x80003b9c": 0xa0cff0ef,
    "0x80003bc8": 0x9e0ff0ef, "0x80003c10": 0x998ff0ef, "0x80003c7c": 0x92cff0ef,
    "0x80003cc4": 0x8e4ff0ef, "0x80003ce8": 0x8c0ff0ef, "0x80003d14": 0x894ff0ef,
    "0x80003d5c": 0x84cff0ef, "0x80003da0": 0x808ff0ef, "0x80003de8": 0xfc1fe0ef,
    "0x80003e98": 0xf11fe0ef, "0x80003f58": 0xe51fe0ef, "0x80003fac": 0xdfdfe0ef,
    "0x80003fdc": 0xdcdfe0ef,
}


def le_bytes(word):
    return [f"0x{(word >> (8 * i)) & 0xFF:02x}" for i in range(4)]


def load_tsv():
    # genseg.lib.load_tsv gives us the #-comment + header skip + tab-split; we
    # keep the per-name dict shape (and derive LE bytes from SITE_WORD, ignoring
    # the tsv byte column) that the emitter expects.
    from genseg.lib import load_tsv as _lib_load_tsv
    cols = ["premise", "intro_arity", "site_pc", "bytes", "node_desc"]
    rows = {}
    for d in _lib_load_tsv(TSV, cols):
        name, pc, desc = d["premise"], d["site_pc"], d["node_desc"]
        b = le_bytes(SITE_WORD[pc])  # derive LE bytes from the word, ignore tsv col
        rows[name] = dict(arity=int(d["intro_arity"]), pc=pc, bytes=b, desc=desc)
    return rows


def count_binders(body):
    """number of value binders (∀ vars + hyp arrows) BEFORE the final ErrHalts c.
    Each becomes one `_` in the discharging `fun`.  NOTE the leading (c:Config)
    is one of the ∀ vars but we bind it by name `c`, so it is intro'd separately.
    """
    m = re.search(r'∀(.*?),', body, re.S)
    nvars = 0
    cvar = False
    if m:
        for grp in re.findall(r'\(([^:]+):', m.group(1)):
            names = grp.split()
            nvars += len(names)
    arrows = body.count('→')
    return nvars, arrows


def reach_hsite_type(body, pc, b):
    """The CORRECTED per-route residual type: the premise body with its FINAL
    `ErrHalts c` conclusion replaced by `ReachJal S … <pc> <bytes> c`.

    This is the `SitePre`-conditioned reachability (`ErrorReach.lean`): the route
    KEEPS every spec-derivation binder + hypothesis (they are the arm context that
    makes reachability true) and concludes that the entry config `c` RUNS to a
    config parked at this site's `jal runtime_error`, instead of the refuted
    universal `∀ c, JalErrPre … c` (which claimed `c` is ALREADY at the jal).
    Recursive premises' inner `ErrHalts c` hypotheses (IHs) stay as available
    context; only the trailing conclusion changes."""
    reach = f"ReachJal S.g S.inp S.m0 {pc}#64 {b[0]}#8 {b[1]}#8 {b[2]}#8 {b[3]}#8 c"
    head, sep, _tail = body.rstrip().rpartition("ErrHalts c")
    assert sep, f"premise body does not end in `ErrHalts c`: {body!r}"
    return head + reach


def hsite_binder(name, tsv, prems_body=None):
    """The `(hsite_<name> : <type>)` binder line(s) as ONE string.  For a routed
    site it is the CORRECTED `SitePre`-conditioned reachability residual (the
    premise body with `ErrHalts c` → `ReachJal … c`); for a PASSTHROUGH premise
    it is the premise's own body verbatim (multi-line)."""
    if name in PASSTHROUGH:
        return f"    (hsite_{name} : {PASSTHROUGH[name]})"
    info = tsv[name]
    pc, b = info["pc"], info["bytes"]
    body = prems_body[name]
    return f"    (hsite_{name} : {reach_hsite_type(body, pc, b)})"


def emit():
    prems = parse_premises()
    tsv = load_tsv()
    prems_body = {name: body for name, body in prems}
    E = Emitter()
    A = E  # Emitter is callable: A("line")
    A("import Vsa.Sim.ErrorSiteRows")
    A("import Vsa.Sim.ErrorSiteApplied")
    A("import Vsa.Sim.ErrorReach")
    A("import Vsa.Sim.InterpSimBundle")
    A("import Vsa.Sim.InterpSimFinal")
    A("import Vsa.Sim.rows.ErrSitesBatch0")
    A("import Vsa.Sim.rows.ErrSitesBatch1")
    A("import Vsa.Sim.rows.ErrSitesBatch2")
    A("import Vsa.Sim.rows.ErrSitesBatch3")
    A("")
    A("/-!")
    A("# `ErrorRouting` — the M5 error-family routing (herrFam, GENERATED)")
    A("")
    A("Every `errFamily_of_sites` minor premise (`InterpSimBundle.lean`) is")
    A("discharged UNIFORMLY by one `errRow` application (`ErrorSiteRows.lean`),")
    A("exactly as `ErrorSiteApplied.row_hNegType_applied` discharges `hNegType`:")
    A("`SitePre` is pinned to the site's `JalErrPre g inp m0 <pc> <bytes>`, the")
    A("per-site `Triple T` is supplied by the generated `errSite_<pc> g inp m0`")
    A("(proved unconditionally by `#derive_error_site`), and the shared L7/L8")
    A("`SC`/`out`/`HT` are threaded once via the `ErrShared` bundle.")
    A("")
    A("The ONLY per-premise residual is `hsite` — the M4 caller-linkage that the")
    A("config `c` REACHES this error node's `jal runtime_error`.  Its CORRECTED shape")
    A("(`ErrorReach.lean`) keeps every spec-derivation binder/hypothesis of the")
    A("premise (the arm context) and concludes `ReachJal S … <pc> <bytes> c`, i.e.")
    A("`∃ c', Steps c c' ∧ JalErrPre … c'` — the entry config `c` RUNS to a config")
    A("parked at the jal.  This replaces the earlier `∀ c, JalErrPre … c`, which was")
    A("machine-checked FALSE (`ErrLinkObstruction.jalErrPre_forall_false`): it claimed")
    A("`c` is ALREADY at the jal.  `errRow` is polymorphic in `SitePre`, so with")
    A("`SitePre := ReachJal …` and `T := Triple.seq (reachJal_triple …) (errSite …)`")
    A("the reachability IS the honest residual (`errRow_reach` below packages this).")
    A("")
    A("Two premises are NOT `jal runtime_error` sites (`hBadClosure`, `hTopAbrupt`):")
    A("they carry no `JalErrPre`/`errSite`/`route_` and are threaded straight through")
    A("`errFamily_of_sites` as raw `hsite` residuals.")
    A("")
    A("GENERATED by `scripts/gen_m5_error_routing.py`.  DO NOT hand-edit.")
    A("NO sorry/axiom/native_decide/bv_decide; no Mathlib.")
    A("-/")
    A("")
    A("open LeanRV64DExecutable Vsa")
    A("open Vsa.Machine (MState Config Steps Halts)")
    A("open Vsa.Logic (Triple)")
    A("open Vsa.While")
    A("open Register")
    A("")
    A("namespace Vsa.Sim")
    A("")
    A("local notation \"SpecSt\" => Vsa.While.St")
    A("")
    A("/-- **The shared L7/L8 error bundle** — the SAME for all 42 rows: the ghost")
    A("frame `g`, the ErrorIn pointer `inp`, the captured callee-saveds, the entry")
    A("memory `m0`, the `SnprintfContract SC` (M3 snprintf input), and the error")
    A("message `out` with its `ErrorTailChain HT` (M6 exit-tail input). -/")
    A("structure ErrShared where")
    A("  g : (R : Register) → Option (RegisterType R)")
    A("  inp : BitVec 64")
    for nm in ["ra0", "s0v", "s1v", "s2v", "s3v", "s4v", "s5v", "s6v", "s7v",
               "s8v", "s9v", "s10v", "s11v", "spv"]:
        A(f"  {nm} : BitVec 64")
    A("  m0 : Std.ExtHashMap Nat (BitVec 8)")
    A("  SC : SnprintfContract g inp ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv m0")
    A("  out : String")
    A("  HT : ErrorTailChain ra0 ExitStorePreExit out")
    A("")
    A("/-- **The reachability-conditioned error row.**  Packages the corrected")
    A("`SitePre := ReachJal …` composition once for all 42 routes: given the site's")
    A("proven jal-step `Triple T` (from `errSite_<pc>`) and the reachability residual")
    A("`hreach : ReachJal S.g S.inp S.m0 <pc> <bytes> c` (the entry config `c` RUNS to")
    A("a config parked at the jal), `errRow` with `T' := Triple.seq (reachJal_triple …) T`")
    A("and `SitePre := ReachJal …` yields `ErrHalts c`.  This is the honest, inhabitable")
    A("shape (`ReachJal` is `∃ c', Steps c c' ∧ JalErrPre … c'`), NOT the refuted")
    A("`∀ c, JalErrPre … c`. -/")
    A("theorem errRow_reach (S : ErrShared)")
    A("    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)")
    A("    (T : Triple (JalErrPre S.g S.inp S.m0 pcJal b0 b1 b2 b3)")
    A("      (fun c' => RuntimeErrorAt S.g S.inp S.m0 c'))")
    A("    (c : Config) (hreach : ReachJal S.g S.inp S.m0 pcJal b0 b1 b2 b3 c) :")
    A("    ErrHalts c :=")
    A("  errRow S.g S.inp S.ra0 S.s0v S.s1v S.s2v S.s3v S.s4v S.s5v S.s6v S.s7v")
    A("    S.s8v S.s9v S.s10v S.s11v S.spv S.m0 S.SC S.out S.HT")
    A("    (SitePre := ReachJal S.g S.inp S.m0 pcJal b0 b1 b2 b3)")
    A("    (Triple.seq (reachJal_triple S.g S.inp S.m0 pcJal b0 b1 b2 b3) T) c hreach")
    A("")

    # emit one route_<name> per JAL-SITE premise (passthroughs get no route_).
    for name, body in prems:
        if name in PASSTHROUGH:
            continue
        info = tsv[name]
        pc = info["pc"]
        b = info["bytes"]  # [b0,b1,b2,b3]
        # errSite theorem name: errSite_<pc without 0x>
        site = "errSite_" + pc.replace("0x", "")
        nvars, arrows = count_binders(body)
        # the ∀ closure has (c : Config) as its FIRST binder; we bind c by name and
        # bind the remaining (nvars-1) spec vars + `arrows` spec hyps by NAME so the
        # route can FORWARD them to the reachability residual `hsite` (which retains
        # them as context).  Names: a1 a2 … ak.
        k = (nvars - 1) + arrows
        arg_names = [f"a{i}" for i in range(1, k + 1)]
        fwd = (" " + " ".join(arg_names)) if arg_names else ""
        reach_ty = reach_hsite_type(body, pc, b)
        A(f"/-- Route `{name}` → `{site}` ({info['desc']}).  `hsite` is the")
        A(f"`SitePre`-conditioned reachability residual (spec context → `ReachJal`). -/")
        A(f"theorem route_{name} (S : ErrShared)")
        A(f"    (hsite : {reach_ty}) :")
        A(f"    {body} :=")
        A(f"  fun c{fwd} =>")
        A(f"    errRow_reach S {pc}#64 {b[0]}#8 {b[1]}#8 {b[2]}#8 {b[3]}#8")
        A(f"      ({site} S.g S.inp S.m0) c (hsite c{fwd})")
        A("")

    # the capstone: errFamilyClosed
    A("/-- **The routed error family (`herrFam`), modulo the shared bundle + the 42")
    A("reachability links.**  Feeds all 42 `route_<premise>` rows into")
    A("`InterpSimBundle.errFamily_of_sites` ⇒ `ErrFamily L`.  Its residuals are")
    A("exactly (1) the shared `ErrShared` bundle (L7/L8: `SC`/`HT`, M3/M6 inputs)")
    A("and (2) the 42 per-premise `SitePre`-conditioned reachability residuals")
    A("`hsite<name>`: each keeps the premise's spec-derivation context and concludes")
    A("`ReachJal … c` (the entry config `c` RUNS to a config parked at its")
    A("`jal runtime_error`) — the corrected, inhabitable M4 caller-linkage, NOT the")
    A("refuted `∀ c, JalErrPre … c`.  NO other glue. -/")
    A("theorem errFamilyClosed (L : Vsa.Refine.Layout) (S : ErrShared)")
    for name, body in prems:
        A(hsite_binder(name, tsv, prems_body))
    A("    : Vsa.Sim.InterpSimBundle.ErrFamily L :=")
    A("  Vsa.Sim.InterpSimBundle.errFamily_of_sites L")
    for name, body in prems:
        if name in PASSTHROUGH:
            A(f"    hsite_{name}")
        else:
            A(f"    (route_{name} S hsite_{name})")
    A("")
    A("#print axioms errFamilyClosed")
    A("")
    A("/-! ## Wiring check — `errFamilyClosed` fills `interpSimClosed_of_families`'")
    A("`herrFam` slot")
    A("")
    A("The `herrFam` argument of `InterpSimFinal.interpSimClosed_of_families` has")
    A("type `ErrFamily L`.  `errFamilyClosed L S hsite…` produces exactly that, so")
    A("the endgame capstone can be driven from the routed error family directly —")
    A("modulo ONLY the shared `ErrShared` bundle and the 42 reachability links. -/")
    A("example (L : Vsa.Refine.Layout) (S : ErrShared)")
    for name, body in prems:
        A(hsite_binder(name, tsv, prems_body))
    A("    (hterm : ∀ (p : Program) (c : Config) (out : String),")
    A("      Vsa.Refine.Loaded L p c → Vsa.While.BigStep p out → Halts c out 0)")
    A("    (htri : Trichotomy) (hdivFam : Vsa.Sim.InterpSimBundle.DivFamily L) :")
    A("    Vsa.Refine.InterpSim L :=")
    A("  Vsa.Sim.InterpSimFinal.interpSimClosed_of_families L hterm htri hdivFam")
    A("    (errFamilyClosed L S")
    for name, body in prems:
        A(f"      hsite_{name}")
    A("    )")
    A("")
    A("end Vsa.Sim")
    A("")
    E.write(OUT)
    print(f"wrote {OUT} ({len(prems)} premises)")


OUT_CLASSES = os.path.join(ROOT, "Vsa/Sim/rows/ErrorRoutingClasses.lean")


def emit_classes():
    """Emit the `ErrSiteLinks` bundle of the 42 CONDITIONED reachability residuals.

    Under the OLD (refuted) shape each premise's hsite was `∀ c, JalErrPre S.g
    S.inp S.m0 <pc> <bytes> c` — a type depending ONLY on the PC, so the 42
    premises' hsites collapsed to the 19 DISTINCT `jal` PCs and `ErrSiteLinks`
    carried 19 fields.  THAT COLLAPSE WAS AN ARTIFACT OF THE FALSE UNIVERSAL: it
    dropped the spec-derivation context, leaving nothing but the PC to vary on.

    The CORRECTED residual (`ErrorReach.lean`) is `SitePre`-conditioned: each hsite
    KEEPS the premise's spec binders/hypotheses and concludes `ReachJal … <pc> …
    c`.  Its type now depends on the SPEC CONTEXT, not only the PC, so premises
    sharing a PC (e.g. `hVarUndef`/`hExpr` at `0x80003b54`) have DIFFERENT hsite
    types and no longer coalesce.  `ErrSiteLinks` therefore bundles one field per
    routed premise (42), each the honest conditioned reachability residual — the
    exact remaining M4/M6 caller-linkage work, now correctly typed.

    Names `ErrSiteLinks`/`errFamilyClosed_ofClasses` are retained; their premise
    types change (that is the point of the amendment)."""
    prems = parse_premises()
    tsv = load_tsv()
    prems_body = {name: body for name, body in prems}

    E = Emitter()
    A = E
    A("import Vsa.Sim.rows.ErrorRouting")
    A("")
    A("/-!")
    A("# `ErrorRoutingClasses` — the `ErrSiteLinks` bundle of conditioned error links")
    A("")
    A("Under the OLD (refuted) shape each `errFamilyClosed` hsite was `∀ c, JalErrPre")
    A("S.g S.inp S.m0 <pc> <bytes> c`, a type fixed by the PC ALONE, so the 42 hsites")
    A("collapsed to **19 distinct `jal` PCs** and `ErrSiteLinks` carried 19 fields.")
    A("That collapse was an ARTIFACT of the false universal (`ErrLinkObstruction`):")
    A("dropping the spec-derivation context left nothing but the PC to vary on.")
    A("")
    A("The CORRECTED residual (`ErrorReach.lean`) is `SitePre`-conditioned — each")
    A("hsite keeps the premise's spec binders/hypotheses and concludes `ReachJal …")
    A("<pc> … c`.  Its type now depends on the SPEC CONTEXT, so premises sharing a PC")
    A("(e.g. `hVarUndef`/`hExpr` @ `0x80003b54`) have DIFFERENT hsite types and no")
    A("longer coalesce.  `ErrSiteLinks` therefore bundles ONE field per routed")
    A("premise (42), each the honest conditioned reachability residual;")
    A("`errFamilyClosed_ofClasses` feeds them (plus the 2 passthroughs) to")
    A("`errFamilyClosed`.  The 42→19 reduction does not survive honest conditioning —")
    A("that is the correction, not a regression.")
    A("")
    A("GENERATED by `scripts/gen_m5_error_routing.py` (`emit_classes`).  DO NOT")
    A("hand-edit.  NO sorry/axiom/native_decide/bv_decide; no Mathlib.")
    A("-/")
    A("")
    A("open LeanRV64DExecutable Vsa")
    A("open Vsa.Machine (MState Config Steps Halts)")
    A("open Vsa.Logic (Triple)")
    A("open Vsa.While")
    A("open Register")
    A("")
    A("namespace Vsa.Sim")
    A("")
    A("local notation \"SpecSt\" => Vsa.While.St")
    A("")
    A("/-- **The 42 conditioned error reachability links** — one field per routed")
    A("premise, each the `SitePre`-conditioned residual (spec context → `ReachJal …")
    A("c`).  This is the honest remaining M4/M6 caller-linkage work; the earlier 19")
    A("per-PC coalescing was an artifact of the refuted `∀ c, JalErrPre … c` shape and")
    A("does not survive conditioning. -/")
    A("structure ErrSiteLinks (S : ErrShared) where")
    for name, body in prems:
        if name in PASSTHROUGH:
            continue
        pc, b = tsv[name]["pc"], tsv[name]["bytes"]
        # reuse the same conditioned residual type; field name = hsite_<name>.
        A(f"  hsite_{name} : {reach_hsite_type(body, pc, b)}")
    A("")
    A("/-- **The routed error family from the `ErrSiteLinks` bundle + 2 passthroughs.**")
    A("Feeds each of `errFamilyClosed`'s 42 `jal`-site slots the corresponding")
    A("conditioned field of `H : ErrSiteLinks S`, plus the two non-jal passthrough")
    A("residuals `hBadClosure`/`hTopAbrupt`.  The error-side remaining work is the 42")
    A("conditioned links (the 19-PC coalescing no longer applies under correct")
    A("conditioning; see the module doc). -/")
    A("theorem errFamilyClosed_ofClasses (L : Vsa.Refine.Layout) (S : ErrShared)")
    A("    (H : ErrSiteLinks S)")
    A(hsite_binder("hBadClosure", tsv, prems_body))
    A(hsite_binder("hTopAbrupt", tsv, prems_body))
    A("    : Vsa.Sim.InterpSimBundle.ErrFamily L :=")
    A("  errFamilyClosed L S")
    for name, _ in prems:
        if name == "hBadClosure":
            A("    hsite_hBadClosure")
        elif name == "hTopAbrupt":
            A("    hsite_hTopAbrupt")
        else:
            A(f"    H.hsite_{name}")
    A("")
    A("#print axioms errFamilyClosed_ofClasses")
    A("")
    A("end Vsa.Sim")
    A("")
    E.write(OUT_CLASSES)
    n_routed = sum(1 for n, _ in prems if n not in PASSTHROUGH)
    print(f"wrote {OUT_CLASSES} ({n_routed} conditioned links + 2 passthrough)")


if __name__ == "__main__":
    emit()
    emit_classes()
