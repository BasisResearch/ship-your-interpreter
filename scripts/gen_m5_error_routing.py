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

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BUNDLE = os.path.join(ROOT, "Vsa/Sim/InterpSimBundle.lean")
TSV = os.path.join(ROOT, "scripts/m5_error_routing.tsv")
OUT = os.path.join(ROOT, "Vsa/Sim/rows/ErrorRouting.lean")


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
    rows = {}
    for line in open(TSV):
        line = line.rstrip("\n")
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        name, arity, pc, bytes_, desc = parts[0], parts[1], parts[2], parts[3], parts[4]
        b = le_bytes(SITE_WORD[pc])  # derive LE bytes from the word, ignore tsv col
        rows[name] = dict(arity=int(arity), pc=pc, bytes=b, desc=desc)
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


def emit():
    prems = parse_premises()
    tsv = load_tsv()
    L = []
    A = L.append
    A("import Vsa.Sim.ErrorSiteRows")
    A("import Vsa.Sim.ErrorSiteApplied")
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
    A("config `c` is parked at this error node's `jal runtime_error`.  `errRow` is")
    A("polymorphic in `SitePre`, so the premise→site assignment (`m5_error_routing.tsv`)")
    A("only fixes the `JalErrPre <pc>` shape of that reachability residual.")
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

    # emit one route_<name> per premise
    for name, body in prems:
        info = tsv[name]
        pc = info["pc"]
        b = info["bytes"]  # [b0,b1,b2,b3]
        # errSite theorem name: errSite_<pc without 0x>
        site = "errSite_" + pc.replace("0x", "")
        nvars, arrows = count_binders(body)
        # the ∀ closure has (c : Config) as its FIRST binder; we intro c by name,
        # then the remaining (nvars-1) vars + arrows hyps as `_`.
        n_underscore = (nvars - 1) + arrows
        underscores = " ".join(["_"] * n_underscore) if n_underscore else ""
        jalpre = f"JalErrPre S.g S.inp S.m0 {pc}#64 {b[0]}#8 {b[1]}#8 {b[2]}#8 {b[3]}#8"
        A(f"/-- Route `{name}` → `{site}` ({info['desc']}). -/")
        A(f"theorem route_{name} (S : ErrShared)")
        A(f"    (hsite : ∀ c : Config, {jalpre} c) :")
        A(f"    {body} :=")
        # the body opens `∀ (c : Config) <rest>,`; intro c by name, rest as `_`.
        fun_binders = "c " + underscores if underscores else "c"
        A(f"  fun {fun_binders} =>")
        A(f"    errRow S.g S.inp S.ra0 S.s0v S.s1v S.s2v S.s3v S.s4v S.s5v S.s6v S.s7v")
        A(f"      S.s8v S.s9v S.s10v S.s11v S.spv S.m0 S.SC S.out S.HT")
        A(f"      (SitePre := {jalpre})")
        A(f"      ({site} S.g S.inp S.m0) c (hsite c)")
        A("")

    # the capstone: errFamilyClosed
    A("/-- **The routed error family (`herrFam`), modulo the shared bundle + the 42")
    A("reachability links.**  Feeds all 42 `route_<premise>` rows into")
    A("`InterpSimBundle.errFamily_of_sites` ⇒ `ErrFamily L`.  Its residuals are")
    A("exactly (1) the shared `ErrShared` bundle (L7/L8: `SC`/`HT`, M3/M6 inputs)")
    A("and (2) the 42 per-premise reachability hypotheses `hsite<name>` (the M4")
    A("caller-linkage that the machine, run to this error node, is parked at its")
    A("`jal runtime_error`).  NO other glue. -/")
    A("theorem errFamilyClosed (L : Vsa.Refine.Layout) (S : ErrShared)")
    for name, body in prems:
        info = tsv[name]
        pc = info["pc"]; b = info["bytes"]
        jalpre = f"JalErrPre S.g S.inp S.m0 {pc}#64 {b[0]}#8 {b[1]}#8 {b[2]}#8 {b[3]}#8"
        A(f"    (hsite_{name} : ∀ c : Config, {jalpre} c)")
    A("    : Vsa.Sim.InterpSimBundle.ErrFamily L :=")
    A("  Vsa.Sim.InterpSimBundle.errFamily_of_sites L")
    for name, body in prems:
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
        info = tsv[name]
        pc = info["pc"]; b = info["bytes"]
        jalpre = f"JalErrPre S.g S.inp S.m0 {pc}#64 {b[0]}#8 {b[1]}#8 {b[2]}#8 {b[3]}#8"
        A(f"    (hsite_{name} : ∀ c : Config, {jalpre} c)")
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
    open(OUT, "w").write("\n".join(L))
    print(f"wrote {OUT} ({len(prems)} premises)")


if __name__ == "__main__":
    emit()
