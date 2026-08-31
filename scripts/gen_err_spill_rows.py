#!/usr/bin/env python3
"""gen_err_spill_rows.py — the Family-A error-link emitter.

Fans `BridgeSegFramed.spillNeg_toJalErr` (the negType model) across the eight
distinct `jal runtime_error` sites whose spill prefix is a contiguous run of
`sd sN,off(sp)` callee-saved stores (`wrChain = []`).  For each such PC it emits:

  * `spill<PC>Seg` — the `#derive_case chain` over the store run (words read
    straight from `experiments/disasm.txt`);
  * `spill<PC>_toJalErr : Triple (SpillArmPre …) (JalErrPre …)` — a THIN
    instantiation of the seg-generic `ErrSpillCore.spillSeg_toJalErr` (the sole
    per-site datum is `wrChain spill<PC>Seg = []`, one `decide`);
  * `<premise>_hsite_of_armBranch` — for every premise routing to that PC, the
    ErrorReachInhab-shaped marshalling (spec binders + hyps → `ReachJal`) built
    from an arm-branch seg, then routed through `route_<premise>`/`errRow_reach`
    to `ErrHalts c`.  Signatures are lifted verbatim from `ErrorRouting.lean`.

The Family-B sites (register-setup prefixes ending in `mv a0,s2; auipc a2; addi`,
`wrChain ≠ []`, `x10 = inp` COMPUTED by the seg rather than preserved) do NOT
match the pure-store model and are emitted only as NAMED residual comments — they
resist this template (see the report).

Reads: experiments/disasm.txt, Vsa/Sim/rows/ErrorRouting.lean.
Writes: Vsa/Sim/rows/ErrSpillRows.lean.
NO Lean proof text is hand-written here beyond the fixed thin wrappers.
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
from genseg.lib import Emitter, bv64, bv32  # noqa: E402

DISASM = os.path.join(ROOT, "experiments", "disasm.txt")
ROUTING = os.path.join(ROOT, "Vsa", "Sim", "rows", "ErrorRouting.lean")
OUT = os.path.join(ROOT, "Vsa", "Sim", "rows", "ErrSpillRows.lean")
OUT_B = os.path.join(ROOT, "Vsa", "Sim", "rows", "ErrSetupRows.lean")
OUT_LINKS_B = os.path.join(ROOT, "Vsa", "Sim", "rows", "ErrArmLinksB.lean")

# The eight Family-A jal PCs (pure `sd`-store spill prefix immediately before jal).
FAMILY_A = ["800034e4", "80003950", "80003b54", "80003bc8",
            "80003d14", "80003ce8", "80003fac", "80003fdc"]

# The eleven Family-B jal PCs (register-setup prefix that COMPUTES the args:
# `mv a0,sN; li a4,0; auipc/addi a2 (msg ptr)`).  `wrChain ≠ []`; `x10 = inp` is
# computed (the entry value of the `mv a0,sN` source `sN`), read off the seg post.
FAMILY_B = ["80002e90", "80002ebc", "80003b9c", "80003c10", "80003c7c",
            "80003cc4", "80003d5c", "80003da0", "80003de8", "80003e98", "80003f58"]

# GPR name → index (the subset the setup runs touch).
_GPR = {"zero": 0, "ra": 1, "sp": 2, "gp": 3, "tp": 4,
        "t0": 5, "t1": 6, "t2": 7, "s0": 8, "fp": 8, "s1": 9,
        "a0": 10, "a1": 11, "a2": 12, "a3": 13, "a4": 14, "a5": 15,
        "a6": 16, "a7": 17, "s2": 18, "s3": 19, "s4": 20, "s5": 21,
        "s6": 22, "s7": 23, "s8": 24, "s9": 25, "s10": 26, "s11": 27,
        "t3": 28, "t4": 29, "t5": 30, "t6": 31}

_CTRL = re.compile(r'^(jal|jalr|j|jr|ret|beq|bne|blt|bge|bltu|bgeu|beqz|bnez'
                   r'|blez|bgez|bltz|bgtz|tail)\b')


def parse_disasm_lines():
    """addr(hex str) -> (word hex str, mnemonic-ish rest)."""
    d = {}
    pat = re.compile(r'^\s*([0-9a-f]{8}):\s+([0-9a-f]{8})\s+(.*)$')
    for line in open(DISASM):
        m = pat.match(line)
        if m:
            d[m.group(1)] = (m.group(2), m.group(3).strip())
    return d


def spill_run(disasm, jal_pc):
    """The contiguous run of `sd ...(sp)` stores ending just before `jal_pc`."""
    addr = int(jal_pc, 16)
    run = []
    a = addr - 4
    while True:
        h = f"{a:08x}"
        if h not in disasm:
            break
        word, mnem = disasm[h]
        if re.match(r'sd\s+s\d+,\s*\d+\(sp\)', mnem):
            run.append((h, word))
            a -= 4
        else:
            break
    run.reverse()
    return run


def le_bytes(word):
    w = int(word, 16)
    return [(w >> (8 * i)) & 0xff for i in range(4)]


def parse_routes():
    """premise -> dict(pc, bytes[4], binders(str), hyps(str), argc)."""
    txt = open(ROUTING).read()
    blocks = re.split(r'(?=^theorem route_)', txt, flags=re.M)
    routes = {}
    for b in blocks:
        m = re.match(r'theorem route_(h\w+)', b)
        if not m:
            continue
        prem = m.group(1)
        # the hsite hypothesis block: from `(hsite : ∀ (...` to its closing `) :`
        hm = re.search(r'\(hsite\s*:\s*(.*?)\)\s*:\s*\n\s*∀', b, flags=re.S)
        if not hm:
            continue
        hsite = hm.group(1)
        # split binders `∀ (...) ..., ` from the hyp chain.  The binder prefix is
        # `∀ <binders>,` up to the first top-level comma after the ∀ list.
        bm = re.match(r'∀\s*(.*?),\s*(.*)', hsite, flags=re.S)
        binders, tail = bm.group(1), bm.group(2)
        # tail is `<hyps> → ReachJal S.g S.inp S.m0 0x..#64 b0 b1 b2 b3 c`
        rm = re.search(r'(.*?)→\s*ReachJal S\.g S\.inp S\.m0 0x([0-9a-f]+)#64'
                       r'\s*0x([0-9a-f]+)#8\s*0x([0-9a-f]+)#8\s*0x([0-9a-f]+)#8'
                       r'\s*0x([0-9a-f]+)#8\s*c', tail, flags=re.S)
        hyps = rm.group(1).strip()
        pc = rm.group(2)
        bytez = [rm.group(i) for i in range(3, 7)]
        # arg count from the `fun c a1 a2 ... =>` line
        am = re.search(r'fun c ((?:a\d+ ?)*)=>', b)
        argc = len(am.group(1).split()) if am and am.group(1).strip() else 0
        routes.setdefault(prem, dict(pc=pc, bytes=bytez, binders=binders.strip(),
                                     hyps=hyps, argc=argc))
    return routes


def main():
    disasm = parse_disasm_lines()
    routes = parse_routes()
    # premise groups per Family-A PC
    by_pc = {}
    for prem, r in routes.items():
        if r["pc"] in FAMILY_A:
            by_pc.setdefault(r["pc"], []).append(prem)

    E = Emitter()
    E.house_header(
        imports=["Vsa.Sim.rows.ErrSpillCore", "Vsa.Sim.rows.ErrorReachInhab"],
        doc=("`ErrSpillRows` — the eight Family-A error links, GENERATED.\n\n"
             "Each pure-`sd`-store spill prefix → `jal runtime_error` is emitted "
             "as a `#derive_case` seg, instantiated through the seg-generic "
             "`spillSeg_toJalErr`, and marshalled per premise via "
             "`<premise>_hsite_of_armBranch` (the `ErrorReachInhab` pattern) to "
             "`ErrHalts c`.  GENERATED by `scripts/gen_err_spill_rows.py`; DO NOT "
             "hand-edit.\n\nNO sorry/axiom/native_decide/bv_decide; no Mathlib."),
        namespace="Vsa.Sim",
        opens=[
            "open LeanRV64DExecutable Vsa",
            "open Vsa.Machine (MState Config Steps)",
            "open Vsa.Logic (Triple)",
            "open Vsa.While",
            "open Register",
        ],
    )

    for pc in FAMILY_A:
        run = spill_run(disasm, pc)
        assert run, f"no store run for {pc}"
        pc0 = run[0][0]
        jb = le_bytes(disasm[pc][0])
        segname = f"spill{pc}Seg"
        E(f"/-! ### jal `0x{pc}` — {len(run)} `sd` spill{'s' if len(run)!=1 else ''}"
          f" `0x{pc0}..0x{run[-1][0]}` → jal.  Premises: "
          f"{', '.join(by_pc.get(pc, []))}. -/")
        E(f"#derive_case {segname} chain")
        entries = [f"({bv64(a)}, {bv32(w)})" for (a, w) in run]
        E("  [" + entries[0] + ("," if len(entries) > 1 else ""))
        for j, e in enumerate(entries[1:], start=1):
            last = (j == len(entries) - 1)
            E("   " + e + ("]" if last else ","))
        E.print_axioms(f"{segname}_seg")
        E.blank()
        # thin instantiation of the generic bridge
        bstr = " ".join(f"0x{b:02x}#8" for b in jb)
        E(f"/-- The `0x{pc}` spill bridge — a thin instance of "
          f"`spillSeg_toJalErr` (`wrChain = []` by `decide`). -/")
        E(f"theorem spill{pc}_toJalErr (S : ErrShared) "
          f"(m0 : Std.ExtHashMap Nat (BitVec 8))")
        E(f"    (L : GRegs) (lds : List (List (BitVec 8))) :")
        E(f"    Triple (SpillArmPre S m0 L lds {segname} {bv64(pc0)} {bv64(pc)} "
          f"{bstr})")
        E(f"      (JalErrPre S.g S.inp S.m0 {bv64(pc)} {bstr}) :=")
        E(f"  spillSeg_toJalErr S m0 L lds {segname} {bv64(pc0)} {bv64(pc)} "
          f"{bstr} (by decide)")
        E.print_axioms(f"spill{pc}_toJalErr")
        E.blank()
        # per-premise hsite marshalling
        for prem in by_pc.get(pc, []):
            r = routes[prem]
            bstr_p = " ".join(f"0x{b}#8" for b in r["bytes"])
            args = " ".join(f"a{i}" for i in range(1, r["argc"] + 1))
            E(f"/-- `{prem}` arm-branch marshalling → `ErrHalts c` "
              f"(ErrorReachInhab pattern; arm `hlink` is the named M4 residual). -/")
            E(f"theorem {prem}_hsite_of_armBranch (S : ErrShared)")
            E(f"    {{ArmBranchPre : Config → Prop}}")
            E(f"    (seg : Triple ArmBranchPre")
            E(f"      (JalErrPre S.g S.inp S.m0 0x{r['pc']}#64 {bstr_p}))")
            E(f"    (hlink : ∀ {r['binders']},")
            E(f"      {r['hyps']} → ArmBranchPre c) :")
            E(f"    ∀ {r['binders']},")
            E(f"      {r['hyps']} → ErrHalts c :=")
            E(f"  route_{prem} S")
            E(f"    (fun c {args} =>")
            E(f"      reachJal_of_armBranch S 0x{r['pc']}#64 {bstr_p} seg c")
            E(f"        (hlink c {args}))")
            E.print_axioms(f"{prem}_hsite_of_armBranch")
            E.blank()

    E("end Vsa.Sim")
    E.write(OUT)
    print(f"wrote {OUT}")
    print(f"Family-A PCs: {len(FAMILY_A)}; premises: "
          f"{sum(len(by_pc.get(pc, [])) for pc in FAMILY_A)}")

    emit_arm_links(disasm, routes, by_pc)


def emit_arm_links(disasm, routes, by_pc):
    """The `ErrArmLinks` collector: ONE named-field structure carrying every
    Family-A premise's arm-linkage residual (`spec → SpillArmPre`), plus one
    consumer per premise producing `ErrHalts c`.  This is the genuinely M4-side
    residue, collected so the consumer story is `ErrShared + ErrArmLinks +
    Runtime_errorLoaded`."""
    # per-premise seg identity (pc0, segname, jal bytes)
    meta = {}
    for pc in FAMILY_A:
        run = spill_run(disasm, pc)
        pc0 = run[0][0]
        jb = le_bytes(disasm[pc][0])
        for prem in by_pc.get(pc, []):
            meta[prem] = dict(pc=pc, pc0=pc0, seg=f"spill{pc}Seg",
                              bytes=" ".join(f"0x{b:02x}#8" for b in jb))

    E = Emitter()
    E.house_header(
        imports=["Vsa.Sim.rows.ErrSpillRows"],
        doc=("`ErrArmLinks` — the Family-A arm-linkage collector (item 3).\n\n"
             "The `<premise>_hsite_of_armBranch` marshalling (ErrSpillRows) and "
             "the seg-generic `spillSeg_toJalErr` reduce each Family-A error link "
             "to ONE genuinely M4-side residual: that the premise's spec context "
             "lands the machine at the spill-block entry (`SpillArmPre`).  This "
             "structure collects all 16 such residuals into ONE named-field "
             "bundle, so `errLinkA_<premise>` closes to `ErrHalts c` from just "
             "`ErrShared` + `ErrArmLinks` (whose fields carry the "
             "`Runtime_errorLoaded`/`LongjmpLoaded` loaded-post data inside "
             "`SpillArmPre`).  GENERATED by `scripts/gen_err_spill_rows.py`; DO "
             "NOT hand-edit.\n\nNO sorry/axiom/native_decide/bv_decide; no "
             "Mathlib."),
        namespace="Vsa.Sim",
        opens=[
            "open LeanRV64DExecutable Vsa",
            "open Vsa.Machine (MState Config Steps)",
            "open Vsa.Logic (Triple)",
            "open Vsa.While",
            "open Register",
        ],
    )
    # the collector structure
    E("/-- **The Family-A arm-linkage collector.**  One field per Family-A "
      "premise: the")
    E("arm-linkage residual that the premise's spec context lands the machine at "
      "the")
    E("spill-block entry (`SpillArmPre`), the genuine M4-side work.  All other "
      "layers")
    E("(seg run, jal seam, per-premise marshalling) are proved. -/")
    E("structure ErrArmLinks (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))")
    E("    (L : GRegs) (lds : List (List (BitVec 8))) where")
    for prem in meta:
        m = meta[prem]
        r = routes[prem]
        E(f"  link_{prem} : ∀ {r['binders']},")
        E(f"      {r['hyps']} →")
        E(f"      SpillArmPre S m0 L lds {m['seg']} 0x{m['pc0']}#64 0x{m['pc']}#64 "
          f"{m['bytes']} c")
    E.blank()
    E.print_axioms("ErrArmLinks")
    E.blank()
    # per-premise consumer
    for prem in meta:
        m = meta[prem]
        r = routes[prem]
        args = " ".join(f"a{i}" for i in range(1, r["argc"] + 1))
        E(f"/-- `{prem}` closed to `ErrHalts c` from the collector — seg ≫ jal ≫ "
          f"tail, modulo only `A.link_{prem}`. -/")
        E(f"theorem errLinkA_{prem} (S : ErrShared) "
          f"(m0 : Std.ExtHashMap Nat (BitVec 8))")
        E(f"    (L : GRegs) (lds : List (List (BitVec 8))) "
          f"(A : ErrArmLinks S m0 L lds) :")
        E(f"    ∀ {r['binders']},")
        E(f"      {r['hyps']} → ErrHalts c :=")
        E(f"  {prem}_hsite_of_armBranch S (spill{m['pc']}_toJalErr S m0 L lds) "
          f"A.link_{prem}")
        E.print_axioms(f"errLinkA_{prem}")
        E.blank()
    E("end Vsa.Sim")
    outlinks = os.path.join(ROOT, "Vsa", "Sim", "rows", "ErrArmLinks.lean")
    E.write(outlinks)
    print(f"wrote {outlinks}")


# ==========================================================================
# Family B — the register-setup-prefix error links.
# ==========================================================================

def setup_run(disasm, jal_pc):
    """The contiguous straight-line run ending just before `jal_pc`, walking back
    to the first control-flow instruction (jal/branch/jr/ret).  Returns a list of
    `(addr_hex, word_hex, mnem)` in program order."""
    addr = int(jal_pc, 16)
    run = []
    a = addr - 4
    while True:
        h = f"{a:08x}"
        if h not in disasm:
            break
        word, mnem = disasm[h]
        if _CTRL.match(mnem):
            break
        run.append((h, word, mnem))
        a -= 4
    run.reverse()
    return run


def a0_source(run):
    """The register index the run's LAST `mv a0,rS` reads (the `x10` writer's
    source) and its 0-based position in the run.  `mv a0,rS` disassembles as
    `mv a0,rS` (a pseudo of `addi a0,rS,0`).  Returns (src_idx, pos)."""
    src, pos = None, None
    for i, (_a, _w, mnem) in enumerate(run):
        m = re.match(r'mv\s+a0,\s*(\w+)$', mnem)
        if m:
            src, pos = _GPR[m.group(1)], i
    assert src is not None, "no `mv a0,rS` in setup run"
    return src, pos


def _regname(idx):
    for k, v in _GPR.items():
        if v == idx and k not in ("fp",):  # prefer canonical name
            return k
    return f"x{idx}"


def emit_family_b(disasm, routes):
    """Emit `ErrSetupRows.lean` (segs + x10 readbacks + thin bridges + per-premise
    marshallings) and `ErrArmLinksB.lean` (the Family-B collector)."""
    by_pc = {}
    for prem, r in routes.items():
        if r["pc"] in FAMILY_B:
            by_pc.setdefault(r["pc"], []).append(prem)

    E = Emitter()
    E.house_header(
        imports=["Vsa.Sim.rows.ErrSetupCore", "Vsa.Sim.rows.ErrorReachInhab"],
        doc=("`ErrSetupRows` — the eleven Family-B error links, GENERATED.\n\n"
             "Each register-setup prefix (`mv a0,sN; li a4,0; auipc/addi a2 …`) → "
             "`jal runtime_error` is emitted as a `#derive_case` seg, an `x10` "
             "readback (the `mv a0,sN` value = `sN`'s entry value, read off the "
             "seg post via `lookupG_runGM_mid` + `srcVal_runGM_ne`), a THIN "
             "instantiation of the seg-generic `spillSetupSeg_toJalErr`, and a "
             "per-premise `<premise>_hsite_of_armBranch` marshalling to `ErrHalts "
             "c`.  `wrChain ≠ []`: `x10 = inp` is COMPUTED, so the entry predicate "
             "pins `sN = inp` and reads `x10` back off the post; the g-frame is "
             "the named residual `SetupArmPre.hgJal`.  The value_kind_name-return "
             "sites start the seg AT the return point (`mv a4,a0` captures the "
             "call result).  GENERATED by `scripts/gen_err_spill_rows.py`; DO NOT "
             "hand-edit.\n\nNO sorry/axiom/native_decide/bv_decide; no Mathlib."),
        namespace="Vsa.Sim",
        opens=[
            "open LeanRV64DExecutable Vsa",
            "open Vsa.Machine (MState Config Steps)",
            "open Vsa.Logic (Triple)",
            "open Vsa.While",
            "open Register",
        ],
    )
    E("set_option maxHeartbeats 1600000")
    E("set_option maxRecDepth 1000000")
    E.blank()

    meta = {}  # pc -> dict(pc0, seg, jbytes, src, pos, run, has_store)
    for pc in FAMILY_B:
        run = setup_run(disasm, pc)
        assert run, f"no setup run for {pc}"
        pc0 = run[0][0]
        jb = le_bytes(disasm[pc][0])
        jbytes = " ".join(f"0x{b:02x}#8" for b in jb)
        src, pos = a0_source(run)
        has_store = any(re.match(r's[wdb]\s', m) for (_a, _w, m) in run)
        meta[pc] = dict(pc0=pc0, seg=f"setup{pc}Seg", jbytes=jbytes,
                        src=src, pos=pos, run=run, has_store=has_store)

        E(f"/-! ### jal `0x{pc}` — setup run `0x{pc0}..0x{run[-1][0]}` → jal "
          f"(x10 ← {_regname(src)}). Premises: {', '.join(by_pc.get(pc, []))}. -/")
        # the #derive_case seg
        E(f"#derive_case {meta[pc]['seg']} chain")
        entries = [(f"({bv64(a)}, {bv32(w)})", m) for (a, w, m) in run]
        for j, (e, m) in enumerate(entries):
            open_br = "  [" if j == 0 else "   "
            close = "]" if j == len(entries) - 1 else ","
            E(f"{open_br}{e}{close}   -- {m}")
        E.print_axioms(f"{meta[pc]['seg']}_seg")

        # the x10 readback: split run as pre ++ [writer] ++ post around `pos`.
        pre = run[:pos]
        writer = run[pos]
        post = run[pos + 1:]
        def mkline_list(rs):
            return "[" + ", ".join(f"mkLine {bv64(a)} {bv32(w)}" for (a, w, _m) in rs) + "]"
        srcname = _regname(src)
        E(f"/-- The `x10` readback for `0x{pc}`: last writer of `x10` is "
          f"`mv a0,{srcname}` (`addi a0,{srcname},0`), read off the seg post. -/")
        E(f"theorem setup{pc}_x10 (inp x{src}v : BitVec 64) (lds : List (List (BitVec 8))) :")
        E(f"    lookupG 10 (evalBlocks {meta[pc]['seg']} "
          f"(SegEvalState.init [({src}, x{src}v)] lds)).regs")
        E(f"      = some x{src}v := by")
        E(f"  rw [evalBlocks_regs]")
        E(f"  show lookupG 10 (runGM")
        E(f"      ({mkline_list(pre)} ++ mkLine {bv64(writer[0])} {bv32(writer[1])} ::")
        E(f"        {mkline_list(post)})")
        E(f"      [({src}, x{src}v)] lds) = some x{src}v")
        E(f"  rw [lookupG_runGM_mid {mkline_list(pre)}")
        E(f"      (mkLine {bv64(writer[0])} {bv32(writer[1])}) {mkline_list(post)}")
        E(f"      [({src}, x{src}v)] lds (by decide) 10 (by decide) (by decide)]")
        E(f"  show some (srcVal {src} (runGM {mkline_list(pre)} [({src}, x{src}v)] lds)")
        E(f"      + Functions.sign_extend 0#12) = some x{src}v")
        E(f"  rw [srcVal_runGM_ne {src} {mkline_list(pre)} (by decide) [({src}, x{src}v)] lds]")
        E(f"  show some (srcVal {src} [({src}, x{src}v)] + Functions.sign_extend 0#12) = some x{src}v")
        E(f"  rw [show (Functions.sign_extend 0#12 : BitVec 64) = 0#64 from by decide, BitVec.add_zero]")
        E(f"  rfl")
        E.print_axioms(f"setup{pc}_x10")

        # the thin bridge (fully generic — no per-site obligation)
        E(f"/-- The `0x{pc}` setup bridge — a thin instance of `spillSetupSeg_toJalErr`. -/")
        E(f"theorem setup{pc}_toJalErr (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))")
        E(f"    (L : GRegs) (lds : List (List (BitVec 8))) :")
        E(f"    Triple (SetupArmPre S m0 L lds {meta[pc]['seg']} {bv64(pc0)} {bv64(pc)} {jbytes})")
        E(f"      (JalErrPre S.g S.inp S.m0 {bv64(pc)} {jbytes}) :=")
        E(f"  spillSetupSeg_toJalErr S m0 L lds {meta[pc]['seg']} {bv64(pc0)} {bv64(pc)} {jbytes}")
        E.print_axioms(f"setup{pc}_toJalErr")

        # per-premise marshalling
        for prem in by_pc.get(pc, []):
            r = routes[prem]
            bstr_p = " ".join(f"0x{b}#8" for b in r["bytes"])
            args = " ".join(f"a{i}" for i in range(1, r["argc"] + 1))
            E(f"/-- `{prem}` arm-branch marshalling → `ErrHalts c` (Family B; arm "
              f"`hlink` is the named M4 residual). -/")
            E(f"theorem {prem}_hsite_of_armBranch (S : ErrShared)")
            E(f"    {{ArmBranchPre : Config → Prop}}")
            E(f"    (seg : Triple ArmBranchPre")
            E(f"      (JalErrPre S.g S.inp S.m0 0x{r['pc']}#64 {bstr_p}))")
            E(f"    (hlink : ∀ {r['binders']},")
            E(f"      {r['hyps']} → ArmBranchPre c) :")
            E(f"    ∀ {r['binders']},")
            E(f"      {r['hyps']} → ErrHalts c :=")
            E(f"  route_{prem} S")
            E(f"    (fun c {args} =>")
            E(f"      reachJal_of_armBranch S 0x{r['pc']}#64 {bstr_p} seg c")
            E(f"        (hlink c {args}))")
            E.print_axioms(f"{prem}_hsite_of_armBranch")

    E("end Vsa.Sim")
    E.write(OUT_B)
    print(f"wrote {OUT_B}")
    print(f"Family-B PCs: {len(FAMILY_B)}; premises: "
          f"{sum(len(by_pc.get(pc, [])) for pc in FAMILY_B)}")

    emit_arm_links_b(routes, by_pc, meta)


def emit_arm_links_b(routes, by_pc, meta):
    """The `ErrArmLinksB` collector: one field per Family-B premise (`spec →
    SetupArmPre`), plus one consumer per premise producing `ErrHalts c`."""
    E = Emitter()
    E.house_header(
        imports=["Vsa.Sim.rows.ErrSetupRows"],
        doc=("`ErrArmLinksB` — the Family-B arm-linkage collector.\n\n"
             "The `<premise>_hsite_of_armBranch` marshalling (ErrSetupRows) and "
             "the seg-generic `spillSetupSeg_toJalErr` reduce each Family-B error "
             "link to ONE genuinely M4-side residual: that the premise's spec "
             "context lands the machine at the setup-block entry (`SetupArmPre`, "
             "whose `hx10read`/`hgJal` fields carry the computed-`x10`/`g`-frame "
             "data).  This structure collects all such residuals into ONE "
             "named-field bundle, so `errLinkB_<premise>` closes to `ErrHalts c` "
             "from just `ErrShared` + `ErrArmLinksB`.  GENERATED by "
             "`scripts/gen_err_spill_rows.py`; DO NOT hand-edit.\n\n"
             "NO sorry/axiom/native_decide/bv_decide; no Mathlib."),
        namespace="Vsa.Sim",
        opens=[
            "open LeanRV64DExecutable Vsa",
            "open Vsa.Machine (MState Config Steps)",
            "open Vsa.Logic (Triple)",
            "open Vsa.While",
            "open Register",
        ],
    )
    # the collector structure
    E("/-- **The Family-B arm-linkage collector.**  One field per Family-B "
      "premise: the")
    E("arm-linkage residual that the premise's spec context lands the machine at "
      "the")
    E("setup-block entry (`SetupArmPre`), the genuine M4-side work. -/")
    E("structure ErrArmLinksB (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))")
    E("    (L : GRegs) (lds : List (List (BitVec 8))) where")
    order = [(pc, prem) for pc in FAMILY_B for prem in by_pc.get(pc, [])]
    for pc, prem in order:
        m = meta[pc]
        r = routes[prem]
        E(f"  link_{prem} : ∀ {r['binders']},")
        E(f"      {r['hyps']} →")
        E(f"      SetupArmPre S m0 L lds {m['seg']} {bv64(m['pc0'])} 0x{pc}#64 "
          f"{m['jbytes']} c")
    E.blank()
    E.print_axioms("ErrArmLinksB")
    E.blank()
    # per-premise consumer
    for pc, prem in order:
        m = meta[pc]
        r = routes[prem]
        E(f"/-- `{prem}` closed to `ErrHalts c` from the collector — seg ≫ jal ≫ "
          f"tail, modulo only `A.link_{prem}`. -/")
        E(f"theorem errLinkB_{prem} (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))")
        E(f"    (L : GRegs) (lds : List (List (BitVec 8))) "
          f"(A : ErrArmLinksB S m0 L lds) :")
        E(f"    ∀ {r['binders']},")
        E(f"      {r['hyps']} → ErrHalts c :=")
        E(f"  {prem}_hsite_of_armBranch S (setup{pc}_toJalErr S m0 L lds) A.link_{prem}")
        E.print_axioms(f"errLinkB_{prem}")
    E("end Vsa.Sim")
    E.write(OUT_LINKS_B)
    print(f"wrote {OUT_LINKS_B}")


if __name__ == "__main__":
    main()
    emit_family_b(parse_disasm_lines(), parse_routes())
