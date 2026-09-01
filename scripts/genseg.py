#!/usr/bin/env python3
"""genseg.py — the ARM COMPILER.

    python3 scripts/genseg.py <arm.toml|arm.tsv> [-o OUT.lean]

Compiles an *arm description* — name, PC span, entry register/mem pin list,
terminator kind (fallthrough/br/j/jal+callee), the post fields wanted — into a
`.lean` file matching the `EnvDefSeg` / `EnvDefBridges4` idiom EXACTLY (the
discipline-gate-clean seg-layer shape): the `#derive_case` seg def, the `L`-list,
the named-field `Post`, and the `segToTriple` (or `bridgeOfSeg`) row with its one
kernel `decide`.

This subsumes the hand-authored seg/row idioms as templates: every `#derive_case`
seg + `SegPre`/`Post` + `segToTriple` row in `EnvDefSeg.lean`/`EnvDefBridges4.lean`
(`mallocArgSeg`/`strlenArgSeg`/`appendHeadSeg`/`appendStoreSeg`/`updateStoreSeg`)
is one arm description here.

Terminator kinds
================
  fallthrough  straight-line body, no terminator; end PC = last addr + 4.
               (`mallocArgSeg`, `updateStoreSeg`.)
  br/j         the last block ends in a branch/jump terminator, decoded from
               disasm; the seg carries it in-model (`TKind.br/j`); end PC =
               the terminator target.  (`appendHeadSeg`, `appendStoreSeg`.)
  jal          the body ends in a `jal <callee>` CALL seam (out of `TKind`);
               emits a `bridgeOfSeg` row (Shape D) — NOTE: the jal-seam glue
               (`jalStep_of_obs` + the callee `site_*` lemma) is region-specific
               and emitted as a NAMED residual the row consumes, not fabricated.

Arm-description format
======================
See the `--help`-printed spec (ARM_SPEC below) and the worked examples in
`scripts/arms/`.  Both `.toml` and a flat `key<TAB>value` `.tsv` are accepted.

NO `sorry`/`axiom`/`native_decide`/`bv_decide` in the output; no Mathlib.
"""

import argparse
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genseg import lib

ROOT = lib.ROOT


ARM_SPEC = """\
ARM DESCRIPTION FORMAT (.toml)
==============================

  name        = "mallocArg"          # seg is <name>Seg, row is <name>Row,
                                      # post is <cap name>Post, L-list <name>L
  namespace   = "Vsa.Sim"            # (default Vsa.Sim)
  entry       = 0x80002b24           # entry PC (span start)
  span_end    = 0x80002b2c           # exclusive end of the STRAIGHT-LINE body
                                      # (for br/j: the terminator addr; the body
                                      #  is [entry, span_end), terminator @span_end)
  terminator  = "fallthrough"        # fallthrough | br | j | jal
  # for terminator = "br": which arm this case resolves —
  taken       = true
  # for terminator = "jal": the callee entry symbol/addr + the residual name —
  callee      = "malloc"
  callee_pc   = 0x80004790

  imports     = ["Vsa.Sim.DeriveCaseRow", "Vsa.Sim.ChainFactsTac"]
  doc         = "One-line summary of the span."

  # entry pin list: registers READ-before-written in the span (the seg's L).
  # each: reg index, the ghost-value param name.  (Order = first-use order.)
  [[pin]]
  reg = 10
  name = "a0"
  [[pin]]
  reg = 18
  name = "s2"

  # (optional) extra value-parameter binders threaded into the seg (rare).

FLAT TSV FORM (.tsv)
====================
  name<TAB>mallocArg
  entry<TAB>0x80002b24
  span_end<TAB>0x80002b2c
  terminator<TAB>fallthrough
  imports<TAB>Vsa.Sim.DeriveCaseRow,Vsa.Sim.ChainFactsTac
  doc<TAB>...
  pin<TAB>10<TAB>a0
  pin<TAB>18<TAB>s2
"""


def _tobool(v):
    if isinstance(v, str):
        return v.lower() == "true"
    return bool(v)


def norm_arm(d):
    """Normalize a loaded arm dict (toml or tsv) into a canonical structure."""
    a = {}
    a["name"] = d["name"]
    a["namespace"] = d.get("namespace", "Vsa.Sim")
    a["entry"] = lib.hexint(d["entry"])
    a["span_end"] = lib.hexint(d["span_end"])
    a["terminator"] = d.get("terminator", "fallthrough")
    a["taken"] = d.get("taken", None)
    if isinstance(a["taken"], str):
        a["taken"] = a["taken"].lower() == "true"
    # optional intermediate blocks: a chain [entry..end0]▷term0 ;; [end0+4..end1]▷term1 ;; …
    # each `[[block]]` has `end` (its terminator addr) and `taken` (its polarity).
    # The FINAL block runs [last_end+4 .. span_end) with the top-level terminator.
    a["blocks"] = []
    if "block" in d and isinstance(d["block"], list):
        for b in d["block"]:
            a["blocks"].append(
                (lib.hexint(b["end"]), _tobool(b.get("taken", True))))
    a["callee"] = d.get("callee")
    a["callee_pc"] = lib.hexint(d["callee_pc"]) if d.get("callee_pc") else None
    imports = d.get("imports", [])
    if isinstance(imports, str):
        imports = [x.strip() for x in imports.split(",") if x.strip()]
    a["imports"] = imports
    a["doc"] = d.get("doc", "")
    # pins
    pins = []
    if "pin" in d and isinstance(d["pin"], list):
        for p in d["pin"]:
            if isinstance(p, dict):
                pins.append((int(p["reg"]), p["name"]))
            else:  # tsv row: [reg, name]
                pins.append((int(p[0]), p[1]))
    a["pins"] = pins
    return a


def build_body(a, di, idx):
    """Return (blocks, end_pc) where `blocks` is a list of dicts, each
      {body: [Instr], term: term_data_or_None}
    modelling one `#derive_case` basic block ([body] ▷ terminator), and verify
    every word is tabled.

    The intermediate `[[block]]`s (each `end`/`taken`) become a chain; the FINAL
    block carries the top-level terminator (fallthrough/br/j) at `span_end`."""
    entry, span_end = a["entry"], a["span_end"]
    kind = a["terminator"]
    blocks = []
    all_instrs = []
    cur = entry
    # intermediate blocks (each ends in a branch/j terminator at its `end`)
    for (bend, btaken) in a["blocks"]:
        body = lib.words_for_range(cur, bend, di)
        tinstr = di[bend]
        tdata = lib.decode_terminator(
            tinstr, taken=btaken if tinstr.is_branch else None)
        blocks.append({"body": body, "term": tdata})
        all_instrs += body + [tinstr]
        cur = tdata["target"]   # next block's head = this terminator's target
    # final block: [cur, span_end) + the top-level terminator
    if kind in ("br", "j"):
        body = lib.words_for_range(cur, span_end, di)
        tinstr = di[span_end]
        tdata = lib.decode_terminator(
            tinstr, taken=a["taken"] if kind == "br" else None)
        blocks.append({"body": body, "term": tdata})
        all_instrs += body + [tinstr]
        end_pc = tdata["target"]
    elif kind == "jal":
        body = lib.words_for_range(cur, span_end, di)
        tinstr = di[span_end]
        if tinstr.mnem != "jal":
            raise SystemExit(
                f"terminator=jal but 0x{span_end:08x} is {tinstr.mnem}")
        blocks.append({"body": body, "term": None})
        all_instrs += body
        if not idx.has(tinstr.word):
            raise SystemExit(f"jal word 0x{tinstr.word:08x} not tabled")
        end_pc = span_end        # parked at the jal, ready for the callee seam
    else:  # fallthrough
        body = lib.words_for_range(cur, span_end, di)
        blocks.append({"body": body, "term": None})
        all_instrs += body
        end_pc = body[-1].addr + 4 if body else cur
    miss = idx.check_range(all_instrs)
    if miss:
        raise SystemExit(
            "NOT ALL WORDS TABLED (seg layer needs every word on the decode "
            "table): " + ", ".join(f"0x{m.addr:08x}:{m.word:08x}" for m in miss))
    if kind == "jal":
        _check_abi_writes(blocks, a)
    return blocks, end_pc


# Callee-saved ABI registers (RISC-V): s0/fp..s11.  A jal row emitted by
# `emit_jal_row` proves its frame with `(by show WrChainAvoidAbi <seg>; decide)`;
# if the span WRITES a callee-saved register that proposition is FALSE, the
# `decide` fails to elaborate, and Lean's error recovery lands `sorryAx` in the
# row — the file LOOKS green until `#print axioms`.  (Post-mortem: the wave-34
# concatStringifyRArg span, `mv s2,a0 ; mv s3,a0`.)  So: static-check and
# HARD-ERROR here, pointing at the framed bridge that handles such spans.
_CALLEE_SAVED = {"s0": 8, "fp": 8, "s1": 9, "s2": 18, "s3": 19, "s4": 20,
                 "s5": 21, "s6": 22, "s7": 23, "s8": 24, "s9": 25,
                 "s10": 26, "s11": 27}
_NO_GPR_WRITE = {"sd", "sw", "sh", "sb", "fsd", "fsw", "beq", "bne", "blt",
                 "bge", "bltu", "bgeu", "beqz", "bnez", "blez", "bgez", "bltz",
                 "bgtz", "j", "jr", "ret", "fence", "fence.i", "ecall", "ebreak"}


def _check_abi_writes(blocks, a):
    bad = []
    for blk in blocks:
        for ins in blk["body"]:
            if ins.mnem in _NO_GPR_WRITE:
                continue
            rd = ins.ops.split(",")[0].strip() if ins.ops else ""
            if rd in _CALLEE_SAVED:
                bad.append(f"0x{ins.addr:08x}: {ins.mnem} {ins.ops} "
                           f"(writes callee-saved {rd}=x{_CALLEE_SAVED[rd]})")
    if bad:
        raise SystemExit(
            f"arm {a['name']}: the jal span writes CALLEE-SAVED register(s) — "
            "`WrChainAvoidAbi` is FALSE and the emitted `decide` would land "
            "error-recovery sorryAx.  Use `bridgeOfSegFramed` with a restricted "
            "avoid-set instead (model: rows/ConcatStringifyRArg.lean at "
            "AbiExceptS2S3):\n  " + "\n  ".join(bad))


def emit_seg(E, a, blocks):
    """Emit the `#derive_case <name>Seg chain <block> ;; <block> …`."""
    seg = a["name"] + "Seg"
    kind = a["terminator"]
    nblk = len(blocks)
    # NOTE: a plain block comment (not `/-- -/`) — a `#derive_case` command does
    # not accept a preceding doc-comment.
    E(f"/- The `{a['name']}` span body `0x{a['entry']:08x} → "
      f"0x{a['span_end']:08x}` ({kind}-terminated, {nblk} block(s)), decoded "
      f"from `experiments/disasm.txt`. -/")
    E(f"#derive_case {seg} chain")
    for bi, blk in enumerate(blocks):
        body, term = blk["body"], blk["term"]
        last_block = (bi == nblk - 1)
        pair_lines = []
        for k, i in enumerate(body):
            lhs = (f"  [({lib.bv64(i.addr)}, {lib.bv32(i.word)})" if k == 0
                   else f"   ({lib.bv64(i.addr)}, {lib.bv32(i.word)})")
            pair_lines.append((lhs, f"{i.mnem} {i.ops}"))
        if not body:
            # empty body block (e.g. the bnez-only second block of appendHead)
            E("  []")
        else:
            w = max(len(l) for l, _ in pair_lines)
            for k, (l, c) in enumerate(pair_lines):
                rhs = "]" if k == len(pair_lines) - 1 else ","
                E(f"{l}{rhs}{' ' * (w - len(l) + 2)}-- {c}")
        if term is not None:
            chain_sep = "" if last_block else " ;;"
            E(f"    terminator {term['record']}{chain_sep}")
    E("")


def emit_L(E, a):
    """Emit the seg's entry pin list `<name>L`."""
    name = a["name"]
    pins = a["pins"]
    params = " ".join(n for _, n in pins)
    entries = ", ".join(f"({r}, {n})" for r, n in pins)
    keys = [r for r, _ in pins]
    doc = ", ".join(f"`x{r}`" for r, _ in pins)
    E(f"/-- The `{name}` entry pin list — the registers the body reads: {doc}. -/")
    if params:
        E(f"def {name}L ({params} : BitVec 64) : GRegs := [{entries}]")
    else:
        E(f"def {name}L : GRegs := [{entries}]")
    E("")
    return keys


def emit_post_and_row(E, a, end_pc, keys):
    """Emit the named-field `Post` + the `segToTriple` row (Shape A: br/j/
    fallthrough)."""
    name = a["name"]
    seg = name + "Seg"
    Post = lib.cap(name) + "Post"
    pins = a["pins"]
    pnames = " ".join(n for _, n in pins)
    Ldecl = f"{name}L {pnames}".strip()
    Lapp = f"({Ldecl})" if pins else name + "L"
    pbind = "".join(f" ({n} : BitVec 64)" for _, n in pins)
    endS = lib.bv64(end_pc)

    # ---- Post ----
    E(f"/-- The `{name}` row post: parked at the computed end PC `{endS}`, "
      f"memory = the entry memory with the seg's write-log applied (computed "
      f"off `#derive_case`). -/")
    E(f"def {Post}{pbind} (lds : List (List (BitVec 8)))")
    E(f"    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=")
    E(f"  GoodState c.σ ∧")
    E(f"  c.σ.mem = writeLog m0 (evalBlocks {seg}")
    E(f"    (SegEvalState.init {Lapp} lds)).log ∧")
    E(f"  c.σ.regs.get? Register.PC = some {endS}")
    E("")

    # ---- row ----
    E(f"/-- **`{name}Row`** — the `{name}` span as a `Triple`, via `segToTriple` "
      f"over the {a['terminator']}-terminated `{seg}`.  `hwf` is the row's one "
      f"kernel `decide` (`ChainOK`); `hpost` projects the computed end PC "
      f"({endS}) and the write-log memory off the outcome.  Replaces the hand "
      f"`site_*` `stepObs` battery for this span. -/")
    E(f"theorem {name}Row{pbind} (lds : List (List (BitVec 8)))")
    E(f"    (m0 : Std.ExtHashMap Nat (BitVec 8)) :")
    E(f"    Triple (SegPre {seg} {Lapp} lds {lib.bv64(a['entry'])} m0)")
    E(f"      ({Post} {pnames} lds m0) := by")
    # the two idioms: 1 pin -> direct `show ChainOK`; >=2 -> keysG rewrite
    keylist = "[" + ", ".join(str(k) for k in keys) + "]"
    if len(keys) <= 1:
        E(f"  apply segToTriple {seg} {Lapp} lds {lib.bv64(a['entry'])} m0")
        E(f"    ({Post} {pnames} lds m0)")
        E(f"    (by show ChainOK {lib.bv64(a['entry'])} {keylist} {seg}; decide)")
    else:
        E(f"  apply segToTriple {seg} {Lapp} lds {lib.bv64(a['entry'])} m0")
        E(f"    ({Post} {pnames} lds m0)")
        E(f"    (by have h : keysG {Lapp} = {keylist} := rfl")
        E(f"        rw [h]; show ChainOK {lib.bv64(a['entry'])} {keylist} {seg}; decide)")
    E(f"  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' _hregs")
    E(f"  refine ⟨hG', hmem', ?_⟩")
    E(f"  rw [hpc']")
    E(f"  show some (evalBlocksPC {lib.bv64(a['entry'])} "
      f"(SegEvalState.init {Lapp} lds) {seg})")
    E(f"    = some {endS}")
    E(f"  rfl")
    E("")
    E(f"#print axioms {name}Row")
    E("")


def emit_jal_row(E, a, end_pc, keys):
    """Emit the Shape-D `bridgeOfSeg` row for a jal-terminated span.

    The straight-line body run + ABI callee-saved frame are FREE via
    `bridgeOfSeg`; the region-specific jal seam (the callee `site_*` obs →
    `JalStep`) is consumed as a NAMED residual `hjalSeam` — we do NOT fabricate a
    `site_*` lemma (that would trip the discipline gate / be unsound).  The row
    is a drop-in for the hand `*Seg_run` idiom (model:
    `EnvDefSeg.capComputeSeg_run`): its conclusion is the landed `∃ σ2 i2, Steps
    … ∧ PC = calleeEntry ∧ x1 = link ∧ writeLog-mem ∧ ABI-frame`, NOT a `True`
    stub.  `calleeEntry` = the callee entry PC; `link` = span_end + 4 (the jal's
    return address)."""
    name = a["name"]
    seg = name + "Seg"
    pins = a["pins"]
    pnames = " ".join(n for _, n in pins)
    Ldecl = f"{name}L {pnames}".strip()
    Lapp = f"({Ldecl})" if pins else name + "L"
    pbind = "".join(f" ({n} : BitVec 64)" for _, n in pins)
    keylist = "[" + ", ".join(str(k) for k in keys) + "]"
    calleeS = a["callee"] or "callee"
    entryS = lib.bv64(a["entry"])
    calleeE = lib.bv64(a["callee_pc"])
    linkS = lib.bv64(a["span_end"] + 4)
    E(f"/-! ## The jal seam is Shape-D (`bridgeOfSeg`)")
    E(f"")
    E(f"The `{name}` body ends in `jal {calleeS}` (a CALL — deliberately outside "
      f"`TKind`).  The straight-line body run + the ABI callee-saved frame are "
      f"FREE via `bridgeOfSeg`; the ONLY region-specific input is the jal seam's "
      f"`JalStep` (the callee entry obs, packaged by `jalStep_of_obs` from the "
      f"region's `site_{a['span_end']:08x}_*` lemma).  That seam is threaded as a "
      f"NAMED residual `hjalSeam` — it is NOT fabricated here (a hand `site_*` "
      f"would trip the discipline gate).  The row shape mirrors "
      f"`EnvDefSeg.capComputeSeg_run`. -/")
    E("")
    E(f"/-- **`{name}Bridge`** — the `{name}` body ≫ `jal {calleeS}` bridge, via "
      f"`bridgeOfSeg`.  The seg run + ABI frame are FREE; `hfacts` (the memory "
      f"chain-facts, one `chain_facts` call at the caller) and `hjalSeam` (the "
      f"call-seam `JalStep` off the callee `site_*` obs) are the only "
      f"region-specific residuals.  Conclusion: parked at the callee entry "
      f"`{calleeE}` with link `{linkS}`, memory = the seg write-log, ABI frame "
      f"preserved. -/")
    E(f"theorem {name}Bridge")
    E(f"    (σ : MState) (i u : Nat) (vminstret : BitVec 64){pbind}")
    E(f"    (m0 : Std.ExtHashMap Nat (BitVec 8))")
    E(f"    (hG : GoodState σ)")
    E(f"    (hpc : σ.regs.get? Register.PC = some ({entryS} : BitVec 64))")
    E(f"    (hminstret : σ.regs.get? Register.minstret = some vminstret)")
    E(f"    (hmem : σ.mem = m0)")
    E(f"    (hL : GHolds σ {Lapp})")
    E(f"    (hfacts : ChainFacts σ.mem σ.mem {Lapp} [] {seg})")
    E(f"    (hi : i < 2)")
    E(f"    -- output-regs key hygiene: the keys are value-free, but they mention the")
    E(f"    -- pins as values, so they stall `decide` under the pin binders; the")
    E(f"    -- caller closes each with ONE `decide` (see observations "
      f"`keys-decides-per-seg`).")
    E(f"    (hKeysOut : KeysOK (keysG (evalBlocks {seg} (SegEvalState.init {Lapp} [])).regs))")
    E(f"    (hRaOut : KeysAvoidRa (evalBlocks {seg} (SegEvalState.init {Lapp} [])).regs)")
    E(f"    (hjalSeam : ∀ (σ' : MState) (i' u' : Nat),")
    E(f"      GoodState σ' → i' < 2 →")
    E(f"      σ'.regs.get? Register.PC = some")
    E(f"        (evalBlocksPC {entryS} (SegEvalState.init {Lapp} []) {seg}) →")
    E(f"      (∃ w, σ'.regs.get? Register.minstret = some w) →")
    E(f"      σ'.mem = writeLog m0 (evalBlocks {seg} (SegEvalState.init {Lapp} [])).log →")
    E(f"      GHolds σ' (evalBlocks {seg} (SegEvalState.init {Lapp} [])).regs →")
    E(f"      JalStep {calleeE} {linkS} σ' i' u') :")
    E(f"    ∃ (σ2 : MState) (i2 : Nat),")
    E(f"      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel {seg} + 1⟩ ∧ i2 < 2 ∧ GoodState σ2 ∧")
    E(f"      σ2.regs.get? Register.PC = some ({calleeE} : BitVec 64) ∧")
    E(f"      σ2.regs.get? Register.x1 = some ({linkS} : BitVec 64) ∧")
    E(f"      (∃ w, σ2.regs.get? Register.minstret = some w) ∧")
    E(f"      GHolds σ2 (evalBlocks {seg} (SegEvalState.init {Lapp} [])).regs ∧")
    E(f"      σ2.mem = writeLog m0 (evalBlocks {seg} (SegEvalState.init {Lapp} [])).log ∧")
    E(f"      (∀ R, Vsa.Alloc.AbiPreserved R = true → σ2.regs.get? R = σ.regs.get? R) := by")
    E(f"  apply bridgeOfSeg {seg} {Lapp} []")
    E(f"    σ i u ({entryS}) ({calleeE}) ({linkS}) vminstret m0")
    E(f"    hG hpc hminstret hmem hL")
    if len(keys) <= 1:
        E(f"    (by show KeysOK {keylist}; decide)")
    else:
        E(f"    (by have h : keysG {Lapp} = {keylist} := rfl")
        E(f"        rw [h]; decide)")
    E(f"    hfacts hi")
    if len(keys) <= 1:
        E(f"    (by show ChainOK {entryS} {keylist} {seg}; decide)")
    else:
        E(f"    (by have h : keysG {Lapp} = {keylist} := rfl")
        E(f"        rw [h]; show ChainOK {entryS} {keylist} {seg}; decide)")
    E(f"    (by show WrChainAvoidAbi {seg}; decide)")
    E(f"    hKeysOut hRaOut")
    E(f"  exact hjalSeam")
    E("")
    E(f"#print axioms {name}Bridge")
    E("")


def compile_arm(arm_path, out_path):
    d = lib.load_arm(arm_path)
    a = norm_arm(d)
    di = lib.parse_disasm()
    idx = lib.DecodeIndex()
    blocks, end_pc = build_body(a, di, idx)

    E = lib.Emitter()
    default_imports = ["Vsa.Sim.DeriveCaseRow", "Vsa.Sim.ChainFactsTac"]
    imports = a["imports"] or default_imports
    doc = (
        f"# `{a['name']}` — GENERATED seg-layer arm (scripts/genseg.py)\n\n"
        f"{a['doc']}\n\n"
        f"Compiled from an arm description: span "
        f"`0x{a['entry']:08x} → 0x{a['span_end']:08x}` "
        f"({a['terminator']}-terminated).  The `#derive_case` seg carries the "
        f"whole `Steps` chain / computed end-PC / write-log; the row's ONLY "
        f"kernel obligation is the single `ChainOK` `decide`.  Matches the "
        f"`EnvDefSeg`/`EnvDefBridges4` idiom.\n\n"
        f"GENERATED by `scripts/genseg.py`.  DO NOT hand-edit.\n"
        f"NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.")
    E.house_header(
        imports, doc, namespace=a["namespace"],
        opens=[
            "open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa",
            "open Register",
            "open Vsa.Machine (MState Config Step Steps)",
            "open Vsa.Logic (Triple)",
        ],
        options=["set_option maxHeartbeats 800000",
                 "set_option maxRecDepth 100000"],
        notation_specst=False)

    emit_seg(E, a, blocks)
    keys = emit_L(E, a)
    if a["terminator"] == "jal":
        emit_jal_row(E, a, end_pc, keys)
    else:
        emit_post_and_row(E, a, end_pc, keys)

    E(f"end {a['namespace']}")
    E.write(out_path)
    print(f"wrote {out_path}")
    print(f"  arm={a['name']} span=0x{a['entry']:08x}..0x{a['span_end']:08x} "
          f"term={a['terminator']} pins={keys} end_pc=0x{end_pc:08x}")


def main():
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("arm", nargs="?", help="arm description (.toml or .tsv)")
    ap.add_argument("-o", "--output", help="output .lean path")
    ap.add_argument("--spec", action="store_true",
                    help="print the arm-description format spec and exit")
    args = ap.parse_args()
    if args.spec or not args.arm:
        print(ARM_SPEC)
        return 0
    out = args.output
    if not out:
        d = lib.load_arm(args.arm)
        name = d["name"]
        out = os.path.join(ROOT, "Vsa/Sim/rows", lib.cap(name) + "Gen.lean")
    compile_arm(args.arm, out)
    return 0


if __name__ == "__main__":
    sys.exit(main())
