#!/usr/bin/env python3
"""gen_stagepre.py — the 3-step eval-arm-head stagePre-class emitter.

    python3 scripts/gen_stagepre.py <arm.toml> [-o OUT.lean] [--verify]

Emits the WHOLE `rows/<Name>ArmStagePre.lean` file (the 3-step `ld+addi+sd → jal`
arm-head cut) from a 5-tuple TOML row.  This is the class the wave-37 audit found
was CLONED verbatim twice (`rows/AssignArmStagePre.lean`, `rows/CallArmStagePre.lean`)
and once before that (`StagePreSuppliers2.blockB_logical_stagePre`), differing ONLY in
the 5-tuple

  { armPC0 (first head PC; the 4 head PCs are armPC0, +4, +8, +12),
    operand-load offset (`ld a2,OFF(a2)` — 16 for assign, 8 for call),
    buffer offset (`addi a0,sp,BUF`),
    the jal target imm / jal decode word,
    callee bundle (`UnaryArmCallee` etc.) }

plus the node-level naming { node pattern, node binders, child expr var, operand-ptr
var, field/theorem-name stem }.

Every OTHER literal is DERIVED:
  * the 4 head PCs               = armPC0 + {0,4,8,12}
  * the ld/addi/store/jal decode words + their LE byte splits   = read from disasm
  * the DecodeTable.Batch imports    = looked up per decode word in DecodeTable/
  * the 21-bit jal J-immediate       = decoded from the jal word
  * the frame sub-constant           = 1088 - BUF
  * the `aExpr + OFF` payload bound   = OFF + 8

This file supplies (per row):
  * `site_<pc0>_<sfx>` .. `site_<pc0+12>_<sfx>` — the four per-PC StepObs site lemmas
  * `blockB_<stem>_stagePre`   — the arm-head cut (LandedN 3, second factor)
  * `<Stem>ArmDispatch` + `<field>_field_of_dispatch` — the EvalChildStages.<field>
    composer (modulo the standing EvalEntry→ArmEntryK dispatch residual)

SELF-VERIFICATION (MANDATORY, --verify): after writing, run `lake env lean` on the
emitted file and grep `#print axioms` for `sorryAx`; on elaboration failure HARD-ERROR
with the Lean output; never leave a broken file staged.

NO `sorry`/`axiom`/`native_decide`/`bv_decide` in the output; no Mathlib; no
`maxHeartbeats` bump beyond the standing stagePre budget.
"""

import argparse
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genseg import lib

ROOT = lib.ROOT
DECODE_DIR = os.path.join(ROOT, "Vsa", "Sim", "DecodeTable")


STAGEPRE_SPEC = """\
stagePre 3-step arm-head DESCRIPTION FORMAT (.toml)
===================================================

  name       = "assign"            # theorem stem: blockB_<name>_stagePre etc.
  namespace  = "Vsa.Sim"
  armPC0     = 0x8000347c           # the FIRST head PC (ld). +4 addi, +8 sd, +12 jal.
  operand_off= 16                   # `ld a2,OFF(a2)` immediate (bytes; 16=assign 8=call)
  buf_off    = 240                  # `addi a0,sp,BUF` immediate (bytes; sp+BUF sret buf)
  callee     = "UnaryArmCallee"     # the JalPreBundle callee bundle name
  node_pat   = ".assign x e"        # the Expr constructor pattern
  node_binders = "(x : String) (e : Expr)"   # its bound variables (theorem binders)
  child      = "e"                  # the child expr the sub-call evaluates
  operand    = "aRhs"              # the operand-pointer ghost name (aRhs/aClo)
  sfx        = "as"                 # the site-lemma suffix (site_<pc>_<sfx>)
  doc        = "One-line summary of the arm."
"""


def _batch_for_word(word):
    """Grep DecodeTable/ for `decode_<word>` and return its Batch module name."""
    needle = f"decode_{word}"
    for root, _dirs, files in os.walk(DECODE_DIR):
        for fn in files:
            if not fn.endswith(".lean"):
                continue
            p = os.path.join(root, fn)
            with open(p) as f:
                txt = f.read()
            if re.search(rf"\bdecode_{word}\b", txt):
                return "Vsa.Sim.DecodeTable." + fn[:-len(".lean")]
    raise SystemExit(f"decode_{word} not found under {DECODE_DIR} — is the word tabled?")


def _jimm21(word):
    """The 21-bit RISC-V J-type immediate of a `jal` word (as an int)."""
    imm20 = (word >> 31) & 1
    imm10_1 = (word >> 21) & 0x3FF
    imm11 = (word >> 20) & 1
    imm19_12 = (word >> 12) & 0xFF
    return ((imm20 << 20) | (imm19_12 << 12) | (imm11 << 11) | (imm10_1 << 1)) & 0x1FFFFF


def norm(d):
    a = {}
    a["name"] = d["name"]
    a["namespace"] = d.get("namespace", "Vsa.Sim")
    a["armPC0"] = lib.hexint(d["armPC0"])
    a["operand_off"] = int(d["operand_off"])
    a["buf_off"] = int(d["buf_off"])
    a["callee"] = d["callee"]
    a["node_pat"] = d["node_pat"]
    a["node_binders"] = d["node_binders"]
    a["child"] = d["child"]
    a["operand"] = d["operand"]
    a["sfx"] = d["sfx"]
    a["doc"] = d.get("doc", "")
    # the four head PCs
    a["pcs"] = [a["armPC0"] + 4 * k for k in range(4)]
    # the decode words for each head instruction, read from disasm
    dis = lib.parse_disasm()
    words = []
    for pc in a["pcs"]:
        instr = dis.get(pc)
        if instr is None:
            raise SystemExit(f"disasm has no line at 0x{pc:08x}")
        words.append(instr.word if hasattr(instr, "word") else instr["word"])
    a["ld_word"], a["addi_word"], a["sd_word"], a["jal_word"] = words
    # jal J-immediate (21-bit) + link
    a["jal_imm"] = _jimm21(a["jal_word"])
    a["jal_link"] = a["pcs"][3] + 4
    # frame sub-constant
    a["sub_const"] = 1088 - a["buf_off"]
    # payload bound: aExpr + (operand_off + 8)
    a["pay_hi"] = a["operand_off"] + 8
    # batch imports (dedup, preserve order)
    imports = []
    for w in (a["ld_word"], a["addi_word"], a["sd_word"], a["jal_word"]):
        b = _batch_for_word(f"{w:08x}")
        if b not in imports:
            imports.append(b)
    a["batch_imports"] = imports
    return a


# ------------------------------------------------------------------------------
# The three site lemmas + the jal site + blockB_<stem>_stagePre + composer.
# Rendered from `a` via .format on {PLACEHOLDER}.  This is the assign/call golden
# text with the 5-tuple + naming punched out.  All literals not in a placeholder
# are FIXED across the class (verified by regenerating both twins).
# ------------------------------------------------------------------------------

def emit(a):
    name = a["name"]
    ns = a["namespace"]
    sfx = a["sfx"]
    Stem = lib.cap(name)
    pc0, pc1, pc2, pc3 = a["pcs"]
    OFF = a["operand_off"]           # 16 / 8
    BUF = a["buf_off"]               # 240 / 96
    SUB = a["sub_const"]             # 848 / 992
    PAY = a["pay_hi"]                # 24 / 16
    ld_w, addi_w, sd_w, jal_w = a["ld_word"], a["addi_word"], a["sd_word"], a["jal_word"]
    ld_by = lib.le_bytes(ld_w)
    addi_by = lib.le_bytes(addi_w)
    sd_by = lib.le_bytes(sd_w)
    jal_by = lib.le_bytes(jal_w)
    imm = a["jal_imm"]
    child = a["child"]
    oper = a["operand"]

    def hx3(n):   # 12-bit hex immediate literal like 0x010
        return f"0x{n:03x}"

    E = lib.Emitter()
    # ------- imports -------
    for m in a["batch_imports"]:
        E(f"import {m}")
    # also the two stagePre-supplier + combinator modules (fixed)
    # (put them first so ordering is stable; re-emit header cleanly)
    E.lines = []
    E("import Vsa.Sim.StagePreSuppliers2")
    E("import Vsa.Sim.EvalChildFieldCombinator")
    for m in a["batch_imports"]:
        E(f"import {m}")
    E("")
    # ------- doc -------
    E("/-!")
    E(f"# `{Stem}ArmStagePre` — GENERATED (scripts/gen_stagepre.py)")
    E("")
    E(f"The 3-step `ld a2,{OFF}(a2)` ≫ `addi a0,sp,{BUF}` ≫ `sd a3,0(sp)` ≫ `jal eval_expr`")
    E(f"arm-head cut for the `{a['node_pat']}` arm (first head PC `{lib.bv64(pc0)[:-4]}`).")
    E(f"{a['doc']}")
    E("")
    E("This is a member of the wave-37 `blockB_*_stagePre` 3-step class (twins")
    E("`AssignArmStagePre`/`CallArmStagePre`, ancestor `blockB_logical_stagePre`),")
    E("differing only in the 5-tuple {armPC, operand-load offset, buffer offset, jal")
    E("target imm, callee bundle} + node naming.  GENERATED — DO NOT hand-edit;")
    E("regenerate via `gen_stagepre.py`.  See observation")
    E("`assign-call-logical-stagepre-uniform`.")
    E("")
    E("NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib; no `maxHeartbeats`")
    E("bump.  Axioms of every theorem ⊆ {propext, Classical.choice, Quot.sound}.")
    E("-/")
    E("")
    E("open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa")
    E("open Register")
    E("open Sail.ConcurrencyInterfaceV1.PreSail")
    E("open Vsa.Machine (MState Config Step Steps StepsN)")
    E("open Vsa.Logic")
    E("open Vsa.RuntimeRepr")
    E("open Vsa.MemRepr")
    E("open Vsa.While")
    E("open Vsa.Alloc")
    E("open Vsa.Sim.Code")
    E("open Vsa.Sim.ApproxArmReseat")
    E("")
    E(f"namespace {ns}")
    E("")
    E("set_option maxHeartbeats 8000000")
    E("set_option maxRecDepth 1000000")
    E("set_option linter.unusedVariables false")
    E("")
    E(f"-- discipline: allow(R7-conj-tower-def) GENERATED 3-step stagePre-class member; the")
    E(f"-- ∃-towers are the ESTABLISHED `JalPreBundle` landing bundle + the")
    E(f"-- `blockB_{name}_stagePre`/`{Stem}ArmDispatch` entry bundle mirroring the landed")
    E(f"-- `blockB_logical_stagePre`; consumed through `evalChildField_of_blockA_stage` /")
    E(f"-- `landedN_eentryC_of_preBundle`.")
    E("")

    # ======================= §1 site lemmas =======================
    E("/-! ## §1. The four arm-head site lemmas (GENERATED stagePre-class members). -/")
    E("")
    # ---- site 0: ld a2,OFF(a2) ----
    E(f"/-- {lib.bv64(pc0)[:-4]}: `ld x12,{hx3(OFF)}(x12)` (a2 := expr operand at child[{OFF}]). -/")
    E(f"-- discipline: allow(R1-site-battery) generated `JalPreBundle`-landing site lemma (grandfathered LogicalSites class); reflection layer cannot land the rich repr")
    E(f"theorem site_{pc0:08x}_{sfx} (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v12 : BitVec 64)")
    E(f"    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)")
    E(f"    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)")
    E(f"    (hminstret : σ.regs.get? Register.minstret = some vminstret)")
    E(f"    (hx12 : σ.regs.get? Register.x12 = some v12)")
    E(f"    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)")
    E(f"    (hpcv : pc = ({lib.bv64(pc0)} : BitVec 64))")
    E(f"    (hlo : 0x80000000 ≤ (v12 + sign_extend (m := 64) ({hx3(OFF)}#12)).toNat)")
    E(f"    (hhiram : (v12 + sign_extend (m := 64) ({hx3(OFF)}#12)).toNat + 8 ≤ 0x100000000)")
    E(f"    (hhtif : (v12 + sign_extend (m := 64) ({hx3(OFF)}#12)).toNat + 8 ≤ tohostAddr")
    E(f"      ∨ tohostAddr + 8 ≤ (v12 + sign_extend (m := 64) ({hx3(OFF)}#12)).toNat)")
    E(f"    (halign : (v12 + sign_extend (m := 64) ({hx3(OFF)}#12)).toNat % 8 = 0)")
    for k in range(8):
        plus = "" if k == 0 else f" + {k}"
        E(f"    (h{k} : σ.mem[(v12 + sign_extend (m := 64) ({hx3(OFF)}#12)).toNat{plus}]? = some b{k})")
    E(f"    (hi : i < 2) :")
    E(f"    ∃ (σ' : MState) (i' : Nat),")
    E(f"      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧")
    E(f"      σ'.mem = σ.mem ∧")
    E(f"      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12")
    E(f"        (sign_extend (m := 64)")
    E(f"          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by")
    E(f"  subst hpcv")
    E(f"  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_{pc0:08x} hmem")
    E(f"  exact stepObs_alu σ i u ({lib.bv64(pc0)}) vminstret ({lib.bv32(ld_w)})")
    E(f"    (instruction.LOAD ({hx3(OFF)}#12, regidx.Regidx 0x0c#5, regidx.Regidx 0x0c#5, false, 8))")
    E(f"    Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))")
    E(f"    ({ld_by[0]}) ({ld_by[1]}) ({ld_by[2]}) ({ld_by[3]})")
    E(f"    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)")
    E(f"    (by apply BitVec.eq_of_toNat_eq; decide)")
    E(f"    (Vsa.Sim.DecodeTable.decode_{ld_w:08x} (afterPrelude σ)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))")
    E(f"    (exec_ld σ ({lib.bv64(pc0)}) ({hx3(OFF)}#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0c#5)")
    E(f"      (sigma3_alu σ ({lib.bv64(pc0)}) Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))")
    E(f"      v12 b0 b1 b2 b3 b4 b5 b6 b7 hG")
    E(f"      (rX_bits_x12 _ v12")
    E(f"        (by rw [get?_afterNextPC σ ({lib.bv64(pc0)}) _ (by decide) (by decide)]; exact hx12))")
    E(f"      (wX_bits_x12 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))")
    E(f"      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)")
    E(f"    (by decide) (by decide) (by decide) (by decide) (by decide)")
    E(f"    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi")
    E("")
    # ---- site 1: addi a0,sp,BUF ----
    E(f"/-- {lib.bv64(pc1)[:-4]}: `addi x10,x2,{hx3(BUF)}` (a0 := sret buffer @sp+{BUF}). -/")
    E(f"-- discipline: allow(R1-site-battery) generated `JalPreBundle`-landing site lemma")
    E(f"theorem site_{pc1:08x}_{sfx} (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)")
    E(f"    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)")
    E(f"    (hminstret : σ.regs.get? Register.minstret = some vminstret)")
    E(f"    (hx2 : σ.regs.get? Register.x2 = some v2)")
    E(f"    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)")
    E(f"    (hpcv : pc = ({lib.bv64(pc1)} : BitVec 64)) (hi : i < 2) :")
    E(f"    ∃ (σ' : MState) (i' : Nat),")
    E(f"      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧")
    E(f"      σ'.mem = σ.mem ∧")
    E(f"      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10")
    E(f"        (v2 + sign_extend (m := 64) ({hx3(BUF)}#12))) := by")
    E(f"  subst hpcv")
    E(f"  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_{pc1:08x} hmem")
    E(f"  exact stepObs_alu σ i u ({lib.bv64(pc1)}) vminstret ({lib.bv32(addi_w)})")
    E(f"    (instruction.ITYPE ({hx3(BUF)}#12, regidx.Regidx 0x02#5, regidx.Regidx 0x0a#5, iop.ADDI))")
    E(f"    Register.x10 (v2 + sign_extend (m := 64) ({hx3(BUF)}#12))")
    E(f"    ({addi_by[0]}) ({addi_by[1]}) ({addi_by[2]}) ({addi_by[3]})")
    E(f"    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)")
    E(f"    (by apply BitVec.eq_of_toNat_eq; decide)")
    E(f"    (Vsa.Sim.DecodeTable.decode_{addi_w:08x} (afterPrelude σ)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))")
    E(f"    (execute_itype_addi_char ({hx3(BUF)}#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x0a#5) v2")
    E(f"      (afterNextPC (afterPrelude σ) ({lib.bv64(pc1)}))")
    E(f"      (sigma3_alu σ ({lib.bv64(pc1)}) Register.x10 (v2 + sign_extend (m := 64) ({hx3(BUF)}#12)))")
    E(f"      (rX_bits_x2 _ v2")
    E(f"        (by rw [get?_afterNextPC σ ({lib.bv64(pc1)}) _ (by decide) (by decide)]; exact hx2))")
    E(f"      (wX_bits_x10 _ (v2 + sign_extend (m := 64) ({hx3(BUF)}#12))))")
    E(f"    (by decide) (by decide) (by decide) (by decide) (by decide)")
    E(f"    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi")
    E("")
    # ---- site 2: sd a3,0(sp) ----
    E(f"/-- {lib.bv64(pc2)[:-4]}: `sd x13,0x0(x2)` (spill env across the sub-call). -/")
    E(f"-- discipline: allow(R1-site-battery) generated `JalPreBundle`-landing site lemma")
    E(f"theorem site_{pc2:08x}_{sfx} (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v13 : BitVec 64)")
    E(f"    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)")
    E(f"    (hminstret : σ.regs.get? Register.minstret = some vminstret)")
    E(f"    (hx2 : σ.regs.get? Register.x2 = some v2)")
    E(f"    (hx13 : σ.regs.get? Register.x13 = some v13)")
    E(f"    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)")
    E(f"    (hpcv : pc = ({lib.bv64(pc2)} : BitVec 64))")
    E(f"    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)")
    E(f"    (hahiram : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)")
    E(f"    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)")
    E(f"    (haalign : (v2 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :")
    E(f"    ∃ (σ' : MState) (i' : Nat),")
    E(f"      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧")
    E(f"      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) ({lib.bv64(pc2)})).mem")
    E(f"        (v2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v13) ∧")
    E(f"      ReadsLikePost σ' (sigmaPost_store σ pc vminstret")
    E(f"        (writeMap8 (afterNextPC (afterPrelude σ) ({lib.bv64(pc2)})).mem (v2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v13))) := by")
    E(f"  subst hpcv")
    E(f"  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_{pc2:08x} hmem")
    E(f"  exact stepObs_store σ i u ({lib.bv64(pc2)}) vminstret ({lib.bv32(sd_w)})")
    E(f"    (instruction.STORE (0x000#12, regidx.Regidx 0x0d#5, regidx.Regidx 0x02#5, 8))")
    E(f"    (writeMap8 (afterNextPC (afterPrelude σ) ({lib.bv64(pc2)})).mem (v2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v13))")
    E(f"    ({sd_by[0]}) ({sd_by[1]}) ({sd_by[2]}) ({sd_by[3]})")
    E(f"    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)")
    E(f"    (by apply BitVec.eq_of_toNat_eq; decide)")
    E(f"    (Vsa.Sim.DecodeTable.decode_{sd_w:08x} (afterPrelude σ)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))")
    E(f"    (exec_sd_val σ ({lib.bv64(pc2)}) (0x000#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x02#5)")
    E(f"      v2 v13 hG")
    E(f"      (rX_bits_x2 _ v2")
    E(f"        (by rw [get?_afterNextPC σ ({lib.bv64(pc2)}) _ (by decide) (by decide)]; exact hx2))")
    E(f"      (rX_bits_x13 _ v13")
    E(f"        (by rw [get?_afterNextPC σ ({lib.bv64(pc2)}) _ (by decide) (by decide)]; exact hx13))")
    E(f"      halo hahiram hahiwin haalign)")
    E(f"    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi")
    E("")
    # ---- site 3: jal ----
    E(f"/-- {lib.bv64(pc3)[:-4]}: `jal x1,0x80003164` (link `x1 := {lib.bv64(a['jal_link'])[:-4]}`). THE recursive sub-call. -/")
    E(f"-- discipline: allow(R1-site-battery) generated `JalPreBundle`-landing site lemma")
    E(f"theorem site_{pc3:08x}_{sfx} (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)")
    E(f"    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)")
    E(f"    (hminstret : σ.regs.get? Register.minstret = some vminstret)")
    E(f"    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)")
    E(f"    (hpcv : pc = ({lib.bv64(pc3)} : BitVec 64)) (hi : i < 2) :")
    E(f"    ∃ (σ' : MState) (i' : Nat),")
    E(f"      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧")
    E(f"      σ'.mem = σ.mem ∧")
    E(f"      ReadsLikePost σ' (sigmaPost_jal σ pc vminstret (0x{imm:x}#21) Register.x1 (BitVec.addInt pc 4)) := by")
    E(f"  subst hpcv")
    E(f"  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_{pc3:08x} hmem")
    E(f"  refine stepObs_jal σ i u ({lib.bv64(pc3)}) vminstret ({lib.bv32(jal_w)}) (0x{imm:x}#21)")
    E(f"    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt ({lib.bv64(pc3)}) 4)")
    E(f"    ({jal_by[0]}) ({jal_by[1]}) ({jal_by[2]}) ({jal_by[3]})")
    E(f"    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)")
    E(f"    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)")
    E(f"    (Vsa.Sim.DecodeTable.decode_{jal_w:08x} (afterPrelude σ)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)")
    E(f"      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))")
    E(f"    (by decide)")
    E(f"    (by decide) (by decide) (by decide) (by decide) (by decide) ?_ hi")
    E(f"  exact wX_bits_x1 _ (BitVec.addInt ({lib.bv64(pc3)}) 4)")
    E("")

    # ======================= §2 blockB_<name>_stagePre =======================
    _emit_blockB(E, a, name, sfx, pc0, pc1, pc2, pc3, OFF, BUF, SUB, PAY, imm, child, oper, Stem)
    # ======================= §3 dispatch + composer =======================
    _emit_composer(E, a, name, OFF, PAY, child, oper, Stem)

    E(f"end {ns}")
    return E


def _emit_entry_bundle(E, a, indent, OFF, PAY, child, oper, out_field):
    """The ArmEntryK-plus-recursive-extras entry bundle (shared by the theorem hpre
    and the dispatch Mid post).  `out_field` = the sailOutput field expression."""
    I = indent
    E(f"{I}ArmEntryK {a['_g']} N A SL φf φc st ({lib.bv64(a['pcs'][0])}) {a['callee']} ({a['node_pat']})")
    E(f"{I}  sp {a['_r']} sret aExpr aIn v8 v9 v18 {out_field} m0 ment {a['_c']} ∧")
    E(f"{I}{a['_c']}.σ.regs.get? Register.x11 = some aIn ∧")
    E(f"{I}{a['_c']}.σ.regs.get? Register.x13 = some aEnv3 ∧")
    E(f"{I}(∀ R : Register, AbiPreservedNoise R → {a['_c']}.σ.regs.get? R = gpre R) ∧")
    E(f"{I}(∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧")
    E(f"{I}read64 ment (aExpr.toNat + {OFF}) = some {oper}.toNat ∧")
    E(f"{I}(∀ m' : Mem,")
    E(f"{I}  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m'[a]?) →")
    E(f"{I}  ExprRepr m' {oper}.toNat {child}) ∧")
    E(f"{I}aExpr.toNat + {PAY} ≤ 0x100000000 ∧")
    E(f"{I}{oper}.toNat % 8 = 0 ∧")
    E(f"{I}0x80000000 ≤ {oper}.toNat ∧ {oper}.toNat + 16 ≤ 0x100000000 ∧")
    E(f"{I}tohostAddr + 16 ≤ {oper}.toNat ∧")
    E(f"{I}({oper}.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ {oper}.toNat) ∧")
    E(f"{I}SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧")
    E(f"{I}SL.hi ≤ 0x100000000 ∧")
    E(f"{I}(sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧")
    E(f"{I}((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧")
    E(f"{I}((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧")
    E(f"{I}(A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧")
    E(f"{I}(A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)")


def _emit_blockB(E, a, name, sfx, pc0, pc1, pc2, pc3, OFF, BUF, SUB, PAY, imm, child, oper, Stem):
    hOFF = f"haddr{OFF}"
    hsub = f"hsub{SUB}"
    hOFFbv = f"h{OFF}"
    E(f"/-! ## §2. `blockB_{name}_stagePre` — the arm-head → `JalPreBundle` cut. -/")
    E("")
    E(f"/-- **The {a['node_pat']} arm-head → `JalPreBundle` cut** (LandedN 3). -/")
    E(f"theorem blockB_{name}_stagePre")
    E(f"    (gouter gpre : (R : Register) → Option (RegisterType R))")
    E(f"    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)")
    E(f"    (st : Vsa.While.St) (d : Nat) (env : Addr) {a['node_binders']}")
    E(f"    (sp r sret aExpr aIn {oper} aEnv3 : BitVec 64) (v8 v9 v18 : BitVec 64)")
    E(f"    (out0 : Array String) (m0 : Mem)")
    E(f"    (c : Config)")
    E(f"    (hpre : ∃ ment,")
    # entry bundle for the theorem: config c, g=gouter, r=r, out0 literal
    a["_g"], a["_r"], a["_c"] = "gouter", "r", "c"
    _emit_entry_bundle_theorem(E, a, OFF, PAY, child, oper)
    E(f"    LandedN 3 c (fun c' => JalPreBundle {child} c' st d env) := by")
    E(f"  obtain ⟨ment, hArm, hx11, hx13, hgframe, hg8, hg18, hpay, hexprSurv, hexprHi,")
    E(f"    hopAl, hopLo, hopHi, hopWin, hopStk,")
    E(f"    hsproom, hspSLhi, hsp16, hSLhiRam,")
    E(f"    hcodeStk, hviStk, htableStk, harenaStk, harenaCode⟩ := hpre")
    E(f"  obtain ⟨hG, htick, hpc, ha0, hs1, ha2, hsp, hra, ⟨vmi, hmi⟩, hout, hmem, hcode, hviCode,")
    E(f"    hexpr, houtStr, hexprAl, hexprLo, hexprHi', hexprWin,")
    E(f"    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,")
    E(f"    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,")
    E(f"    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,")
    E(f"    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl,")
    E(f"    _hAEx11, _hAEx8, _hAEx18⟩ := hArm")
    E(f"  have htoh : tohostAddr = 0x8001ad00 := rfl")
    E(f"  obtain ⟨hviInt, hviSlot⟩ : Value_intLoaded ment ∧ IntSlotPinned ment := hviCode")
    E(f"  have {hOFFbv} : (sign_extend (m := 64) (0x{OFF:03x}#12) : BitVec 64) = {OFF}#64 := by")
    E(f"    apply BitVec.eq_of_toNat_eq; decide")
    E(f"  have {hOFF} : (aExpr + sign_extend (m := 64) (0x{OFF:03x}#12)).toNat = aExpr.toNat + {OFF} := by")
    E(f"    rw [{hOFFbv}, BitVec.toNat_add]")
    E(f"    have hv : ({OFF}#64 : BitVec 64).toNat = {OFF} := by decide")
    E(f"    rw [hv]; omega")
    E(f"  have {hsub} : ((sp - 1088#64) + sign_extend (m := 64) (0x{BUF:03x}#12)).toNat = sp.toNat - {SUB} :=")
    E(f"    spill_addr sp (0x{BUF:03x}#12) {SUB} (by decide) (by omega) hsp1088")
    E(f"  have hspill0 : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 :=")
    E(f"    spill_addr sp (0x000#12) 1088 (by decide) (by omega) hsp1088")
    E(f"  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hpsext⟩ :=")
    E(f"    spill_roundtrip_ee ment (aExpr.toNat + {OFF}) {oper} hpay")
    E(f"  -- ============ {lib.bv64(pc0)[:-4]}: ld a2,{OFF}(a2) → x12 := {oper} ============")
    E(f"  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=")
    E(f"    site_{pc0:08x}_{sfx} c.σ c.tick c.steps ({lib.bv64(pc0)}) vmi aExpr pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7")
    E(f"      hG hpc hmi ha2 (hmem ▸ hcode) rfl")
    E(f"      (by rw [{hOFF}]; omega) (by rw [{hOFF}]; omega)")
    E(f"      (by rw [{hOFF}, htoh]; right; omega) (by rw [{hOFF}]; omega)")
    E(f"      (by rw [{hOFF}, hmem]; exact hp0) (by rw [{hOFF}, hmem]; exact hp1)")
    E(f"      (by rw [{hOFF}, hmem]; exact hp2) (by rw [{hOFF}, hmem]; exact hp3)")
    E(f"      (by rw [{hOFF}, hmem]; exact hp4) (by rw [{hOFF}, hmem]; exact hp5)")
    E(f"      (by rw [{hOFF}, hmem]; exact hp6) (by rw [{hOFF}, hmem]; exact hp7) htick")
    E(f"  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'")
    E(f"  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem")
    E(f"  have hpc1 : σ1.regs.get? Register.PC = some ({lib.bv64(pc1)}) := by")
    E(f"    have := obs_alu_pc hobs1")
    E(f"    rwa [show BitVec.addInt ({lib.bv64(pc0)}) 4 = ({lib.bv64(pc1)} : BitVec 64) from by decide] at this")
    E(f"  have hx12_1 : σ1.regs.get? Register.x12 = some {oper} := by")
    E(f"    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)")
    E(f"    rwa [hpsext] at this")
    E(f"  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other' hobs1 Register.x10 (by decide) ha0")
    E(f"  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1")
    E(f"  have hx11_1 : σ1.regs.get? Register.x11 = some aIn := obs_alu_other' hobs1 Register.x11 (by decide) hx11")
    E(f"  have hx13_1 : σ1.regs.get? Register.x13 = some aEnv3 := obs_alu_other' hobs1 Register.x13 (by decide) hx13")
    E(f"  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp")
    E(f"  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1")
    E(f"  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout")
    E(f"  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode")
    E(f"  -- ============ {lib.bv64(pc1)[:-4]}: addi a0,sp,{BUF} → x10 := (sp-1088) + {BUF} ============")
    E(f"  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=")
    E(f"    site_{pc1:08x}_{sfx} σ1 i1 (c.steps + 1) ({lib.bv64(pc1)}) vmi1 (sp - 1088#64)")
    E(f"      hG1 hpc1 hmi1 hsp_1 hcode1 rfl hi1")
    E(f"  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'")
    E(f"  have hmem2e : σ2.mem = ment := by rw [hmem2]; exact hmem1e")
    E(f"  have hpc2 : σ2.regs.get? Register.PC = some ({lib.bv64(pc2)}) := by")
    E(f"    have := obs_alu_pc hobs2")
    E(f"    rwa [show BitVec.addInt ({lib.bv64(pc1)}) 4 = ({lib.bv64(pc2)} : BitVec 64) from by decide] at this")
    E(f"  have hx10_2 : σ2.regs.get? Register.x10")
    E(f"      = some ((sp - 1088#64) + sign_extend (m := 64) (0x{BUF:03x}#12)) :=")
    E(f"    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)")
    E(f"  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1")
    E(f"  have hx11_2 : σ2.regs.get? Register.x11 = some aIn := obs_alu_other' hobs2 Register.x11 (by decide) hx11_1")
    E(f"  have hx12_2 : σ2.regs.get? Register.x12 = some {oper} := obs_alu_other' hobs2 Register.x12 (by decide) hx12_1")
    E(f"  have hx13_2 : σ2.regs.get? Register.x13 = some aEnv3 := obs_alu_other' hobs2 Register.x13 (by decide) hx13_1")
    E(f"  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1")
    E(f"  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2")
    E(f"  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1")
    E(f"  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode")
    E(f"  -- ============ {lib.bv64(pc2)[:-4]}: sd a3,0(sp) → mcall := writeMap8 ment (sp-1088) (sdData_val aEnv3) ============")
    E(f"  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=")
    E(f"    site_{pc2:08x}_{sfx} σ2 i2 (c.steps + 1 + 1) ({lib.bv64(pc2)}) vmi2 (sp - 1088#64) aEnv3")
    E(f"      hG2 hpc2 hmi2 hsp_2 hx13_2 hcode2 rfl")
    E(f"      (by rw [hspill0]; omega) (by rw [hspill0]; omega)")
    E(f"      (by rw [hspill0, htoh]; omega) (by rw [hspill0]; omega) hi2")
    E(f"  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'")
    E(f"  let mcall : Mem := writeMap8 ment (sp.toNat - 1088) (sdData_val aEnv3)")
    E(f"  have hmcalldef : mcall = writeMap8 ment (sp.toNat - 1088) (sdData_val aEnv3) := rfl")
    E(f"  have hmem3e : σ3.mem = mcall := by")
    E(f"    rw [hmem3, hmcalldef]")
    E(f"    have hmi' : (afterNextPC (afterPrelude σ2) ({lib.bv64(pc2)})).mem = ment := by")
    E(f"      rw [mem_afterNextPC, mem_afterPrelude]; exact hmem2e")
    E(f"    rw [hmi', hspill0]")
    E(f"  have hpc3 : σ3.regs.get? Register.PC = some ({lib.bv64(pc3)}) := by")
    E(f"    have := obs_store_pc hobs3")
    E(f"    rwa [show BitVec.addInt ({lib.bv64(pc2)}) 4 = ({lib.bv64(pc3)} : BitVec 64) from by decide] at this")
    E(f"  have hx10_3 : σ3.regs.get? Register.x10")
    E(f"      = some ((sp - 1088#64) + sign_extend (m := 64) (0x{BUF:03x}#12)) :=")
    E(f"    obs_store_other' hobs3 Register.x10 (by decide) hx10_2")
    E(f"  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_store_other' hobs3 Register.x9 (by decide) hs1_2")
    E(f"  have hx11_3 : σ3.regs.get? Register.x11 = some aIn := obs_store_other' hobs3 Register.x11 (by decide) hx11_2")
    E(f"  have hx12_3 : σ3.regs.get? Register.x12 = some {oper} := obs_store_other' hobs3 Register.x12 (by decide) hx12_2")
    E(f"  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_store_other' hobs3 Register.x2 (by decide) hsp_2")
    E(f"  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3")
    E(f"  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_store]; exact hout2")
    E(f"  have hAgSpill : ∀ k : Nat, ¬ (sp.toNat - 1088 ≤ k ∧ k < sp.toNat - 1088 + 8) →")
    E(f"      mcall[k]? = ment[k]? := by")
    E(f"    intro k hk")
    E(f"    rw [hmcalldef, getElem_writeMap8_disjoint ment (sp.toNat - 1088) k (sdData_val aEnv3) (by omega)]")
    E(f"  have hcodeMcall : Eval_exprLoaded mcall :=")
    E(f"    loaded_eval_expr_agreeP ment mcall")
    E(f"      (fun a ha => (hAgSpill a (by rcases hcodeStk with h | h <;> omega)).symm) hcode")
    E(f"  have hviIntMcall : Value_intLoaded mcall :=")
    E(f"    loaded_value_int_agreeP ment mcall")
    E(f"      (fun a ha => (hAgSpill a (by rcases hviStk with h | h <;> omega)).symm) hviInt")
    E(f"  have hviSlotMcall : IntSlotPinned mcall := by")
    E(f"    obtain ⟨q0, q1, q2, q3⟩ := hviSlot")
    E(f"    refine ⟨?_, ?_, ?_, ?_⟩ <;>")
    E(f"      (rw [hAgSpill _ (by simp only [jumpTableBase] at *; rcases htableStk with h | h <;> omega)]; assumption)")
    E(f"  have hExprMcall : ExprRepr mcall {oper}.toNat {child} :=")
    E(f"    hexprSurv mcall (fun a ha => (hAgSpill a (by omega)).symm)")
    E(f"  have hStoreMcall : StoreRepr mcall N A φf φc st.store := by")
    E(f"    refine hstoreSurv mcall (fun k hk1 _ => ?_)")
    E(f"    exact (hAgSpill k (by omega)).symm")
    E(f"  have hStoreSurvMcall : ∀ m' : Mem,")
    E(f"      (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →")
    E(f"        mcall[k]? = m'[k]?) → StoreRepr m' N A φf φc st.store := by")
    E(f"    intro m' hag")
    E(f"    refine hstoreSurv m' (fun k hk1 hk2 => ?_)")
    E(f"    rw [← hag k hk1 hk2, hAgSpill k (by omega)]")
    E(f"  have hslotRaMcall : read64 mcall (sp.toNat - 8) = some r.toNat := by")
    E(f"    rw [read64_agreeP (P := fun k => sp.toNat - 8 ≤ k ∧ k < sp.toNat) (m := mcall) (m' := ment)")
    E(f"      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotRa")
    E(f"  have hslotS0Mcall : read64 mcall (sp.toNat - 16) = some v8.toNat := by")
    E(f"    rw [read64_agreeP (P := fun k => sp.toNat - 16 ≤ k ∧ k < sp.toNat - 8) (m := mcall) (m' := ment)")
    E(f"      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotS0")
    E(f"  have hslotS1Mcall : read64 mcall (sp.toNat - 24) = some v9.toNat := by")
    E(f"    rw [read64_agreeP (P := fun k => sp.toNat - 24 ≤ k ∧ k < sp.toNat - 16) (m := mcall) (m' := ment)")
    E(f"      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotS1")
    E(f"  have hslotS2Mcall : read64 mcall (sp.toNat - 32) = some v18.toNat := by")
    E(f"    rw [read64_agreeP (P := fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat - 24) (m := mcall) (m' := ment)")
    E(f"      (fun j hj => hAgSpill j (by omega)) (fun j hj => by omega)]; exact hslotS2")
    E(f"  have abi_ne' : ∀ {{X R : Register}}, AbiPreserved X = false → AbiPreserved R = true →")
    E(f"      (X == R) = false := by")
    E(f"    intro X R hX hR")
    E(f"    rcases hXR : (X == R) with _ | _")
    E(f"    · rfl")
    E(f"    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)")
    E(f"  have hframeB : ∀ R : Register, AbiPreservedNoise R → σ3.regs.get? R = gpre R := by")
    E(f"    intro R hR")
    E(f"    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR")
    E(f"    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩")
    E(f"    have h12R : (Register.x12 == R) = false := abi_ne' (by decide) hab")
    E(f"    have h10R : (Register.x10 == R) = false := abi_ne' (by decide) hab")
    E(f"    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=")
    E(f"      (hobs1.1 R hmcR hmtR hmipR).trans")
    E(f"        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h12R hnpcR hmiiR)")
    E(f"    have f2 : σ2.regs.get? R = σ1.regs.get? R :=")
    E(f"      (hobs2.1 R hmcR hmtR hmipR).trans")
    E(f"        (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR h10R hnpcR hmiiR)")
    E(f"    have f3 : σ3.regs.get? R = σ2.regs.get? R :=")
    E(f"      (hobs3.1 R hmcR hmtR hmipR).trans")
    E(f"        (get?_sigmaPost_store _ _ _ _ R hmiR hpcR hnpcR hmiiR)")
    E(f"    rw [f3, f2, f1]; exact hgframe R hR'")
    E(f"  refine ⟨3, ⟨σ3, i3, c.steps + 1 + 1 + 1⟩, Nat.le_refl _,")
    E(f"    StepsN.succ hstep1 (StepsN.succ hstep2 (StepsN.succ hstep3 (StepsN.zero _))), ?_⟩")
    E(f"  · exact ⟨gpre, N, A, SL, φf, φc, ({lib.bv64(pc3)}), ({lib.bv64(a['jal_link'])}), (0x{imm:x}#21),")
    E(f"      sp, r, sret, ((sp - 1088#64) + sign_extend (m := 64) (0x{BUF:03x}#12)), aIn, {oper},")
    E(f"      v8, v9, v18, out0, mcall,")
    E(f"      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide),")
    E(f"      (by apply BitVec.eq_of_toNat_eq; decide),")
    E(f"      (by decide),")
    E(f"      (fun σ i u vmiσ hGσ hpcσ hmiσ hcodeσ hiσ =>")
    E(f"        site_{pc3:08x}_{sfx} σ i u ({lib.bv64(pc3)}) vmiσ hGσ hpcσ hmiσ hcodeσ rfl hiσ),")
    E(f"      hG3, hi3, hpc3, hx10_3, hs1_3, hx11_3, hx12_3, hsp_3, ⟨vmi3, hmi3⟩, hout3, houtStr,")
    E(f"      hmem3e, hcodeMcall, hviIntMcall, hviSlotMcall, hExprMcall, hStoreMcall, hStoreSurvMcall,")
    E(f"      hframeB, ⟨hg8, hg18⟩,")
    E(f"      hslotRaMcall, hslotS0Mcall, hslotS1Mcall, hslotS2Mcall,")
    E(f"      hopAl, hopLo, hopHi, hopWin, hopStk,")
    E(f"      (by rw [{hsub}]; omega), (by rw [{hsub}]; omega), (by rw [{hsub}]; omega),")
    E(f"      hsproom, hspSLhi, hsp16, hsphi, hSLlo, hSLhiRam, hSLwin,")
    E(f"      hcodeStk, hviStk, htableStk, harenaStk, harenaCode⟩")
    E("")
    E(f"#print axioms blockB_{name}_stagePre")
    E("")


def _emit_entry_bundle_theorem(E, a, OFF, PAY, child, oper):
    """The theorem `hpre` entry-bundle body (config c, gouter, r, out0 literal)."""
    E(f"        ArmEntryK gouter N A SL φf φc st ({lib.bv64(a['pcs'][0])}) {a['callee']} ({a['node_pat']})")
    E(f"          sp r sret aExpr aIn v8 v9 v18 out0 m0 ment c ∧")
    E(f"        c.σ.regs.get? Register.x11 = some aIn ∧")
    E(f"        c.σ.regs.get? Register.x13 = some aEnv3 ∧")
    E(f"        (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = gpre R) ∧")
    E(f"        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧")
    E(f"        read64 ment (aExpr.toNat + {OFF}) = some {oper}.toNat ∧")
    E(f"        (∀ m' : Mem,")
    E(f"          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m'[a]?) →")
    E(f"          ExprRepr m' {oper}.toNat {child}) ∧")
    E(f"        aExpr.toNat + {PAY} ≤ 0x100000000 ∧")
    E(f"        {oper}.toNat % 8 = 0 ∧")
    E(f"        0x80000000 ≤ {oper}.toNat ∧ {oper}.toNat + 16 ≤ 0x100000000 ∧")
    E(f"        tohostAddr + 16 ≤ {oper}.toNat ∧")
    E(f"        ({oper}.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ {oper}.toNat) ∧")
    E(f"        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧")
    E(f"        SL.hi ≤ 0x100000000 ∧")
    E(f"        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧")
    E(f"        ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧")
    E(f"        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧")
    E(f"        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧")
    E(f"        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo)) :")


def _emit_composer(E, a, name, OFF, PAY, child, oper, Stem):
    ns_binders = a["node_binders"]
    node_pat = a["node_pat"]
    E(f"/-! ## §3. The `{name}` dispatch residual + field composer. -/")
    E("")
    E(f"/-- **The {name} dispatch residual** (the `blockA_{name}Arm` a row would produce)."
      f"  The `Mid` post is `blockB_{name}_stagePre`'s entry bundle. -/")
    E(f"def {Stem}ArmDispatch")
    E(f"    {ns_binders} (st : Vsa.While.St) (d : Nat) (env : Addr) (c : Config) : Prop :=")
    E(f"  ∀ (g : (R : Register) → Option (RegisterType R))")
    E(f"    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)")
    E(f"    (sp r0 sret aEnv aExpr : BitVec 64) (m0 : Mem),")
    E(f"    EvalEntry g N A SL φf φc st d env ({node_pat}) sp r0 sret aEnv aExpr m0 c →")
    E(f"    Triple (fun c'' => c'' = c)")
    E(f"      (fun c' => ∃ (gpre : (R : Register) → Option (RegisterType R))")
    E(f"        (aIn {oper} aEnv3 : BitVec 64) (v8 v9 v18 : BitVec 64),")
    E(f"        ∃ ment,")
    E(f"        ArmEntryK g N A SL φf φc st ({lib.bv64(a['pcs'][0])}) {a['callee']} ({node_pat})")
    E(f"          sp r0 sret aExpr aIn v8 v9 v18 c'.σ.sailOutput m0 ment c' ∧")
    E(f"        c'.σ.regs.get? Register.x11 = some aIn ∧")
    E(f"        c'.σ.regs.get? Register.x13 = some aEnv3 ∧")
    E(f"        (∀ R : Register, AbiPreservedNoise R → c'.σ.regs.get? R = gpre R) ∧")
    E(f"        (∃ w, gpre Register.x8 = some w) ∧ (∃ w, gpre Register.x18 = some w) ∧")
    E(f"        read64 ment (aExpr.toNat + {OFF}) = some {oper}.toNat ∧")
    E(f"        (∀ m' : Mem,")
    E(f"          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m'[a]?) →")
    E(f"          ExprRepr m' {oper}.toNat {child}) ∧")
    E(f"        aExpr.toNat + {PAY} ≤ 0x100000000 ∧")
    E(f"        {oper}.toNat % 8 = 0 ∧")
    E(f"        0x80000000 ≤ {oper}.toNat ∧ {oper}.toNat + 16 ≤ 0x100000000 ∧")
    E(f"        tohostAddr + 16 ≤ {oper}.toNat ∧")
    E(f"        ({oper}.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ {oper}.toNat) ∧")
    E(f"        SL.lo + 3264 ≤ sp.toNat ∧ sp.toNat ≤ SL.hi ∧ sp.toNat % 16 = 0 ∧")
    E(f"        SL.hi ≤ 0x100000000 ∧")
    E(f"        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧")
    E(f"        ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧")
    E(f"        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧")
    E(f"        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧")
    E(f"        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo))")
    E("")
    field = a["field"]
    E(f"/-- **The `EvalChildStages.{field}` field, machine-composed** (GENERATED). -/")
    E(f"theorem {field}_field_of_dispatch")
    E(f"    {ns_binders} (c : Config) (st : Vsa.While.St)")
    E(f"    (d : Nat) (env : Addr)")
    E(f"    (hDisp : {Stem}ArmDispatch {a['node_argnames']} st d env c)")
    E(f"    (hEE : EEntryC c st d env ({node_pat})) :")
    E(f"    LandedN 1 c (fun c' => JalPreBundle {child} c' st d env) := by")
    E(f"  obtain ⟨g, N, A, SL, φf, φc, sp, r0, sret, aEnv, aExpr, m0, hEntry⟩ := hEE")
    E(f"  refine evalChildField_of_blockA_stage (k := 3) (by omega)")
    E(f"    (hDisp g N A SL φf φc sp r0 sret aEnv aExpr m0 hEntry)")
    E(f"    (fun c' hMid => ?_) c rfl")
    E(f"  obtain ⟨gpre, aIn, {oper}, aEnv3, v8, v9, v18, ment, hArm, hx11, hx13, hgframe,")
    E(f"    hg8, hg18, hpay, hexprSurv, hexprHi, hopAl, hopLo, hopHi, hopWin,")
    E(f"    hsproom, hspSLhi, hsp16, hSLhiRam, hcodeStk, hviStk, htableStk,")
    E(f"    harenaStk, harenaCode⟩ := hMid")
    E(f"  exact blockB_{name}_stagePre g gpre N A SL φf φc st d env {a['node_argnames']}")
    E(f"    sp r0 sret aExpr aIn {oper} aEnv3 v8 v9 v18 c'.σ.sailOutput m0 c'")
    E(f"    ⟨ment, hArm, hx11, hx13, hgframe, hg8, hg18, hpay, hexprSurv, hexprHi,")
    E(f"      hopAl, hopLo, hopHi, hopWin, hsproom, hspSLhi, hsp16, hSLhiRam,")
    E(f"      hcodeStk, hviStk, htableStk, harenaStk, harenaCode⟩")
    E("")
    E(f"#print axioms {field}_field_of_dispatch")
    E("")


def verify(out_path, names):
    print(f"  [verify] lake env lean {out_path} …", flush=True)
    r = subprocess.run(["lake", "env", "lean", out_path],
                       cwd=ROOT, capture_output=True, text=True)
    out = (r.stdout or "") + (r.stderr or "")
    if r.returncode != 0:
        raise SystemExit(
            f"SELF-VERIFICATION FAILED — `lake env lean {out_path}` errored "
            f"(rc={r.returncode}).  Emitted file is broken; NOT reporting success.\n"
            f"--- Lean output ---\n{out}")
    if "sorryAx" in out:
        raise SystemExit(
            f"SELF-VERIFICATION FAILED — emitted file depends on `sorryAx`.\n"
            f"--- Lean output ---\n{out}")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    for line in out.splitlines():
        if "depends on axioms" in line:
            found = set(re.findall(r"(propext|Classical\.choice|Quot\.sound|sorryAx|[A-Za-z_][\w.]*Ax)",
                                   line.split(":", 1)[1]))
            bad = {x for x in found if x.endswith("Ax") or (x not in allowed and "Ax" in x)}
            if bad:
                raise SystemExit(f"SELF-VERIFICATION FAILED — unclean axioms {bad}\n{line}")
    print(f"  [verify] OK — green + axiom-clean.")
    return out


def main():
    ap = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("arm", nargs="?", help="stagePre arm description (.toml)")
    ap.add_argument("-o", "--output", help="output .lean path")
    ap.add_argument("--verify", action="store_true",
                    help="run lake env lean + axiom check after writing")
    ap.add_argument("--spec", action="store_true")
    args = ap.parse_args()
    if args.spec or not args.arm:
        print(STAGEPRE_SPEC)
        return 0
    d = lib.load_toml(args.arm)
    a = norm(d)
    # derive field name + node arg names from the node pattern
    a["field"] = d.get("field", a["name"] + "E")
    a["node_argnames"] = d["node_argnames"]
    out = args.output or os.path.join(
        ROOT, "Vsa/Sim/rows", lib.cap(a["name"]) + "ArmStagePre.lean")
    E = emit(a)
    E.write(out)
    print(f"wrote {out}")
    print(f"  name={a['name']} armPC0=0x{a['armPC0']:08x} operand_off={a['operand_off']} "
          f"buf_off={a['buf_off']} callee={a['callee']}")
    print(f"  head words: ld={a['ld_word']:08x} addi={a['addi_word']:08x} "
          f"sd={a['sd_word']:08x} jal={a['jal_word']:08x} jimm=0x{a['jal_imm']:x}")
    if args.verify:
        verify(out, [f"blockB_{a['name']}_stagePre", f"{a['field']}_field_of_dispatch"])
    return 0


if __name__ == "__main__":
    sys.exit(main())
