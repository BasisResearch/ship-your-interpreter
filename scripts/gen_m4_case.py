#!/usr/bin/env python3
"""gen_m4_case.py — emit the scaffolding of an M4 `EvalE.<case>` simulation file.

Usage:
    python3 scripts/gen_m4_case.py <case> [-t scripts/m4_cases.tsv] [-o out.lean]

Reads one row of scripts/m4_cases.tsv (the ground-truth table of per-case
parameters, reverse-engineered from the five PROVEN leaf cases int/str/bool/
null/var) and emits the fixed scaffolding of the case file:

  * imports / opens / set_options / namespace           (fully emitted)
  * the arm `jal <callee>` / `j 0x800033ec` sites       (fully emitted, proof included)
  * the payload-load site statement (ld/lw), if any     (statement emitted, body hole)
  * `loaded_<case>_writeMap8` statement                 (statement emitted, body hole)
  * `value_<case>_spec_full` statement                  (statement emitted, body hole)
  * `blockC_<case>`                                     (armTail style: fully emitted;
                                                         payload styles: entry + holes)
  * `<Case>SlotPinned` + `<case>_slot_kindPinned`       (fully emitted, proof included)
  * `Eval<Case>Entry` structure                         (fully emitted, null/bool shape)
  * `exprRepr_<case>_kind`                              (statement emitted, body hole)
  * `Eval<Case>SimGoal` + `eval<Case>Sim`               (composition emitted;
                                                         hcalleeSurv/hexprSurv holes)

Per-case content is emitted as `sorry`-marked holes tagged `-- PER-CASE:`.
The emitted file is a SCAFFOLD: it is NOT expected to compile as-is (the
holes must be filled), and generated skeletons must NOT be landed in Vsa/.
The point is that everything outside the holes is mechanical, byte-for-byte
identical in shape to the proven cases, and machine-generated from the row.

Modelled on EvalNullSim.lean (armTail style, tag 3) and EvalBoolSim.lean
(payload + inline-tail style, tag 2).
"""

import argparse
import csv
import sys


# ---------------------------------------------------------------- helpers

def le_bytes(word_hex: str):
    """'0xbc0ff0ef' -> ['0xef', '0xf0', '0x0f', '0xbc'] (LE byte order)."""
    w = int(word_hex, 16)
    return [f"0x{(w >> (8 * i)) & 0xFF:02x}" for i in range(4)]


def hex64(addr_hex: str) -> str:
    return f"{addr_hex}#64"


def addp4(addr_hex: str) -> str:
    return f"0x{int(addr_hex, 16) + 4:8x}"


def cap(s: str) -> str:
    return s[0].upper() + s[1:]


def load_row(tsv_path: str, case: str) -> dict:
    with open(tsv_path, newline="") as f:
        for row in csv.DictReader(f, delimiter="\t"):
            if row["case"] == case:
                return row
    sys.exit(f"error: case '{case}' not found in {tsv_path}")


def binders(row):
    """'b:Bool' -> [('b', 'Bool'), ...]; '-' -> []."""
    if row["value_binders"] == "-":
        return []
    return [tuple(b.split(":")) for b in row["value_binders"].split(",")]


# ---------------------------------------------------------------- sections

def emit_header(row):
    case = row["case"]
    C = cap(case)
    imports = [f"import {row['base_import']}"]
    if row["decode_imports"] != "-":
        imports += [f"import Vsa.Sim.DecodeTable.{b}"
                    for b in row["decode_imports"].split(":")]
    payload_note = ("no payload load; the arm is `jal`+`j` only"
                    if row["payload_insn"] == "-"
                    else f"payload `{row['payload_insn']} a1,8(a2)` then `jal`+`j`")
    return f"""{chr(10).join(imports)}

/-!
# Layer 4 — M4: the `{row['evale_ctor']}` simulation Triple (`{row['theorem']}`)

[GENERATED SCAFFOLD — gen_m4_case.py, row `{case}` of m4_cases.tsv.
Fill every `sorry` hole tagged `-- PER-CASE:` before landing; the fixed
scaffolding mirrors EvalNullSim.lean / EvalBoolSim.lean.]

The `{row['evale_ctor']}` arm (`ExprKind` tag `k = {row['tag']}`, arm PC
`{row['arm_pc']}`): {payload_note}; callee `{row['callee']}`
(`{row['callee_entry']}`, code `[{row['callee_code_lo']}, {row['callee_code_hi']})`).
Composition: `blockA_k (→ArmEntryK) ≫ {row['blockC']} (→PreEpilogueV) ≫ {row['epilogue']}
(→EvalExit)`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide` may remain when landed.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim
"""


def emit_payload_site(row):
    if row["payload_insn"] == "-":
        return ""
    pc = row["arm_pc"]
    word = row["payload_word"]
    b = le_bytes(word)
    insn = row["payload_insn"]
    nbytes = 4 if insn == "lw" else 8
    byte_vars = " ".join(f"b{i}" for i in range(nbytes))
    append_chain = "b" + ".append b".join(str(i) for i in range(nbytes - 1, -1, -1))
    pins = "\n".join(
        f"    (h{i} : σ.mem[(vexpr + sign_extend (m := 64) (0x008#12)).toNat"
        + (f" + {i}" if i else "") + f"]? = some b{i})"
        for i in range(nbytes))
    return f"""
/-! ## The payload-load site `{row['payload_site']}` (@{pc}, `{insn} a1,8(a2)`)

Mirrors the int arm's `site_80003408_ee` (`ld`) / the bool arm's
`site_80003420_ee` (`lw`); only the PC (and width) change. Word `{word}`. -/
theorem {row['payload_site']}
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vexpr : BitVec 64)
    ({byte_vars} : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some vexpr)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = ({hex64(pc)} : BitVec 64))
    (hlo : 0x80000000 ≤ (vexpr + sign_extend (m := 64) (0x008#12)).toNat)
    (hhiram : (vexpr + sign_extend (m := 64) (0x008#12)).toNat + {nbytes} ≤ 0x100000000)
    (hhtif : (vexpr + sign_extend (m := 64) (0x008#12)).toNat + {nbytes} ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vexpr + sign_extend (m := 64) (0x008#12)).toNat)
    (halign : (vexpr + sign_extend (m := 64) (0x008#12)).toNat % {nbytes} = 0)
{pins} (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (sign_extend (m := 64) ((({append_chain}) : BitVec (8 * {nbytes}))))) := by
  -- PER-CASE: mirror site_80003408_ee (`ld`, exec_ld) / site_80003420_ee (`lw`,
  -- exec_lw): subst hpcv; obtain byte pins from `eval_expr_at_{pc[2:]}`; apply
  -- stepObs_alu with decode_{word[2:]} and bytes {b[0]} {b[1]} {b[2]} {b[3]}.
  sorry
"""


def emit_jal_site(row):
    pc, word, imm = row["jal_pc"], row["jal_word"], row["jal_imm"]
    b = le_bytes(word)
    return f"""
/-- {pc}: `jal {row['callee']}` (imm {imm} → {row['callee_entry']}, rd=x1=ra). -/
theorem site_{pc[2:]}_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = ({hex64(pc)} : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) ({imm}#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_jal σ pc vminstret ({imm}#21) Register.x1 (BitVec.addInt pc 4)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_{pc[2:]} hmem
  exact stepObs_jal σ i u ({hex64(pc)}) vminstret ({word}#32) ({imm}#21)
    (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt ({hex64(pc)}) 4)
    ({b[0]}#8) ({b[1]}#8) ({b[2]}#8) ({b[3]}#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_{word[2:]} (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt (by decide) (by decide) (by decide) (by decide) (by decide)
    (wX_bits_x1 _ (BitVec.addInt ({hex64(pc)}) 4)) hi
"""


def emit_j_site(row):
    if row["j_pc"] == "-":
        return "\n-- PER-CASE: no shared `j 0x800033ec` site — this arm carries its own tail.\n"
    pc, word, imm = row["j_pc"], row["j_word"], row["j_imm"]
    b = le_bytes(word)
    return f"""
/-- {pc}: `j 0x800033ec` (jal x0, imm {imm} → epilogue). -/
theorem site_{pc[2:]}_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Eval_exprLoaded σ.mem)
    (hpcv : pc = ({hex64(pc)} : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) ({imm}#21)).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) ({imm}#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := eval_expr_at_{pc[2:]} hmem
  exact stepObs_j σ i u ({hex64(pc)}) vminstret ({word}#32) ({imm}#21)
    ({b[0]}#8) ({b[1]}#8) ({b[2]}#8) ({b[3]}#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_{word[2:]} (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi
"""


def emit_loaded_writemap8(row):
    case, C = row["case"], cap(row["case"])
    return f"""
/-! ## `{row['callee_loaded']}` survives an 8-byte spill write (blockA_k's `hcalleeSurv`) -/
theorem loaded_{case}_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ {row['callee_code_lo']} ∨ {row['callee_code_hi']} ≤ a8) (h : {row['callee_loaded']} mem) :
    {row['callee_loaded']} (writeMap8 mem a8 d) := by
  -- PER-CASE: unfold `{row['callee_loaded']}` + its chunk defs, then
  -- `refine ⟨?_, …⟩ <;> (rw [getElem_writeMap8_disjoint _ _ _ _ (by omega)]; simp_all only [])`
  -- (mirror loaded_null_writeMap8 / loaded_bool_writeMap8; arity = #pinned bytes).
  sorry
"""


def emit_spec_full(row):
    case = row["case"]
    if row["spec_full"] == "-":
        return ("\n-- PER-CASE: no `value_*` callee — this arm's callee contract "
                "(e.g. env_get) is supplied separately (see EvalVarSim.lean).\n")
    has_payload = row["payload_insn"] != "-"
    payload_bind = " vb" if has_payload else ""
    payload_pin = ("\n        c.σ.regs.get? Register.x11 = some vb ∧" if has_payload else "")
    C = cap(case)
    return f"""
/-! ## `{row['spec_full']}` — strengthened `{row['callee']}` (output + memFrame)

The base post (`ValueSpec.lean`) carries `ValueRepr` + the `NotWrittenV` register
frame, but NOT the console-output invariance or the sret-buffer memory frame that
`armTail_v` needs. Re-runs the `{row['callee']}` instructions, mirroring
value_null_spec_full / value_bool_spec_full. -/
theorem {row['spec_full']} (g : (R : Register) → Option (RegisterType R)) (buf{payload_bind} r : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (out0 : Array String) :
    Triple
      (fun c => GoodState c.σ ∧ {row['callee_loaded']} c.σ.mem ∧ c.σ.mem = m0 ∧
        c.σ.regs.get? Register.PC = some ({hex64(row['callee_entry'])} : BitVec 64) ∧
        c.σ.regs.get? Register.x10 = some buf ∧{payload_pin}
        c.σ.regs.get? Register.x1 = some r ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
        {C}Region buf ∧ (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
        c.σ.sailOutput = out0 ∧
        (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R))
      (fun c => GoodState c.σ ∧
        c.σ.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
        c.σ.regs.get? Register.x10 = some buf ∧ c.σ.regs.get? Register.x1 = some r ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
        ValueRepr c.σ.mem N φc buf.toNat ({row['value_expr']}) ∧
        c.σ.sailOutput = out0 ∧
        (∀ k : Nat, ¬ (buf.toNat ≤ k ∧ k < buf.toNat + 24) → m0[k]? = c.σ.mem[k]?) ∧
        (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = g R)) := by
  -- PER-CASE: re-run the callee's instructions site by site (mirror
  -- value_null_spec_full's 3-step / value_bool_spec_full's 5-step chain):
  -- per site: `obtain ⟨σk, ik, hsk, hik, hGk, hmemk, hobsk⟩ := site_… …`,
  -- transport pc/regs/minstret via obs_*_pc/obs_*_other/obs_*_minstret, keep
  -- `{row['callee_loaded']}` via loaded_{case}_writeMap4/8, close with the ret site,
  -- the ValueRepr read-back, the memFrame writeMap pass-throughs, and the
  -- NotWrittenV frame chain (frame_alu_v/frame_store_v/frame_jr_v).
  sorry
"""


def emit_blockC(row):
    case, C = row["case"], cap(row["case"])
    style = row["blockC_style"]
    binder_list = binders(row)
    extra_binders = "".join(f" ({n} : {t})" for n, t in binder_list)
    val = row["value_expr"]
    val_paren = f"({val})" if " " in val else val
    head = f"""
/-! ## `{row['blockC']}` — the `{row['evale_ctor']}` arm

`ArmEntryK … {row['arm_pc']} {row['callee_loaded']} {val_paren} → PreEpilogueV … {val_paren}`. -/
theorem {row['blockC']}
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St){extra_binders}
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    -- the sret buffer is disjoint from `{row['callee']}`'s code
    -- `[{row['callee_code_lo']}, {row['callee_code_hi']})` (threaded from `{row['entry_struct']}`).
    (hsret_vcallee : sret.toNat + 24 ≤ {row['callee_code_lo']} ∨ {row['callee_code_hi']} ≤ sret.toNat) :
    Triple
      (fun c => ∃ ment,
        ArmEntryK g N A SL φf φc st ({hex64(row['arm_pc'])}) {row['callee_loaded']} {val_paren}
          sp r sret aExpr v8 v9 v18 out0 m0 ment c)
      (fun c => ∃ mpre, PreEpilogueV g N A SL φf φc st {val_paren} sp r sret v8 v9 v18 out0 m0 mpre c) := by
"""
    if style == "armTail":
        jal_site = f"site_{row['jal_pc'][2:]}_ee"
        j_site = f"site_{row['j_pc'][2:]}_ee"
        return head + f"""  intro c hc
  obtain ⟨ment, hG, htick, hpc, ha0, hs1, ha2, hsp, hra, hmiEx, hout, hmem, hcode, hviCode,
    hexpr, houtStr, hexprAl, hexprLo, hexprHi, hexprWin,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hSLlo, hSLwin, hSLloSp, hraAl⟩ := hc
  -- region facts for `{row['callee']}`'s buffer writes and its `ret`
  have h{C}Region : {C}Region sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsret_vcallee⟩
  have hrettgt : (BitVec.update (({hex64(row['j_pc'])} : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt ({hex64(row['j_pc'])}) (by decide)]; decide
  refine armTail_v g N A SL φf φc st {val_paren}
    ({hex64(row['arm_pc'])}) ({hex64(row['callee_entry'])}) ({hex64(row['j_pc'])}) ({row['jal_imm']}#21) ({row['j_imm']}#21) {row['callee_loaded']}
    sp r sret v8 v9 v18 out0 m0
    (by apply BitVec.eq_of_toNat_eq; decide)   -- jal target = calleeEntry
    (by apply BitVec.eq_of_toNat_eq; decide)   -- addInt armPC 4 = calleeLink
    (by decide)                                -- calleeLink %4 = 0
    (by rw [show ({hex64(row['j_pc'])} + sign_extend (m := 64) ({row['j_imm']}#21) : BitVec 64) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide)  -- j target %4 = 0
    (by apply BitVec.eq_of_toNat_eq; decide)   -- j target = 0x800033ec
    -- jal site
    (fun σ i u vmi hGσ hpcσ hmiσ hcodeσ hiσ =>
      {jal_site} σ i u ({hex64(row['jal_pc'])}) vmi hGσ hpcσ hmiσ hcodeσ rfl
        (by rw [show ({hex64(row['jal_pc'])} + sign_extend (m := 64) ({row['jal_imm']}#21) : BitVec 64) = {hex64(row['callee_entry'])} from by apply BitVec.eq_of_toNat_eq; decide]; decide) hiσ)
    -- j site
    (fun σ i u vmi hGσ hpcσ hmiσ hcodeσ hiσ =>
      {j_site} σ i u ({hex64(row['j_pc'])}) vmi hGσ hpcσ hmiσ hcodeσ rfl
        (by rw [show ({hex64(row['j_pc'])} + sign_extend (m := 64) ({row['j_imm']}#21) : BitVec 64) = 0x800033ec#64 from by apply BitVec.eq_of_toNat_eq; decide]; decide) hiσ)
    -- callee behavior ({row['spec_full']})
    (fun gc cc mc hGc hLc hmemc hpcc ha0c hra1c hmic htickc houtc hframec => by
      exact {row['spec_full']} gc sret ({hex64(row['j_pc'])}) N φc mc out0 cc
        ⟨hGc, hLc, hmemc, hpcc, ha0c, hra1c, hmic, htickc, h{C}Region, hrettgt, houtc, hframec⟩)
    -- the massaged arm-entry precondition
    c ⟨ment, hG, htick, hpc, ha0, hs1, hsp, hmiEx, hout, hmem, hcode, hviCode,
      houtStr, hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
      hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
      hsretStk, hsretEvalCode, hSLloSp,
      hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩
"""
    elif style == "payload_then_armTail":
        return head + f"""  -- PER-CASE: run the payload `{row['payload_insn']} a1,8(a2)` site ({row['payload_site']})
  -- from the ArmEntryK state (mirror blockC_str: extract the payload bytes from
  -- `ExprRepr ment aExpr {val_paren}` via read64_bytes/read32_bytes + the
  -- payload-value bridge), then close the `jal {row['callee']}; j` tail through
  -- `armTail_v` at the jal PC {row['jal_pc']} with `{row['spec_full']}`
  -- (as in the `armTail`-style emission — see blockC_null / blockC_str).
  sorry
"""
    elif style == "inline_tail":
        return head + f"""  -- PER-CASE: payload `{row['payload_insn']}` site ({row['payload_site']}), then the
  -- INLINED tail (mirror blockC_bool / blockC_ee): jal site site_{row['jal_pc'][2:]}_ee,
  -- `{row['spec_full']}` at the callee ghost `fun R => σ2.regs.get? R`, the j site
  -- site_{row['j_pc'][2:]}_ee, spill-slot/store/code survival via the callee memFrame
  -- (AgreeP), and the epilogue g-frame chain. ~150 lines; consider the
  -- payload_then_armTail shape instead if the payload bridge allows it.
  sorry
"""
    else:  # custom_inlined_epilogue (var)
        return head + f"""  -- PER-CASE: fully custom arm (mirror blockC_var, EvalVarSim.lean): the arm
  -- calls `{row['callee']}` and carries its OWN inlined epilogue, reaching
  -- EvalExit directly (no shared blockD_v).
  sorry
"""


def emit_slot(row):
    case, C = row["case"], cap(row["case"])
    bs = row["slot_bytes"].split(":")
    off = 4 * int(row["tag"])
    pins = "\n".join(
        f"  m[(jumpTableBase + {off + i} : Nat)]? = some (0x{bs[i]} : BitVec 8)" + (" ∧" if i < 3 else "")
        for i in range(4))
    simpa = "\n".join("  · simpa using p" + str(i) for i in range(4))
    return f"""
/-! ## `{row['slot_def']}` — the `{row['evale_ctor']}` (tag {row['tag']}) jump-table slot pin

The slot at `jumpTableBase + {off}` holds `{' '.join(bs)}` (LE) = offset
`0xfffe{bs[1]}{bs[0]}`, and `0x80019f58 + (Int32)offset = {row['arm_pc']}` (the {case} arm).
Discharges `KindSlotPinned {row['tag']} {row['arm_pc']}` for the loaded image. -/
def {row['slot_def']} (m : Mem) : Prop :=
{pins}

theorem {row['slot_thm']} {{m : Mem}} (h : {row['slot_def']} m) :
    KindSlotPinned {row['tag']} ({hex64(row['arm_pc'])}) m := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨0x{bs[0]}#8, 0x{bs[1]}#8, 0x{bs[2]}#8, 0x{bs[3]}#8, ?_, ?_, ?_, ?_, ?_⟩
{simpa}
  · apply BitVec.eq_of_toNat_eq; simp only [jumpTableBase]; decide
"""


def emit_entry(row):
    case, C = row["case"], cap(row["case"])
    binder_list = binders(row)
    extra = "".join(f" ({n} : {t})" for n, t in binder_list)
    val = row["value_expr"]
    val_paren = f"({val})" if " " in val else val
    slot_field = f"{case}_slot"
    return f"""
/-! ## `{row['entry_struct']}` — the machine precondition for the `{row['evale_ctor']}` case

Mirrors `EvalNullEntry` (`EvalNullSim.lean`), with the {case}-specific slot pin,
callee-code predicate, and `ExprRepr … {val_paren}` (`read32 = {row['tag']}`). -/
structure {row['entry_struct']}
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Vsa.While.Addr){extra}
    (sp r sret aEnv aExpr : BitVec 64)
    (m0 : Mem)
    (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 evalExprEntry)
  a0 : c.σ.regs.get? Register.x10 = some sret
  a1 : c.σ.regs.get? Register.x11 = some aEnv
  a2 : c.σ.regs.get? Register.x12 = some aExpr
  ra : c.σ.regs.get? Register.x1 = some r
  ra_align : r.toNat % 4 = 0
  spReg : c.σ.regs.get? Register.x2 = some sp
  stackOK : StackOK SL sp (1088 + 1088)
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  mem : c.σ.mem = m0
  code : InterpCodeLoaded c.σ.mem
  expr : ExprRepr c.σ.mem aExpr.toNat {val_paren}
  store : StoreRepr c.σ.mem N A φf φc st.store
  store_survives : ∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
      c.σ.mem[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store
  out : OutRepr c.σ st
  frame : ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R
  code_stack_disjoint : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  expr_stack_disjoint : aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  expr_align : aExpr.toNat % 8 = 0
  expr_ram : 0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000
  expr_win : tohostAddr + 16 ≤ aExpr.toNat
  sret_align : sret.toNat % 8 = 0
  sret_ram : 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000
  sret_win : tohostAddr + 16 ≤ sret.toNat
  /-- sret disjoint from the `value_int` code — the shared `ArmEntryK` field. -/
  sret_vicode_disjoint : sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat
  /-- sret disjoint from the `{row['callee']}` code
  `[{row['callee_code_lo']}, {row['callee_code_hi']})` — the callee's sret-write region. -/
  sret_vcalleecode_disjoint : sret.toNat + 24 ≤ {row['callee_code_lo']} ∨ {row['callee_code_hi']} ≤ sret.toNat
  sret_stack_disjoint : sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat
  sret_evalcode_disjoint : sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat
  /-- `{row['callee']}` code disjoint from the stack region — keeps
  `{row['callee_loaded']}` across the prologue spills. -/
  vcalleecode_stack_disjoint : ({row['callee_code_hi']} : Nat) ≤ SL.lo ∨ sp.toNat ≤ {row['callee_code_lo']}
  stack_ram : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000
  stack_win : tohostAddr + 16 ≤ SL.lo
  callee_code : {row['callee_loaded']} c.σ.mem
  {slot_field} : {row['slot_def']} c.σ.mem
  table_stack_disjoint : (0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + {4 * int(row['tag'])}
  spill_defined : (∃ v, c.σ.regs.get? Register.x8 = some v) ∧
    (∃ v, c.σ.regs.get? Register.x9 = some v) ∧ (∃ v, c.σ.regs.get? Register.x18 = some v)
  -- PER-CASE: payload-survival fields, if any (e.g. EvalStrSim's / EvalVarSim's
  -- `var_stack_disjoint`-style CString geometry for pointer payloads).
"""


def emit_kind_lemma(row):
    case = row["case"]
    val = row["value_expr"]
    val_paren = f"({val})" if " " in val else val
    bvars = "".join(" {" + n + " : " + t + "}" for n, t in binders(row))
    return f"""
/-- The `{row['evale_ctor']}` kind tag `read32 = some {row['tag']}`, from `ExprRepr … {val_paren}`. -/
theorem exprRepr_{case}_kind {{m : Mem}} {{a : Nat}}{bvars} (h : ExprRepr m a {val_paren}) :
    read32 m a = some {row['tag']} := by
  -- PER-CASE: `cases h with | <ctor(s)> hk … => exact hk` (one arm per ExprRepr
  -- constructor of this kind; cf. exprRepr_null_kind / exprRepr_bool_kind).
  sorry
"""


def emit_goal_and_theorem(row):
    case, C = row["case"], cap(row["case"])
    binder_list = binders(row)
    extra = "".join(f" ({n} : {t})" for n, t in binder_list)
    extra_names = "".join(f" {n}" for n, _ in binder_list)
    val = row["value_expr"]
    val_paren = f"({val})" if " " in val else val
    # EvalE source expr: for var the source is (.var x) while the result is v
    src_expr = val_paren if case != "var" else "(.var x)"
    epi = row["epilogue"]
    epi_call = (f"""  -- === block D: epilogue → EvalExit {val_paren} ===
  obtain ⟨c3, hs3, hExit⟩ :=
    {epi} g N A SL φf φc st {val_paren} sp r sret v8 v9 v18 c.σ.sailOutput m0 c2 ⟨mpre, hPre⟩
  exact ⟨c3, (hs1.trans hs2).trans hs3, hExit⟩"""
                if epi in ("blockD_v", "blockD_ee") else
                """  -- PER-CASE: this arm's blockC reaches EvalExit directly (inlined epilogue);
  -- compose hs1 with blockC's run only.
  sorry""")
    return f"""
/-- **The `{row['evale_ctor']}` simulation goal.** -/
def {row['goal_def']} : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (d : Nat) (a : Addr){extra}
    (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem),
    EvalE st d a {src_expr} st {val_paren} →
    Triple
      ({row['entry_struct']} g N A SL φf φc st d a{extra_names} sp r sret aEnv aExpr m0)
      (EvalExit g N A SL φf φc st {val_paren} sp r sret m0)

/-- **The M4 `{row['evale_ctor']}` gate.** Composes `blockA_k` (prologue + dispatch →
`ArmEntryK` at the {case} arm), `{row['blockC']}` (arm + `{row['callee']}` → epilogue entry),
and `{epi}` at {val_paren}. -/
theorem {row['theorem']} : {row['goal_def']} := by
  intro g N A SL φf φc st d a{extra_names} sp r sret aEnv aExpr m0 _hEvalE
  intro c hc
  -- === block A: prologue + dispatch → ArmEntryK (via blockA_k) ===
  have hkm0 : read32 m0 aExpr.toNat = some {row['tag']} := hc.mem ▸ exprRepr_{case}_kind (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm⟩ :=
    blockA_k g N A SL φf φc st {val_paren} {row['tag']} ({hex64(row['arm_pc'])}) {row['callee_loaded']}
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      ({row['slot_thm']} (hc.mem ▸ hc.{case}_slot)) (hc.mem ▸ hc.callee_code)
      (fun mem a8 dd hlo hhi hh => by
        have hvs := hc.vcalleecode_stack_disjoint
        exact loaded_{case}_writeMap8 mem a8 dd (by omega) hh)
      (fun m' hag => by
        -- PER-CASE (hexprSurv): re-establish `ExprRepr m' aExpr {val_paren}` at the
        -- post-prologue memory. The kind word transfers by this template:
        --   obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ :=
        --     read32_bytes m0 aExpr.toNat {row['tag']} hkm0
        --   simp only [read32, readLE, bind, Option.bind]
        --   rw [← hag …] ×4; rw [hb0, hb1, hb2, hb3]; …
        -- plus, per case, the payload word(s)/CString survival (cf.
        -- EvalBoolSim's hpaySurv, EvalStrSim's cstring_agreeP).
        sorry)
      (by decide)
      (by have := hc.table_stack_disjoint; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
      hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
      hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
      hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint,
      hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
      hc.spill_defined⟩, rfl⟩
  -- === block C: arm → PreEpilogueV {val_paren} ===
  obtain ⟨c2, hs2, mpre, hPre⟩ :=
    {row['blockC']} g N A SL φf φc st{extra_names} sp r sret aExpr v8 v9 v18 c.σ.sailOutput m0
      hc.sret_vcalleecode_disjoint c1 ⟨ment, hArm⟩
{epi_call}

end Vsa.Sim
"""


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("case", help="row of m4_cases.tsv (int/str/bool/null/var/…)")
    ap.add_argument("-t", "--tsv", default="scripts/m4_cases.tsv")
    ap.add_argument("-o", "--out", default=None, help="output file (default: stdout)")
    args = ap.parse_args()

    row = load_row(args.tsv, args.case)
    parts = [
        emit_header(row),
        emit_payload_site(row),
        emit_jal_site(row),
        emit_j_site(row),
        emit_loaded_writemap8(row),
        emit_spec_full(row),
        emit_blockC(row),
        emit_slot(row),
        emit_entry(row),
        emit_kind_lemma(row),
        emit_goal_and_theorem(row),
    ]
    text = "".join(parts)
    if args.out:
        with open(args.out, "w") as f:
            f.write(text)
        holes = text.count("PER-CASE")
        print(f"wrote {args.out}: {len(text.splitlines())} lines, "
              f"{holes} PER-CASE markers ({text.count('sorry')} holes)")
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
