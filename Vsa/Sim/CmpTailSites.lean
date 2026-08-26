import Vsa.Sim.CmpTailSitesGen
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part13
import Vsa.Sim.DecodeTable.Batch05Part26
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch16Part27
import Vsa.Sim.DecodeTable.Batch07Part22
import Vsa.Sim.DecodeTable.Batch04Part02
import Vsa.Sim.DecodeTable.Batch02Part23

/-!
Hand-written `StepObs` sites for the shared inline comparison arm @0x80003628
that `scripts/gen_sites.py` cannot emit (auipc / slli / srli / slt / not(xori) /
sgtz(slt x0) / slti).  The gen-able sites live in `CmpTailSitesGen`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- 0x80003640: `auipc x13,0x16` — CSWTCH.25 error-string base (hi). -/
theorem site_80003640_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003640#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13
          (pc + sign_extend (m := 64) ((0x00016#20) +++ 0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_80003640 hmem
  exact stepObs_alu σ i u (0x80003640#64) vminstret (0x00016697#32)
    (instruction.UTYPE (0x00016#20, regidx.Regidx 0x0d#5, uop.AUIPC))
    Register.x13 ((0x80003640#64 : BitVec 64) + sign_extend (m := 64) ((0x00016#20) +++ 0x000#12))
    (0x97#8) (0x66#8) (0x01#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00016697 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by
      have hpc₂ : (afterNextPC (afterPrelude σ) (0x80003640#64)).regs.get? Register.PC
          = some (0x80003640#64) := by
        rw [get?_afterNextPC σ (0x80003640#64) _ (by decide) (by decide)]; exact hpc
      exact execute_utype_auipc_char (0x00016#20) (regidx.Regidx 0x0d#5) (0x80003640#64)
        (afterNextPC (afterPrelude σ) (0x80003640#64))
        (sigma3_alu σ (0x80003640#64) Register.x13
          ((0x80003640#64 : BitVec 64) + sign_extend (m := 64) ((0x00016#20) +++ 0x000#12))) hpc₂
        (wX_bits_x13 _ ((0x80003640#64 : BitVec 64)
          + sign_extend (m := 64) ((0x00016#20) +++ 0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000364c: `slli x14,x15,0x20`. -/
theorem site_8000364c_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000364c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_8000364c hmem
  exact stepObs_alu σ i u (0x8000364c#64) vminstret (0x02079713#32)
    (instruction.SHIFTIOP (0x20#6, regidx.Regidx 0x0f#5, regidx.Regidx 0x0e#5, sop.SLLI))
    Register.x14 (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))
    (0x13#8) (0x97#8) (0x07#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02079713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_slli_char (0x20#6) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) v15
      (afterNextPC (afterPrelude σ) (0x8000364c#64))
      (sigma3_alu σ (0x8000364c#64) Register.x14
        (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0)))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x8000364c#64) _ (by decide) (by decide)]; exact hx15))
      (wX_bits_x14 _ (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003650: `srli x15,x14,0x1d`. -/
theorem site_80003650_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003650#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1d#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_80003650 hmem
  exact stepObs_alu σ i u (0x80003650#64) vminstret (0x01d75793#32)
    (instruction.SHIFTIOP (0x1d#6, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, sop.SRLI))
    Register.x15 (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1d#6) 5 0))
    (0x93#8) (0x57#8) (0xd7#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01d75793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_srli_char (0x1d#6) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v14
      (afterNextPC (afterPrelude σ) (0x80003650#64))
      (sigma3_alu σ (0x80003650#64) Register.x15
        (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1d#6) 5 0)))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x80003650#64) _ (by decide) (by decide)]; exact hx14))
      (wX_bits_x15 _ (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1d#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003654: `auipc x14,0x17` — CSWTCH.25 base (hi). -/
theorem site_80003654_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003654#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (pc + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_80003654 hmem
  exact stepObs_alu σ i u (0x80003654#64) vminstret (0x00017717#32)
    (instruction.UTYPE (0x00017#20, regidx.Regidx 0x0e#5, uop.AUIPC))
    Register.x14 ((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))
    (0x17#8) (0x77#8) (0x01#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00017717 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by
      have hpc₂ : (afterNextPC (afterPrelude σ) (0x80003654#64)).regs.get? Register.PC
          = some (0x80003654#64) := by
        rw [get?_afterNextPC σ (0x80003654#64) _ (by decide) (by decide)]; exact hpc
      exact execute_utype_auipc_char (0x00017#20) (regidx.Regidx 0x0e#5) (0x80003654#64)
        (afterNextPC (afterPrelude σ) (0x80003654#64))
        (sigma3_alu σ (0x80003654#64) Register.x14
          ((0x80003654#64 : BitVec 64) + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))) hpc₂
        (wX_bits_x14 _ ((0x80003654#64 : BitVec 64)
          + sign_extend (m := 64) ((0x00017#20) +++ 0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003698: `slt x14,x17,x19` — `x14 := (a7 <ₛ s3)`. -/
theorem site_80003698_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v17 v19 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hx19 : σ.regs.get? Register.x19 = some v19)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003698#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v17 v19)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_80003698 hmem
  exact stepObs_alu σ i u (0x80003698#64) vminstret (0x0138a733#32)
    (instruction.RTYPE (regidx.Regidx 0x13#5, regidx.Regidx 0x11#5, regidx.Regidx 0x0e#5, rop.SLT))
    Register.x14 (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v17 v19)))
    (0x33#8) (0xa7#8) (0x38#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0138a733 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_slt_char (regidx.Regidx 0x13#5) (regidx.Regidx 0x11#5) (regidx.Regidx 0x0e#5)
      v17 v19 (afterNextPC (afterPrelude σ) (0x80003698#64))
      (sigma3_alu σ (0x80003698#64) Register.x14 (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v17 v19))))
      (rX_bits_x17 _ v17
        (by rw [get?_afterNextPC σ (0x80003698#64) _ (by decide) (by decide)]; exact hx17))
      (rX_bits_x19 _ v19
        (by rw [get?_afterNextPC σ (0x80003698#64) _ (by decide) (by decide)]; exact hx19))
      (wX_bits_x14 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v17 v19)))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000369c: `slt x15,x19,x17` — `x15 := (s3 <ₛ a7)`. -/
theorem site_8000369c_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v17 v19 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx17 : σ.regs.get? Register.x17 = some v17)
    (hx19 : σ.regs.get? Register.x19 = some v19)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x8000369c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v19 v17)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_8000369c hmem
  exact stepObs_alu σ i u (0x8000369c#64) vminstret (0x0119a7b3#32)
    (instruction.RTYPE (regidx.Regidx 0x11#5, regidx.Regidx 0x13#5, regidx.Regidx 0x0f#5, rop.SLT))
    Register.x15 (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v19 v17)))
    (0xb3#8) (0xa7#8) (0x19#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0119a7b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_slt_char (regidx.Regidx 0x11#5) (regidx.Regidx 0x13#5) (regidx.Regidx 0x0f#5)
      v19 v17 (afterNextPC (afterPrelude σ) (0x8000369c#64))
      (sigma3_alu σ (0x8000369c#64) Register.x15 (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v19 v17))))
      (rX_bits_x19 _ v19
        (by rw [get?_afterNextPC σ (0x8000369c#64) _ (by decide) (by decide)]; exact hx19))
      (rX_bits_x17 _ v17
        (by rw [get?_afterNextPC σ (0x8000369c#64) _ (by decide) (by decide)]; exact hx17))
      (wX_bits_x15 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v19 v17)))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800036bc: `not x11,x11` = `xori x11,x11,-1`. -/
theorem site_800036bc_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800036bc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (v11 ^^^ (sign_extend (m := 64) (0xfff#12)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_800036bc hmem
  exact stepObs_alu σ i u (0x800036bc#64) vminstret (0xfff5c593#32)
    (instruction.ITYPE (0xfff#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.XORI))
    Register.x11 (v11 ^^^ (sign_extend (m := 64) (0xfff#12)))
    (0x93#8) (0xc5#8) (0xf5#8) (0xff#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_fff5c593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_xori_char (0xfff#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11
      (afterNextPC (afterPrelude σ) (0x800036bc#64))
      (sigma3_alu σ (0x800036bc#64) Register.x11 (v11 ^^^ (sign_extend (m := 64) (0xfff#12))))
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x800036bc#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x11 _ (v11 ^^^ (sign_extend (m := 64) (0xfff#12)))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800036c0: `srli x11,x11,0x3f` — sign-bit extract (lt fixup). -/
theorem site_800036c0_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x800036c0#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (shift_bits_right v11 (Sail.BitVec.extractLsb (0x3f#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_800036c0 hmem
  exact stepObs_alu σ i u (0x800036c0#64) vminstret (0x03f5d593#32)
    (instruction.SHIFTIOP (0x3f#6, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, sop.SRLI))
    Register.x11 (shift_bits_right v11 (Sail.BitVec.extractLsb (0x3f#6) 5 0))
    (0x93#8) (0xd5#8) (0xf5#8) (0x03#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_03f5d593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_srli_char (0x3f#6) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11
      (afterNextPC (afterPrelude σ) (0x800036c0#64))
      (sigma3_alu σ (0x800036c0#64) Register.x11
        (shift_bits_right v11 (Sail.BitVec.extractLsb (0x3f#6) 5 0)))
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x800036c0#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x11 _ (shift_bits_right v11 (Sail.BitVec.extractLsb (0x3f#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003ae4: `sgtz x11,x11` = `slt x11,x0,x11` — `x11 := (0 <ₛ cmp)` (gt fixup). -/
theorem site_80003ae4_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003ae4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) v11)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_80003ae4 hmem
  exact stepObs_alu σ i u (0x80003ae4#64) vminstret (0x00b025b3#32)
    (instruction.RTYPE (regidx.Regidx 0x0b#5, regidx.Regidx 0x00#5, regidx.Regidx 0x0b#5, rop.SLT))
    Register.x11 (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) v11)))
    (0xb3#8) (0x25#8) (0xb0#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00b025b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_slt_char (regidx.Regidx 0x0b#5) (regidx.Regidx 0x00#5) (regidx.Regidx 0x0b#5)
      (0#64) v11 (afterNextPC (afterPrelude σ) (0x80003ae4#64))
      (sigma3_alu σ (0x80003ae4#64) Register.x11 (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) v11))))
      (rX_bits_zero _)
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x80003ae4#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x11 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) v11)))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80003af8: `slti x11,x11,1` — `x11 := (cmp <ₛ 1)` (le fixup). -/
theorem site_80003af8_ee
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hpcv : pc = (0x80003af8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x11
          (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v11 (sign_extend (m := 64) (0x001#12)))))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.eval_expr_at_80003af8 hmem
  exact stepObs_alu σ i u (0x80003af8#64) vminstret (0x0015a593#32)
    (instruction.ITYPE (0x001#12, regidx.Regidx 0x0b#5, regidx.Regidx 0x0b#5, iop.SLTI))
    Register.x11 (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v11 (sign_extend (m := 64) (0x001#12)))))
    (0x93#8) (0xa5#8) (0x15#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0015a593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_slti_char (0x001#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0b#5) v11
      (afterNextPC (afterPrelude σ) (0x80003af8#64))
      (sigma3_alu σ (0x80003af8#64) Register.x11
        (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v11 (sign_extend (m := 64) (0x001#12))))))
      (rX_bits_x11 _ v11
        (by rw [get?_afterNextPC σ (0x80003af8#64) _ (by decide) (by decide)]; exact hx11))
      (wX_bits_x11 _ (zero_extend (m := 64) (bool_to_bit (zopz0zI_s v11 (sign_extend (m := 64) (0x001#12)))))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
