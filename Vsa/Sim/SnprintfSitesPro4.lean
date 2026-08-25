import Vsa.Sim.SnprintfSitesRet5
import Vsa.Sim.Code.Memset
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch08Part30
import Vsa.Sim.DecodeTable.Batch01Part09
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch06Part14
import Vsa.Sim.DecodeTable.Batch03Part02
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch04Part10

/-!
# M3 Layer-3 — hand `StepObs` sites for the svfprintf PROLOGUE generator gaps

`scripts/gen_sites.py` has no `lhu`/`andi`/`auipc`/`slli`/`srli`/offset-`jr`
classes; the eight sites on the prologue + first-parse-pass path in those
classes are hand-written here on the validated templates
(`SnprintfSitesRet5.site_800079c0_rt5`/`site_800079c4_rt5` for `lhu`/`andi`,
`EvalExprSites.site_80003190_ee` for `auipc`, `StrlenSites.site_80006d04`
for `slli`, `SnprintfSpec14`'s inline `srli` block, and the generated
`jr`-class emission with a nonzero immediate for `jr 12(a3)`).

  0x800076a4  lhu  a5,16(s1)     FILE `_flags` halfword
  0x800076a8  andi a5,a5,128     `__SCLE` test (taken-zero on this path)
  0x80007788  auipc s6,0x13      parse jump-table base (hi part)
  0x800077a8  slli a4,a5,0x20    dispatch index scale (hi)
  0x800077ac  srli a5,a4,0x1e    dispatch index scale (lo) = 4*(ch-32)
  0x80006b2c  slli a3,a3,0x2     memset jump-table scale
  0x80006b30  auipc t0,0x0       memset jump-table base
  0x80006b38  jr   12(a3)        memset computed dispatch
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- 0x800076a4: `lhu a5,16(s1)` — the FILE `_flags` halfword. -/
theorem site_800076a4_pr4 (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v9 : BitVec 64)
    (b0v b1v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Vsa.Sim.Code.SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800076a4#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (v9 + sign_extend (m := 64) (0x010#12)).toNat)
    (hhiram : (v9 + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ 0x100000000)
    (hhtif : (v9 + sign_extend (m := 64) (0x010#12)).toNat + 2 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (v9 + sign_extend (m := 64) (0x010#12)).toNat)
    (halign : (v9 + sign_extend (m := 64) (0x010#12)).toNat % 2 = 0)
    (hb0 : σ.mem[(v9 + sign_extend (m := 64) (0x010#12)).toNat]? = some b0v)
    (hb1 : σ.mem[(v9 + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1v)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15
        (zero_extend (m := 64) ((b1v.append b0v) : BitVec (8 * 2)))) := by
  subst hpcv
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800076a4 hmem
  exact stepObs_alu σ i u (0x800076a4#64) vminstret (0x0104d783#32)
    (instruction.LOAD (0x010#12, regidx.Regidx 0x09#5, regidx.Regidx 0x0f#5, true, 2))
    Register.x15 (zero_extend (m := 64) ((b1v.append b0v) : BitVec (8 * 2)))
    (0x83#8) (0xd7#8) (0x04#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0104d783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lhu_gen σ (0x800076a4#64) (0x010#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0f#5)
      v9 b0v b1v
      (sigma3_alu σ (0x800076a4#64) Register.x15
        (zero_extend (m := 64) ((b1v.append b0v) : BitVec (8 * 2)))) hG
      (rX_bits_x9 _ v9
        (by rw [get?_afterNextPC σ (0x800076a4#64) _ (by decide) (by decide)]; exact hx9))
      (wX_bits_x15 _ (zero_extend (m := 64) ((b1v.append b0v) : BitVec (8 * 2))))
      hlo hhiram hhtif halign hb0 hb1)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi

/-- 0x800076a8: `andi a5,a5,128` — the `__SCLE` flag test. -/
theorem site_800076a8_pr4 (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Vsa.Sim.Code.SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800076a8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15
        (v15 &&& sign_extend (m := 64) (0x080#12))) := by
  subst hpcv
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800076a8 hmem
  exact stepObs_alu σ i u (0x800076a8#64) vminstret (0x0807f793#32)
    (instruction.ITYPE (0x080#12, regidx.Regidx 0x0f#5, regidx.Regidx 0x0f#5, iop.ANDI))
    Register.x15 (v15 &&& sign_extend (m := 64) (0x080#12))
    (0x93#8) (0xf7#8) (0x07#8) (0x08#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0807f793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_andi_char (0x080#12) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15
      (afterNextPC (afterPrelude σ) (0x800076a8#64))
      (sigma3_alu σ (0x800076a8#64) Register.x15 (v15 &&& sign_extend (m := 64) (0x080#12)))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x800076a8#64) _ (by decide) (by decide)]; exact hx15))
      (wX_bits_x15 _ (v15 &&& sign_extend (m := 64) (0x080#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hc0 hc1 hc2 hc3 (by decide) (by decide) (by decide) hi

/-- 0x80007788: `auipc s6,0x13` — parse jump-table base, hi part.
Writes `x22 := pc + sext(0x13 <<< 12)`. -/
theorem site_80007788_pr4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80007788#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x22
          (pc + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80007788 hmem
  exact stepObs_alu σ i u (0x80007788#64) vminstret (0x00013b17#32)
    (instruction.UTYPE (0x00013#20, regidx.Regidx 0x16#5, uop.AUIPC))
    Register.x22 ((0x80007788#64 : BitVec 64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12))
    (0x17#8) (0x3b#8) (0x01#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00013b17 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by
      have hpc₂ : (afterNextPC (afterPrelude σ) (0x80007788#64)).regs.get? Register.PC
          = some (0x80007788#64) := by
        rw [get?_afterNextPC σ (0x80007788#64) _ (by decide) (by decide)]; exact hpc
      exact execute_utype_auipc_char (0x00013#20) (regidx.Regidx 0x16#5) (0x80007788#64)
        (afterNextPC (afterPrelude σ) (0x80007788#64))
        (sigma3_alu σ (0x80007788#64) Register.x22
          ((0x80007788#64 : BitVec 64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12))) hpc₂
        (wX_bits_x22 _ ((0x80007788#64 : BitVec 64)
          + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800077a8: `slli a4,a5,0x20` — dispatch index scale (hi).
Writes `x14 := a5 <<< 32`. -/
theorem site_800077a8_pr4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Vsa.Sim.Code.SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800077a8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x14
          (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077a8 hmem
  exact stepObs_alu σ i u (0x800077a8#64) vminstret (0x02079713#32)
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
      (afterNextPC (afterPrelude σ) (0x800077a8#64))
      (sigma3_alu σ (0x800077a8#64) Register.x14
        (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0)))
      (rX_bits_x15 _ v15
        (by rw [get?_afterNextPC σ (0x800077a8#64) _ (by decide) (by decide)]; exact hx15))
      (wX_bits_x14 _ (shift_bits_left v15 (Sail.BitVec.extractLsb (0x20#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x800077ac: `srli a5,a4,0x1e` — dispatch index scale (lo).
Writes `x15 := a4 >>> 30`. -/
theorem site_800077ac_pr4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Vsa.Sim.Code.SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x800077ac#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x15
          (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1e#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_800077ac hmem
  exact stepObs_alu σ i u (0x800077ac#64) vminstret (0x01e75793#32)
    (instruction.SHIFTIOP (0x1e#6, regidx.Regidx 0x0e#5, regidx.Regidx 0x0f#5, sop.SRLI))
    Register.x15 (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1e#6) 5 0))
    (0x93#8) (0x57#8) (0xe7#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_01e75793 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_srli_char (0x1e#6) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) v14
      (afterNextPC (afterPrelude σ) (0x800077ac#64))
      (sigma3_alu σ (0x800077ac#64) Register.x15
        (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1e#6) 5 0)))
      (rX_bits_x14 _ v14
        (by rw [get?_afterNextPC σ (0x800077ac#64) _ (by decide) (by decide)]; exact hx14))
      (wX_bits_x15 _ (shift_bits_right v14 (Sail.BitVec.extractLsb (0x1e#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006b2c: `slli a3,a3,0x2` — memset jump-table scale. Writes `x13 := a3 <<< 2`. -/
theorem site_80006b2c_pm4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : Vsa.Sim.Code.MemsetLoaded σ.mem)
    (hpcv : pc = (0x80006b2c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x13
          (shift_bits_left v13 (Sail.BitVec.extractLsb (0x02#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memset_at_80006b2c hmem
  exact stepObs_alu σ i u (0x80006b2c#64) vminstret (0x00269693#32)
    (instruction.SHIFTIOP (0x02#6, regidx.Regidx 0x0d#5, regidx.Regidx 0x0d#5, sop.SLLI))
    Register.x13 (shift_bits_left v13 (Sail.BitVec.extractLsb (0x02#6) 5 0))
    (0x93#8) (0x96#8) (0x26#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00269693 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_slli_char (0x02#6) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0d#5) v13
      (afterNextPC (afterPrelude σ) (0x80006b2c#64))
      (sigma3_alu σ (0x80006b2c#64) Register.x13
        (shift_bits_left v13 (Sail.BitVec.extractLsb (0x02#6) 5 0)))
      (rX_bits_x13 _ v13
        (by rw [get?_afterNextPC σ (0x80006b2c#64) _ (by decide) (by decide)]; exact hx13))
      (wX_bits_x13 _ (shift_bits_left v13 (Sail.BitVec.extractLsb (0x02#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006b30: `auipc t0,0x0` — memset jump-table base. Writes `x5 := pc`. -/
theorem site_80006b30_pm4
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.MemsetLoaded σ.mem)
    (hpcv : pc = (0x80006b30#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x5
          (pc + sign_extend (m := 64) ((0x00000#20) +++ 0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memset_at_80006b30 hmem
  exact stepObs_alu σ i u (0x80006b30#64) vminstret (0x00000297#32)
    (instruction.UTYPE (0x00000#20, regidx.Regidx 0x05#5, uop.AUIPC))
    Register.x5 ((0x80006b30#64 : BitVec 64) + sign_extend (m := 64) ((0x00000#20) +++ 0x000#12))
    (0x97#8) (0x02#8) (0x00#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00000297 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (by
      have hpc₂ : (afterNextPC (afterPrelude σ) (0x80006b30#64)).regs.get? Register.PC
          = some (0x80006b30#64) := by
        rw [get?_afterNextPC σ (0x80006b30#64) _ (by decide) (by decide)]; exact hpc
      exact execute_utype_auipc_char (0x00000#20) (regidx.Regidx 0x05#5) (0x80006b30#64)
        (afterNextPC (afterPrelude σ) (0x80006b30#64))
        (sigma3_alu σ (0x80006b30#64) Register.x5
          ((0x80006b30#64 : BitVec 64) + sign_extend (m := 64) ((0x00000#20) +++ 0x000#12))) hpc₂
        (wX_bits_x5 _ ((0x80006b30#64 : BitVec 64)
          + sign_extend (m := 64) ((0x00000#20) +++ 0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80006b38: `jr 12(a3)` — memset computed dispatch (`jalr x0,12(a3)`). -/
theorem site_80006b38_pm4 (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : Vsa.Sim.Code.MemsetLoaded σ.mem)
    (hpcv : pc = (0x80006b38#64 : BitVec 64))
    (htgt : (BitVec.update (v13 + sign_extend (m := 64) (0x00c#12)) 0 0#1).toNat % 4 = 0)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret
          (BitVec.update (v13 + sign_extend (m := 64) (0x00c#12)) 0 0#1)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.memset_at_80006b38 hmem
  exact stepObs_jr σ i u (0x80006b38#64) vminstret v13 (0x00c68067#32) (0x00c#12)
    (regidx.Regidx 0x0d#5) (0x67#8) (0x80#8) (0xc6#8) (0x00#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00c68067 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (rX_bits_x13 _ v13
      (by rw [get?_afterNextPC σ (0x80006b38#64) _ (by decide) (by decide)]; exact hx13))
    htgt hi

end Vsa.Sim
