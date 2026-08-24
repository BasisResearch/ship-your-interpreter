import Vsa.Sim.SnprintfSites
import Vsa.Sim.ValueSites
import Vsa.Sim.StrcpySites
import Vsa.Sim.Code.FlushPins

/-!
# M3 Layer-3 — `SnprintfSitesFlush` : exit-restore + flush-hop step battery (`_fl`)

Sites for the post-loop flush path (ordered PC trace, `experiments/pctrace.md`):
the exit-restore block `0x80008358 … 0x80008394` (spill reloads, `len = top −
cursor`, the sign-byte read-back `lbu t5,167(sp)`), and the hops
`0x8000812c/30/34 → 0x80008088/8c → 0x8000a830/34/38 → 0x8000782c`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- 0x80008358: `ld s6,112(sp)` (reload buffer top) (value `ld`). -/
theorem site_80008358_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008358#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x070#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x070#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x070#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x070#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x070#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x070#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x070#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x070#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x070#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x070#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x070#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x070#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x070#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x22
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008358 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80008358#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80008358#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80008358#64) vminstret (0x07013b03#32)
    (instruction.LOAD (0x070#12, regidx.Regidx 0x02#5, regidx.Regidx 0x16#5, false, 8))
    Register.x22 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x3b#8) (0x01#8) (0x07#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_07013b03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80008358#64) (0x070#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x16#5)
      (sigma3_alu σ (0x80008358#64) Register.x22
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x22 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000835c: `sd s4,104(sp)` (`sd`). -/
theorem site_8000835c_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hdata : σ.regs.get? Register.x20 = some vdata)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x8000835c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x068#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x068#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x068#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x068#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8000835c#64)).mem
        (vsp + sign_extend (m := 64) (0x068#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x8000835c#64)).mem
            (vsp + sign_extend (m := 64) (0x068#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000835c hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x8000835c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x8000835c#64) _ (by decide) (by decide)]; exact hx2
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x8000835c#64)).regs.get? Register.x20 = some vdata := by
    rw [get?_afterNextPC σ (0x8000835c#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x8000835c#64) vminstret (0x07413423#32)
    (instruction.STORE (0x068#12, regidx.Regidx 0x14#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8000835c#64)).mem
      (vsp + sign_extend (m := 64) (0x068#12)).toNat (sdData_val vdata))
    (0x23#8) (0x34#8) (0x41#8) (0x07#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_07413423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000835c#64) (0x068#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x02#5)
      vsp vdata hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x20 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008360: `ld s4,56(sp)` (reload width) (value `ld`). -/
theorem site_80008360_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008360#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x038#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x038#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x038#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x038#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x038#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x038#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x038#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x038#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x038#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x038#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x20
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008360 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80008360#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80008360#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80008360#64) vminstret (0x03813a03#32)
    (instruction.LOAD (0x038#12, regidx.Regidx 0x02#5, regidx.Regidx 0x14#5, false, 8))
    Register.x20 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x3a#8) (0x81#8) (0x03#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_03813a03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80008360#64) (0x038#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x14#5)
      (sigma3_alu σ (0x80008360#64) Register.x20
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x20 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008364: `ld t1,40(sp)` (reload flags) (value `ld`). -/
theorem site_80008364_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008364#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x028#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x028#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x028#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x028#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x028#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x028#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x028#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x028#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x028#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x028#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x6
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008364 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80008364#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80008364#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80008364#64) vminstret (0x02813303#32)
    (instruction.LOAD (0x028#12, regidx.Regidx 0x02#5, regidx.Regidx 0x06#5, false, 8))
    Register.x6 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x33#8) (0x81#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02813303 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80008364#64) (0x028#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x06#5)
      (sigma3_alu σ (0x80008364#64) Register.x6
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x6 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008368: `subw s6,s6,s10` (`len = top − cursor`, 32-bit). -/
theorem site_80008368_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v22 v26 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx22 : σ.regs.get? Register.x22 = some v22)
    (hx26 : σ.regs.get? Register.x26 = some v26)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008368#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x22
          (sign_extend (m := 64)
            ((Sail.BitVec.extractLsb v22 31 0) - (Sail.BitVec.extractLsb v26 31 0)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008368 hmem
  have hx22₂ : (afterNextPC (afterPrelude σ) (0x80008368#64)).regs.get? Register.x22 = some v22 := by
    rw [get?_afterNextPC σ (0x80008368#64) _ (by decide) (by decide)]; exact hx22
  have hx26₂ : (afterNextPC (afterPrelude σ) (0x80008368#64)).regs.get? Register.x26 = some v26 := by
    rw [get?_afterNextPC σ (0x80008368#64) _ (by decide) (by decide)]; exact hx26
  exact stepObs_alu σ i u (0x80008368#64) vminstret (0x41ab0b3b#32)
    (instruction.RTYPEW (regidx.Regidx 0x1a#5, regidx.Regidx 0x16#5, regidx.Regidx 0x16#5, ropw.SUBW))
    Register.x22 (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb v22 31 0) - (Sail.BitVec.extractLsb v26 31 0)))
    (0x3b#8) (0x0b#8) (0xab#8) (0x41#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_41ab0b3b (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtypew_subw_char (regidx.Regidx 0x1a#5) (regidx.Regidx 0x16#5) (regidx.Regidx 0x16#5)
      v22 v26 (afterNextPC (afterPrelude σ) (0x80008368#64))
      (sigma3_alu σ (0x80008368#64) Register.x22
        (sign_extend (m := 64) ((Sail.BitVec.extractLsb v22 31 0) - (Sail.BitVec.extractLsb v26 31 0))))
      (rX_bits_x22 _ v22 hx22₂) (rX_bits_x26 _ v26 hx26₂)
      (wX_bits_x22 _ (sign_extend (m := 64)
        ((Sail.BitVec.extractLsb v22 31 0) - (Sail.BitVec.extractLsb v26 31 0)))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000836c: `sd s7,40(sp)` (`sd`). -/
theorem site_8000836c_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp vdata : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hdata : σ.regs.get? Register.x23 = some vdata)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x8000836c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x028#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x028#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8000836c#64)).mem
        (vsp + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vdata) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x8000836c#64)).mem
            (vsp + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vdata))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000836c hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x8000836c#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x8000836c#64) _ (by decide) (by decide)]; exact hx2
  have hdata₂ : (afterNextPC (afterPrelude σ) (0x8000836c#64)).regs.get? Register.x23 = some vdata := by
    rw [get?_afterNextPC σ (0x8000836c#64) _ (by decide) (by decide)]; exact hdata
  exact stepObs_store σ i u (0x8000836c#64) vminstret (0x03713423#32)
    (instruction.STORE (0x028#12, regidx.Regidx 0x17#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8000836c#64)).mem
      (vsp + sign_extend (m := 64) (0x028#12)).toNat (sdData_val vdata))
    (0x23#8) (0x34#8) (0x71#8) (0x03#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_03713423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000836c#64) (0x028#12) (regidx.Regidx 0x17#5) (regidx.Regidx 0x02#5)
      vsp vdata hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_x23 _ vdata hdata₂)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008370: `ld t3,32(sp)` (value `ld`). -/
theorem site_80008370_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008370#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x020#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x020#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x020#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x020#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x020#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x020#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x020#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x020#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x020#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x020#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x28
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008370 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80008370#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80008370#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80008370#64) vminstret (0x02013e03#32)
    (instruction.LOAD (0x020#12, regidx.Regidx 0x02#5, regidx.Regidx 0x1c#5, false, 8))
    Register.x28 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x3e#8) (0x01#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02013e03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80008370#64) (0x020#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x1c#5)
      (sigma3_alu σ (0x80008370#64) Register.x28
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x28 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008374: `ld s7,48(sp)` (value `ld`). -/
theorem site_80008374_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008374#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x030#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x030#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x030#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x030#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x030#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x030#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x030#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x030#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x030#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x030#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x23
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008374 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80008374#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80008374#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80008374#64) vminstret (0x03013b83#32)
    (instruction.LOAD (0x030#12, regidx.Regidx 0x02#5, regidx.Regidx 0x17#5, false, 8))
    Register.x23 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x83#8) (0x3b#8) (0x01#8) (0x03#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_03013b83 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80008374#64) (0x030#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x17#5)
      (sigma3_alu σ (0x80008374#64) Register.x23
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x23 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008378: `ld s0,120(sp)` (value `ld`). -/
theorem site_80008378_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008378#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x078#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x078#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x078#12)).toNat)
    (halign : (vsp + sign_extend (m := 64) (0x078#12)).toNat % 8 = 0)
    (h0 : σ.mem[(vsp + sign_extend (m := 64) (0x078#12)).toNat]? = some b0)
    (h1 : σ.mem[(vsp + sign_extend (m := 64) (0x078#12)).toNat + 1]? = some b1)
    (h2 : σ.mem[(vsp + sign_extend (m := 64) (0x078#12)).toNat + 2]? = some b2)
    (h3 : σ.mem[(vsp + sign_extend (m := 64) (0x078#12)).toNat + 3]? = some b3)
    (h4 : σ.mem[(vsp + sign_extend (m := 64) (0x078#12)).toNat + 4]? = some b4)
    (h5 : σ.mem[(vsp + sign_extend (m := 64) (0x078#12)).toNat + 5]? = some b5)
    (h6 : σ.mem[(vsp + sign_extend (m := 64) (0x078#12)).toNat + 6]? = some b6)
    (h7 : σ.mem[(vsp + sign_extend (m := 64) (0x078#12)).toNat + 7]? = some b7) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x8
          (sign_extend (m := 64)
            ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
              : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008378 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80008378#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80008378#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80008378#64) vminstret (0x07813403#32)
    (instruction.LOAD (0x078#12, regidx.Regidx 0x02#5, regidx.Regidx 0x08#5, false, 8))
    Register.x8 (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)))
    (0x03#8) (0x34#8) (0x81#8) (0x07#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_07813403 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80008378#64) (0x078#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x08#5)
      (sigma3_alu σ (0x80008378#64) Register.x8
        (sign_extend (m := 64)
          ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
            : BitVec (8 * 8))))
      vsp b0 b1 b2 b3 b4 b5 b6 b7 hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x8 _ (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))))
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000837c: `addiw a6,s4,0` (a6 := width) (`addiw`). -/
theorem site_8000837c_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x8000837c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x16
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb (v20 + sign_extend (m := 64) (0x000#12)) 31 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000837c hmem
  have hx₂ : (afterNextPC (afterPrelude σ) (0x8000837c#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x8000837c#64) _ (by decide) (by decide)]; exact hx20
  exact stepObs_alu σ i u (0x8000837c#64) vminstret (0x000a081b#32)
    (instruction.ADDIW (0x000#12, regidx.Regidx 0x14#5, regidx.Regidx 0x10#5))
    Register.x16 (sign_extend (m := 64)
      (Sail.BitVec.extractLsb (v20 + sign_extend (m := 64) (0x000#12)) 31 0))
    (0x1b#8) (0x08#8) (0x0a#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_000a081b (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_addiw_char (0x000#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x10#5) v20
      (afterNextPC (afterPrelude σ) (0x8000837c#64))
      (sigma3_alu σ (0x8000837c#64) Register.x16
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v20 + sign_extend (m := 64) (0x000#12)) 31 0)))
      (rX_bits_x20 _ v20 hx₂)
      (wX_bits_x16 _ (sign_extend (m := 64)
        (Sail.BitVec.extractLsb (v20 + sign_extend (m := 64) (0x000#12)) 31 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008380: `bge s4,s6` not taken (`width < len`). -/
theorem site_80008380_nottaken_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 v22 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hx22 : σ.regs.get? Register.x22 = some v22)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008380#64 : BitVec 64))
    (hv : zopz0zKzJ_s v20 v22 = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008380 hmem
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x80008380#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x80008380#64) _ (by decide) (by decide)]; exact hx20
  have hx22₂ : (afterNextPC (afterPrelude σ) (0x80008380#64)).regs.get? Register.x22 = some v22 := by
    rw [get?_afterNextPC σ (0x80008380#64) _ (by decide) (by decide)]; exact hx22
  exact stepObs_branch_nottaken σ i u (0x80008380#64) vminstret (0x0008#13)
    (regidx.Regidx 0x14#5) (regidx.Regidx 0x16#5) bop.BGE (0x016a5463#32) (0x63#8) (0x54#8) (0x6a#8) (0x01#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_016a5463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bge_nottaken (0x0008#13) (regidx.Regidx 0x14#5) (regidx.Regidx 0x16#5) v20 v22
      (afterNextPC (afterPrelude σ) (0x80008380#64))
      (rX_bits_x20 _ v20 hx20₂) (rX_bits_x22 _ v22 hx22₂) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008384: `addiw a6,s6,0` (a6 := len) (`addiw`). -/
theorem site_80008384_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v22 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx22 : σ.regs.get? Register.x22 = some v22)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008384#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x16
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb (v22 + sign_extend (m := 64) (0x000#12)) 31 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008384 hmem
  have hx₂ : (afterNextPC (afterPrelude σ) (0x80008384#64)).regs.get? Register.x22 = some v22 := by
    rw [get?_afterNextPC σ (0x80008384#64) _ (by decide) (by decide)]; exact hx22
  exact stepObs_alu σ i u (0x80008384#64) vminstret (0x000b081b#32)
    (instruction.ADDIW (0x000#12, regidx.Regidx 0x16#5, regidx.Regidx 0x10#5))
    Register.x16 (sign_extend (m := 64)
      (Sail.BitVec.extractLsb (v22 + sign_extend (m := 64) (0x000#12)) 31 0))
    (0x1b#8) (0x08#8) (0x0b#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_000b081b (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_addiw_char (0x000#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x10#5) v22
      (afterNextPC (afterPrelude σ) (0x80008384#64))
      (sigma3_alu σ (0x80008384#64) Register.x16
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v22 + sign_extend (m := 64) (0x000#12)) 31 0)))
      (rX_bits_x22 _ v22 hx₂)
      (wX_bits_x16 _ (sign_extend (m := 64)
        (Sail.BitVec.extractLsb (v22 + sign_extend (m := 64) (0x000#12)) 31 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008388: `lbu t5,167(sp)` — the sign-byte read-back. -/
theorem site_80008388_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64) (b0v : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008388#64 : BitVec 64))
    (hlo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat)
    (hhiram : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat + 1 ≤ 0x100000000)
    (hhtif : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat + 1 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat)
    (hb0v : σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some b0v) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x30 (zero_extend (m := 64) b0v)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008388 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80008388#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80008388#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80008388#64) vminstret (0x0a714f03#32)
    (instruction.LOAD (0x0a7#12, regidx.Regidx 0x02#5, regidx.Regidx 0x1e#5, true, 1))
    Register.x30 (zero_extend (m := 64) b0v)
    (0x03#8) (0x4f#8) (0x71#8) (0x0a#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0a714f03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lbu_gen σ (0x80008388#64) (0x0a7#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x1e#5)
      vsp b0v _ hG (rX_bits_x2 _ vsp hx2₂)
      (wX_bits_x30 _ (zero_extend (m := 64) b0v))
      hlo hhiram hhtif hb0v)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000838c: `li t6,0`. -/
theorem site_8000838c_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x8000838c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x31 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000838c hmem
  exact stepObs_alu σ i u (0x8000838c#64) vminstret (0x00000f93#32)
    (instruction.ITYPE (0x000#12, regidx.Regidx 0x00#5, regidx.Regidx 0x1f#5, iop.ADDI))
    Register.x31 ((0#64) + sign_extend (m := 64) (0x000#12))
    (0x93#8) (0x0f#8) (0x00#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_00000f93 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x1f#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x8000838c#64))
      (sigma3_alu σ (0x8000838c#64) Register.x31 ((0#64) + sign_extend (m := 64) (0x000#12)))
      (rX_bits_zero _) (wX_bits_x31 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008390: `sd zero,32(sp)` (`sd`). -/
theorem site_80008390_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008390#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x020#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x020#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x80008390#64)).mem
        (vsp + sign_extend (m := 64) (0x020#12)).toNat (sdData_val (0#64)) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x80008390#64)).mem
            (vsp + sign_extend (m := 64) (0x020#12)).toNat (sdData_val (0#64)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008390 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80008390#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x80008390#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_store σ i u (0x80008390#64) vminstret (0x02013023#32)
    (instruction.STORE (0x020#12, regidx.Regidx 0x00#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80008390#64)).mem
      (vsp + sign_extend (m := 64) (0x020#12)).toNat (sdData_val (0#64)))
    (0x23#8) (0x30#8) (0x01#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02013023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80008390#64) (0x020#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x02#5)
      vsp (0#64) hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_zero _)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008394: `j 0x8000812c` (`j`). -/
theorem site_80008394_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008394#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1ffd98#21)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1ffd98#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008394 hmem
  exact stepObs_j σ i u (0x80008394#64) vminstret (0xd99ff06f#32) (0x1ffd98#21)
    (0x6f#8) (0xf0#8) (0x9f#8) (0xd9#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_d99ff06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

/-- 0x8000812c: `beq t5,zero` not taken (sign byte present). -/
theorem site_8000812c_nottaken_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v30 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx30 : σ.regs.get? Register.x30 = some v30)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x8000812c#64 : BitVec 64))
    (hv : (v30 == (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000812c hmem
  have hx30₂ : (afterNextPC (afterPrelude σ) (0x8000812c#64)).regs.get? Register.x30 = some v30 := by
    rw [get?_afterNextPC σ (0x8000812c#64) _ (by decide) (by decide)]; exact hx30
  exact stepObs_branch_nottaken σ i u (0x8000812c#64) vminstret (0x1f5c#13)
    (regidx.Regidx 0x1e#5) (regidx.Regidx 0x00#5) bop.BEQ (0xf40f0ee3#32) (0xe3#8) (0x0e#8) (0x0f#8) (0xf4#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_f40f0ee3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_beq_nottaken (0x1f5c#13) (regidx.Regidx 0x1e#5) (regidx.Regidx 0x00#5) v30 (0#64)
      (afterNextPC (afterPrelude σ) (0x8000812c#64))
      (rX_bits_x30 _ v30 hx30₂) (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008130: `addiw a6,a6,1` (len += sign) (`addiw`). -/
theorem site_80008130_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v16 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx16 : σ.regs.get? Register.x16 = some v16)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008130#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ'
        (sigmaPost_alu σ pc vminstret Register.x16
          (sign_extend (m := 64)
            (Sail.BitVec.extractLsb (v16 + sign_extend (m := 64) (0x001#12)) 31 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008130 hmem
  have hx₂ : (afterNextPC (afterPrelude σ) (0x80008130#64)).regs.get? Register.x16 = some v16 := by
    rw [get?_afterNextPC σ (0x80008130#64) _ (by decide) (by decide)]; exact hx16
  exact stepObs_alu σ i u (0x80008130#64) vminstret (0x0018081b#32)
    (instruction.ADDIW (0x001#12, regidx.Regidx 0x10#5, regidx.Regidx 0x10#5))
    Register.x16 (sign_extend (m := 64)
      (Sail.BitVec.extractLsb (v16 + sign_extend (m := 64) (0x001#12)) 31 0))
    (0x1b#8) (0x08#8) (0x18#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_0018081b (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_addiw_char (0x001#12) (regidx.Regidx 0x10#5) (regidx.Regidx 0x10#5) v16
      (afterNextPC (afterPrelude σ) (0x80008130#64))
      (sigma3_alu σ (0x80008130#64) Register.x16
        (sign_extend (m := 64)
          (Sail.BitVec.extractLsb (v16 + sign_extend (m := 64) (0x001#12)) 31 0)))
      (rX_bits_x16 _ v16 hx₂)
      (wX_bits_x16 _ (sign_extend (m := 64)
        (Sail.BitVec.extractLsb (v16 + sign_extend (m := 64) (0x001#12)) 31 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x80008134: `j 0x80008088` (`j`). -/
theorem site_80008134_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008134#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1fff54#21)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1fff54#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008134 hmem
  exact stepObs_j σ i u (0x80008134#64) vminstret (0xf55ff06f#32) (0x1fff54#21)
    (0x6f#8) (0xf0#8) (0x5f#8) (0xf5#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_f55ff06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

/-- 0x80008088: `bne t6,zero` not taken (`t6 = 0`). -/
theorem site_80008088_nottaken_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v31 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx31 : σ.regs.get? Register.x31 = some v31)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x80008088#64 : BitVec 64))
    (hv : (v31 != (0#64)) = false) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vminstret) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_80008088 hmem
  have hx31₂ : (afterNextPC (afterPrelude σ) (0x80008088#64)).regs.get? Register.x31 = some v31 := by
    rw [get?_afterNextPC σ (0x80008088#64) _ (by decide) (by decide)]; exact hx31
  exact stepObs_branch_nottaken σ i u (0x80008088#64) vminstret (0x0008#13)
    (regidx.Regidx 0x1f#5) (regidx.Regidx 0x00#5) bop.BNE (0x000f9463#32) (0x63#8) (0x94#8) (0x0f#8) (0x00#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_000f9463 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_btype_bne_nottaken (0x0008#13) (regidx.Regidx 0x1f#5) (regidx.Regidx 0x00#5) v31 (0#64)
      (afterNextPC (afterPrelude σ) (0x80008088#64))
      (rX_bits_x31 _ v31 hx31₂) (rX_bits_zero _) hv)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000808c: `j 0x8000a830` (`j`). -/
theorem site_8000808c_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : SvfprintfSliceLoaded σ.mem)
    (hpcv : pc = (0x8000808c#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x0027a4#21)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x0027a4#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.svfprintfSlice_at_8000808c hmem
  exact stepObs_j σ i u (0x8000808c#64) vminstret (0x7a40206f#32) (0x0027a4#21)
    (0x6f#8) (0x20#8) (0x40#8) (0x7a#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_7a40206f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

/-- 0x8000a830: `sd zero,56(sp)` (clear pad state) (`sd`). -/
theorem site_8000a830_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Vsa.Sim.Code.FlushPinsLoaded σ.mem)
    (hpcv : pc = (0x8000a830#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x038#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x038#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8000a830#64)).mem
        (vsp + sign_extend (m := 64) (0x038#12)).toNat (sdData_val (0#64)) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x8000a830#64)).mem
            (vsp + sign_extend (m := 64) (0x038#12)).toNat (sdData_val (0#64)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.flushPins_at_8000a830 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x8000a830#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x8000a830#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_store σ i u (0x8000a830#64) vminstret (0x02013c23#32)
    (instruction.STORE (0x038#12, regidx.Regidx 0x00#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8000a830#64)).mem
      (vsp + sign_extend (m := 64) (0x038#12)).toNat (sdData_val (0#64)))
    (0x23#8) (0x3c#8) (0x01#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02013c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000a830#64) (0x038#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x02#5)
      vsp (0#64) hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_zero _)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000a834: `sd zero,48(sp)` (clear pad state) (`sd`). -/
theorem site_8000a834_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret vsp : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some vsp)
    (hmem : Vsa.Sim.Code.FlushPinsLoaded σ.mem)
    (hpcv : pc = (0x8000a834#64 : BitVec 64))
    (halo : 0x80000000 ≤ (vsp + sign_extend (m := 64) (0x030#12)).toNat)
    (hahiram : (vsp + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (vsp + sign_extend (m := 64) (0x030#12)).toNat)
    (haalign : (vsp + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeMap8 (afterNextPC (afterPrelude σ) (0x8000a834#64)).mem
        (vsp + sign_extend (m := 64) (0x030#12)).toNat (sdData_val (0#64)) ∧
      ReadsLikePost σ'
        (sigmaPost_store σ pc vminstret
          (writeMap8 (afterNextPC (afterPrelude σ) (0x8000a834#64)).mem
            (vsp + sign_extend (m := 64) (0x030#12)).toNat (sdData_val (0#64)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.flushPins_at_8000a834 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x8000a834#64)).regs.get? Register.x2 = some vsp := by
    rw [get?_afterNextPC σ (0x8000a834#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_store σ i u (0x8000a834#64) vminstret (0x02013823#32)
    (instruction.STORE (0x030#12, regidx.Regidx 0x00#5, regidx.Regidx 0x02#5, 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x8000a834#64)).mem
      (vsp + sign_extend (m := 64) (0x030#12)).toNat (sdData_val (0#64)))
    (0x23#8) (0x38#8) (0x01#8) (0x02#8)
    hG hpc hminstret (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_02013823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x8000a834#64) (0x030#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x02#5)
      vsp (0#64) hG (rX_bits_x2 _ vsp hx2₂) (rX_bits_zero _)
      halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- 0x8000a838: `j 0x8000782c` (to PRINT) (`j`). -/
theorem site_8000a838_fl
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Vsa.Sim.Code.FlushPinsLoaded σ.mem)
    (hpcv : pc = (0x8000a838#64 : BitVec 64))
    (htgt : (pc + sign_extend (m := 64) (0x1fcff4#21)).toNat % 4 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vminstret (pc + sign_extend (m := 64) (0x1fcff4#21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Vsa.Sim.Code.flushPins_at_8000a838 hmem
  exact stepObs_j σ i u (0x8000a838#64) vminstret (0xff5fc06f#32) (0x1fcff4#21)
    (0x6f#8) (0xc0#8) (0x5f#8) (0xff#8)
    hG hpc hminstret hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) (by decide)
    (by apply BitVec.eq_of_toNat_eq; decide)
    (Vsa.Sim.DecodeTable.decode_ff5fc06f (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    htgt hi

end Vsa.Sim
