import Vsa.Sim.SnprintfSitesFast
import Vsa.Sim.SnprintfSitesFast2
import Vsa.Sim.SnprintfSpec43
import Vsa.Sim.ObsAvoid

/-!
# M3 Layer-3 — `SnprintfSpec45` : the NONNEG single-digit arm (`_f45`)

From the value-arm entry `0x800080e4` with the loaded argument `v` NON-NEGATIVE
and `v.toNat ≤ 9`: `mv a4,a3` → `bgez a3` TAKEN → `0x80008050 bltz s4` TAKEN
(default precision `-1`) → the `0x80008100` split → the single-digit fast path
(digit `sb` at `sp+347`) → the `0x80008ea4` tail block (sign read-back reads the
prologue-cleared `0x00`) → seam `0x8000812c` `beqz t5` **TAKEN** (no sign byte;
`a6` stays `1 = len`) → `0x8088`/`0xa830` hops → the PRINT entry `0x8000782c`.

NO sign byte is written on this path — `sp+167` still holds `0x00` at exit and
the downstream PRINT segment will emit a SINGLE iovec (count 1).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded ArmPinsLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **The nonneg single-digit arm**: `0x800080e4 → 0x8000782c`. -/
theorem entryToPrintNN_fast_spec
    (v vsp vt1 v8 v20 v23 v28 : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hap : ArmPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800080e4#64))
    (hx13 : c.σ.regs.get? Register.x13 = some v)
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx23 : c.σ.regs.get? Register.x23 = some v23)
    (hx28 : c.σ.regs.get? Register.x28 = some v28)
    (hnn : zopz0zKzJ_s v (0#64) = true)
    (hmag9 : v.toNat ≤ 9)
    (hwneg : v20.toInt < 0)
    (hz167 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8))
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000782c#64) ∧
      c'.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 1) ∧
      c'.σ.regs.get? Register.x16 = some (BitVec.ofNat 64 1) ∧
      c'.σ.regs.get? Register.x30 = some (0#64) ∧
      c'.σ.regs.get? Register.x31 = some (0#64) ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x6 = some vt1 ∧
      c'.σ.regs.get? Register.x28 = some v28 ∧
      c'.σ.regs.get? Register.x23 = some v23 ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1)) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧
      SlotHolds vsp 0x020 (0#64) c'.σ.mem ∧
      BufInv (entryTop vsp) v.toNat 1 c'.σ.mem ∧
      KeepRegs midRegs5 c.σ c'.σ ∧
      (∀ a : Nat, a ≠ vsp.toNat + 347 →
        ¬(vsp.toNat + 32 ≤ a ∧ a < vsp.toNat + 40) →
        ¬(vsp.toNat + 48 ≤ a ∧ a < vsp.toNat + 64) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      c'.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) ∧
      SvfprintfSliceLoaded c'.σ.mem ∧ FlushPinsLoaded c'.σ.mem ∧
      ArmPinsLoaded c'.σ.mem := by
  have htohv : tohostAddr = 0x8001ad00 := rfl
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff347 : (vsp + sign_extend (m := 64) (0x15b#12)).toNat = vsp.toNat + 347 :=
    addoff_toNat_sn5 vsp (0x15b#12) 347 (by omega) (by decide) hnw
  have hoff167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    addoff_toNat_sn5 vsp (0x0a7#12) 167 (by omega) (by decide) hnw
  have hoff32 : (vsp + sign_extend (m := 64) (0x020#12)).toNat = vsp.toNat + 32 :=
    addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw
  have hoff56 : (vsp + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat + 56 :=
    addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw
  have hoff48 : (vsp + sign_extend (m := 64) (0x030#12)).toNat = vsp.toNat + 48 :=
    addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw
  have htop_toNat : (entryTop vsp).toNat = vsp.toNat + 348 :=
    addoff_toNat_sn5 vsp (0x15c#12) 348 (by omega) (by decide) hnw
  have hg9 : zopz0zI_u ((0#64) + sign_extend (m := 64) (0x009#12)) v = false := by
    unfold zopz0zI_u
    simp only [Sail.BitVec.toNatInt,
      show ((0#64) + sign_extend (m := 64) (0x009#12) : BitVec 64).toNat = 9 from by decide]
    apply decide_eq_false
    intro hc
    exact absurd (Int.ofNat_lt.mp hc) (by omega)
  have hgbltz : zopz0zI_s v20 (0#64) = true := by
    unfold zopz0zI_s
    apply decide_eq_true
    simp only [BitVec.toInt_zero]
    omega
  have hgblez : zopz0zKzJ_s (0#64) v20 = true := by
    unfold zopz0zKzJ_s
    apply decide_eq_true
    simp only [BitVec.toInt_zero, ge_iff_le]
    omega
  -- step-0 aliases
  have hx2_0 := hx2
  have hx6_0 := hx6
  have hx20_0 := hx20
  have hx23_0 := hx23
  have hx8_0 := hx8
  have hx28_0 := hx28
  have hx13_0 := hx13
  have hload0 : SvfprintfSliceLoaded c.σ.mem := hload
  have hfp0 : FlushPinsLoaded c.σ.mem := hfp
  have hap0 : ArmPinsLoaded c.σ.mem := hap
  have hsb0 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hz167
  -- === 0x800080e4: mv a4,a3 — the (nonneg) magnitude ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800080e4_sn4 c.σ c.tick (c.steps) (0x800080e4#64) vmi0 v
      hG hpc hmi0 hx13_0 hload0 rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps+1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x800080e8#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800080e4#64 : BitVec 64) 4 = (0x800080e8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx14_1 : σ1.regs.get? Register.x14 = some (v + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show (v + sign_extend (m := 64) (0x000#12) : BitVec 64) = v from by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by decide]
    exact BitVec.add_zero v] at hx14_1
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs1 Register.x2 (by decide) hx2_0
  have hx6_1 : σ1.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs1 Register.x6 (by decide) hx6_0
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs1 Register.x20 (by decide) hx20_0
  have hx23_1 : σ1.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs1 Register.x23 (by decide) hx23_0
  have hx8_1 : σ1.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs1 Register.x8 (by decide) hx8_0
  have hx28_1 : σ1.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs1 Register.x28 (by decide) hx28_0
  have hx13_1 : σ1.regs.get? Register.x13 = some v :=
    obs_alu_other' hobs1 Register.x13 (by decide) hx13_0
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload0
  have hfp1 : FlushPinsLoaded σ1.mem := hmem1 ▸ hfp0
  have hap1 : ArmPinsLoaded σ1.mem := hmem1 ▸ hap0
  have hsb1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem1 ▸ hsb0

  -- === 0x800080e8: bgez a3 TAKEN (v nonneg) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800080e8_taken_fs σ1 i1 (c.steps+1) (0x800080e8#64) vmi1 v
      hG1 hpc1 hmi1 hx13_1 hload1 rfl hnn hi1
  have hstep2 : Step ⟨σ1,i1,c.steps+1⟩ ⟨σ2,i2,c.steps+1+1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80008050#64) := by
    have := obs_btaken_pc hobs2
    rwa [site_800080e8_taken_fs_tgt] at this
  obtain ⟨vmi2, hmi2⟩ := obs_btaken_minstret hobs2
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_btaken_other' hobs2 Register.x2 (by decide) hx2_1
  have hx6_2 : σ2.regs.get? Register.x6 = some vt1 :=
    obs_btaken_other' hobs2 Register.x6 (by decide) hx6_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_btaken_other' hobs2 Register.x20 (by decide) hx20_1
  have hx23_2 : σ2.regs.get? Register.x23 = some v23 :=
    obs_btaken_other' hobs2 Register.x23 (by decide) hx23_1
  have hx8_2 : σ2.regs.get? Register.x8 = some v8 :=
    obs_btaken_other' hobs2 Register.x8 (by decide) hx8_1
  have hx28_2 : σ2.regs.get? Register.x28 = some v28 :=
    obs_btaken_other' hobs2 Register.x28 (by decide) hx28_1
  have hx13_2 : σ2.regs.get? Register.x13 = some v :=
    obs_btaken_other' hobs2 Register.x13 (by decide) hx13_1
  have hx14_2 : σ2.regs.get? Register.x14 = some v :=
    obs_btaken_other' hobs2 Register.x14 (by decide) hx14_1
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have hfp2 : FlushPinsLoaded σ2.mem := hmem2 ▸ hfp1
  have hap2 : ArmPinsLoaded σ2.mem := hmem2 ▸ hap1
  have hsb2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem2 ▸ hsb1

  -- === 0x80008050: bltz s4 TAKEN (default precision -1) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80008050_taken_fs σ2 i2 (c.steps+1+1) (0x80008050#64) vmi2 v20
      hG2 hpc2 hmi2 hx20_2 hload2 rfl hgbltz hi2
  have hstep3 : Step ⟨σ2,i2,c.steps+1+1⟩ ⟨σ3,i3,c.steps+1+1+1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80008100#64) := by
    have := obs_btaken_pc hobs3
    rwa [site_80008050_taken_fs_tgt] at this
  obtain ⟨vmi3, hmi3⟩ := obs_btaken_minstret hobs3
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_btaken_other' hobs3 Register.x2 (by decide) hx2_2
  have hx6_3 : σ3.regs.get? Register.x6 = some vt1 :=
    obs_btaken_other' hobs3 Register.x6 (by decide) hx6_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_btaken_other' hobs3 Register.x20 (by decide) hx20_2
  have hx23_3 : σ3.regs.get? Register.x23 = some v23 :=
    obs_btaken_other' hobs3 Register.x23 (by decide) hx23_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 :=
    obs_btaken_other' hobs3 Register.x8 (by decide) hx8_2
  have hx28_3 : σ3.regs.get? Register.x28 = some v28 :=
    obs_btaken_other' hobs3 Register.x28 (by decide) hx28_2
  have hx14_3 : σ3.regs.get? Register.x14 = some v :=
    obs_btaken_other' hobs3 Register.x14 (by decide) hx14_2
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  have hfp3 : FlushPinsLoaded σ3.mem := hmem3 ▸ hfp2
  have hap3 : ArmPinsLoaded σ3.mem := hmem3 ▸ hap2
  have hsb3 : σ3.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem3 ▸ hsb2

  -- === 0x80008100: li a5,9 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80008100_sn5 σ3 i3 (c.steps+1+1+1) (0x80008100#64) vmi3
      hG3 hpc3 hmi3 hload3 rfl hi3
  have hstep4 : Step ⟨σ3,i3,c.steps+1+1+1⟩ ⟨σ4,i4,c.steps+1+1+1+1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80008104#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80008100#64 : BitVec 64) 4 = (0x80008104#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hx15_4 : σ4.regs.get? Register.x15 = some ((0#64) + sign_extend (m := 64) (0x009#12)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs4 Register.x2 (by decide) hx2_3
  have hx6_4 : σ4.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs4 Register.x6 (by decide) hx6_3
  have hx20_4 : σ4.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs4 Register.x20 (by decide) hx20_3
  have hx23_4 : σ4.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs4 Register.x23 (by decide) hx23_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs4 Register.x8 (by decide) hx8_3
  have hx28_4 : σ4.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs4 Register.x28 (by decide) hx28_3
  have hx14_4 : σ4.regs.get? Register.x14 = some v :=
    obs_alu_other' hobs4 Register.x14 (by decide) hx14_3
  have hload4 : SvfprintfSliceLoaded σ4.mem := hmem4 ▸ hload3
  have hfp4 : FlushPinsLoaded σ4.mem := hmem4 ▸ hfp3
  have hap4 : ArmPinsLoaded σ4.mem := hmem4 ▸ hap3
  have hsb4 : σ4.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem4 ▸ hsb3

  -- === 0x80008104: bltu a5,a4 NOT taken (v ≤ 9) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80008104_nottaken_fs σ4 i4 (c.steps+1+1+1+1) (0x80008104#64) vmi4 ((0#64) + sign_extend (m := 64) (0x009#12)) v
      hG4 hpc4 hmi4 hx15_4 hx14_4 hload4 rfl hg9 hi4
  have hstep5 : Step ⟨σ4,i4,c.steps+1+1+1+1⟩ ⟨σ5,i5,c.steps+1+1+1+1+1⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80008108#64) := by
    have := obs_bnottaken_pc hobs5
    rwa [show BitVec.addInt (0x80008104#64 : BitVec 64) 4 = (0x80008108#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_bnottaken_minstret hobs5
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_bnottaken_other' hobs5 Register.x2 (by decide) hx2_4
  have hx6_5 : σ5.regs.get? Register.x6 = some vt1 :=
    obs_bnottaken_other' hobs5 Register.x6 (by decide) hx6_4
  have hx20_5 : σ5.regs.get? Register.x20 = some v20 :=
    obs_bnottaken_other' hobs5 Register.x20 (by decide) hx20_4
  have hx23_5 : σ5.regs.get? Register.x23 = some v23 :=
    obs_bnottaken_other' hobs5 Register.x23 (by decide) hx23_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8 :=
    obs_bnottaken_other' hobs5 Register.x8 (by decide) hx8_4
  have hx28_5 : σ5.regs.get? Register.x28 = some v28 :=
    obs_bnottaken_other' hobs5 Register.x28 (by decide) hx28_4
  have hx14_5 : σ5.regs.get? Register.x14 = some v :=
    obs_bnottaken_other' hobs5 Register.x14 (by decide) hx14_4
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  have hfp5 : FlushPinsLoaded σ5.mem := hmem5 ▸ hfp4
  have hap5 : ArmPinsLoaded σ5.mem := hmem5 ▸ hap4
  have hsb5 : σ5.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem5 ▸ hsb4

  -- === 0x80008108: addiw a4,a4,48 — the digit char ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80008108_fs σ5 i5 (c.steps+1+1+1+1+1) (0x80008108#64) vmi5 v
      hG5 hpc5 hmi5 hx14_5 hload5 rfl hi5
  have hstep6 : Step ⟨σ5,i5,c.steps+1+1+1+1+1⟩ ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000810c#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80008108#64 : BitVec 64) 4 = (0x8000810c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hx14_6 : σ6.regs.get? Register.x14 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb (v + sign_extend (m := 64) (0x030#12)) 31 0)) :=
    obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs6 Register.x2 (by decide) hx2_5
  have hx6_6 : σ6.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs6 Register.x6 (by decide) hx6_5
  have hx20_6 : σ6.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs6 Register.x20 (by decide) hx20_5
  have hx23_6 : σ6.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs6 Register.x23 (by decide) hx23_5
  have hx8_6 : σ6.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs6 Register.x8 (by decide) hx8_5
  have hx28_6 : σ6.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs6 Register.x28 (by decide) hx28_5
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  have hfp6 : FlushPinsLoaded σ6.mem := hmem6 ▸ hfp5
  have hap6 : ArmPinsLoaded σ6.mem := hmem6 ▸ hap5
  have hsb6 : σ6.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem6 ▸ hsb5

  -- === 0x8000810c: sb a4,347(sp) — the single digit byte ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_8000810c_fs σ6 i6 (c.steps+1+1+1+1+1+1) (0x8000810c#64) vmi6 vsp (sign_extend (m := 64) (Sail.BitVec.extractLsb (v + sign_extend (m := 64) (0x030#12)) 31 0))
      hG6 hpc6 hmi6 hx2_6 hx14_6 hload6 rfl (by rw [hoff347]; omega) (by rw [hoff347]; omega) (by rw [hoff347]; omega) hi6
  have hstep7 : Step ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80008110#64) := by
    have := obs_store_pc_sn4 hobs7
    rwa [show BitVec.addInt (0x8000810c#64 : BitVec 64) 4 = (0x80008110#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret_sn4 hobs7
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4' Register.x2 hobs7 (by decide) hx2_6
  have hx6_7 : σ7.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4' Register.x6 hobs7 (by decide) hx6_6
  have hx20_7 : σ7.regs.get? Register.x20 = some v20 :=
    obs_store_other_sn4' Register.x20 hobs7 (by decide) hx20_6
  have hx23_7 : σ7.regs.get? Register.x23 = some v23 :=
    obs_store_other_sn4' Register.x23 hobs7 (by decide) hx23_6
  have hx8_7 : σ7.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4' Register.x8 hobs7 (by decide) hx8_6
  have hx28_7 : σ7.regs.get? Register.x28 = some v28 :=
    obs_store_other_sn4' Register.x28 hobs7 (by decide) hx28_6
  have hx14_7 : σ7.regs.get? Register.x14 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb (v + sign_extend (m := 64) (0x030#12)) 31 0)) :=
    obs_store_other_sn4' Register.x14 hobs7 (by decide) hx14_6
  have hNP6b : (afterNextPC (afterPrelude σ6) (0x8000810c#64)).mem = σ6.mem := rfl
  have hload7 : SvfprintfSliceLoaded σ7.mem := by
    rw [hmem7, hNP6b]; exact svfprintfSlice_insert_sn4 _ _ _ (by rw [hoff347]; omega) hload6
  have hfp7 : FlushPinsLoaded σ7.mem := by
    rw [hmem7, hNP6b]; exact flushPins_insert_fl _ _ _ (by rw [hoff347]; omega) hfp6
  have hap7 : ArmPinsLoaded σ7.mem := by
    rw [hmem7, hNP6b]; exact armPins_insert_43 _ _ _ (by rw [hoff347]; omega) hap6
  have hsb7 : σ7.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := by
    rw [hmem7, hNP6b, getElem_insert_ne _ ((vsp + sign_extend (m := 64) (0x0a7#12)).toNat) ((vsp + sign_extend (m := 64) (0x15b#12)).toNat) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; rw [hoff347, hoff167]; omega)]
    exact hsb6
  have hdig7 : σ7.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := by
    rw [hmem7, hNP6b, hoff347, ← fast_digit_byte_43 v hmag9]
    exact getElem_insert_self _ _ _

  -- === 0x80008110: sext.w a6,s4 (value dead) ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80008110_fs σ7 i7 (c.steps+1+1+1+1+1+1+1) (0x80008110#64) vmi7 v20
      hG7 hpc7 hmi7 hx20_7 hload7 rfl hi7
  have hstep8 : Step ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80008114#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80008110#64 : BitVec 64) 4 = (0x80008114#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hx16_8 : σ8.regs.get? Register.x16 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb (v20 + sign_extend (m := 64) (0x000#12)) 31 0)) :=
    obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_8 : σ8.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs8 Register.x2 (by decide) hx2_7
  have hx6_8 : σ8.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs8 Register.x6 (by decide) hx6_7
  have hx20_8 : σ8.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs8 Register.x20 (by decide) hx20_7
  have hx23_8 : σ8.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs8 Register.x23 (by decide) hx23_7
  have hx8_8 : σ8.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs8 Register.x8 (by decide) hx8_7
  have hx28_8 : σ8.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs8 Register.x28 (by decide) hx28_7
  have hload8 : SvfprintfSliceLoaded σ8.mem := hmem8 ▸ hload7
  have hfp8 : FlushPinsLoaded σ8.mem := hmem8 ▸ hfp7
  have hap8 : ArmPinsLoaded σ8.mem := hmem8 ▸ hap7
  have hsb8 : σ8.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem8 ▸ hsb7
  have hdig8 : σ8.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem8 ▸ hdig7

  -- === 0x80008114: blez s4 TAKEN ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80008114_taken_fs σ8 i8 (c.steps+1+1+1+1+1+1+1+1) (0x80008114#64) vmi8 v20
      hG8 hpc8 hmi8 hx20_8 hload8 rfl hgblez hi8
  have hstep9 : Step ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80008ea4#64) := by
    have := obs_btaken_pc hobs9
    rwa [site_80008114_taken_fs_tgt] at this
  obtain ⟨vmi9, hmi9⟩ := obs_btaken_minstret hobs9
  have hx2_9 : σ9.regs.get? Register.x2 = some vsp :=
    obs_btaken_other' hobs9 Register.x2 (by decide) hx2_8
  have hx6_9 : σ9.regs.get? Register.x6 = some vt1 :=
    obs_btaken_other' hobs9 Register.x6 (by decide) hx6_8
  have hx20_9 : σ9.regs.get? Register.x20 = some v20 :=
    obs_btaken_other' hobs9 Register.x20 (by decide) hx20_8
  have hx23_9 : σ9.regs.get? Register.x23 = some v23 :=
    obs_btaken_other' hobs9 Register.x23 (by decide) hx23_8
  have hx8_9 : σ9.regs.get? Register.x8 = some v8 :=
    obs_btaken_other' hobs9 Register.x8 (by decide) hx8_8
  have hx28_9 : σ9.regs.get? Register.x28 = some v28 :=
    obs_btaken_other' hobs9 Register.x28 (by decide) hx28_8
  have hload9 : SvfprintfSliceLoaded σ9.mem := hmem9 ▸ hload8
  have hfp9 : FlushPinsLoaded σ9.mem := hmem9 ▸ hfp8
  have hap9 : ArmPinsLoaded σ9.mem := hmem9 ▸ hap8
  have hsb9 : σ9.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem9 ▸ hsb8
  have hdig9 : σ9.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem9 ▸ hdig8

  -- === 0x80008ea4: lbu t5,167(sp) — reads 0x00 (no sign) ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80008ea4_fs2 σ9 i9 (c.steps+1+1+1+1+1+1+1+1+1) (0x80008ea4#64) vmi9 vsp (0x00#8)
      hG9 hpc9 hmi9 hx2_9 hap9 rfl (by rw [hoff167]; omega) (by rw [hoff167]; omega) (Or.inr (by rw [hoff167]; omega)) hsb9 hi9
  have hstep10 : Step ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ ⟨σ10,i10,c.steps+1+1+1+1+1+1+1+1+1+1⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80008ea8#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80008ea4#64 : BitVec 64) 4 = (0x80008ea8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hx30_10 : σ10.regs.get? Register.x30 = some (zero_extend (m := 64) (0x00#8)) :=
    obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show (zero_extend (m := 64) (0x00#8) : BitVec 64) = (0#64) from by decide] at hx30_10
  have hx2_10 : σ10.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs10 Register.x2 (by decide) hx2_9
  have hx6_10 : σ10.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs10 Register.x6 (by decide) hx6_9
  have hx20_10 : σ10.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs10 Register.x20 (by decide) hx20_9
  have hx23_10 : σ10.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs10 Register.x23 (by decide) hx23_9
  have hx8_10 : σ10.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs10 Register.x8 (by decide) hx8_9
  have hx28_10 : σ10.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs10 Register.x28 (by decide) hx28_9
  have hload10 : SvfprintfSliceLoaded σ10.mem := hmem10 ▸ hload9
  have hfp10 : FlushPinsLoaded σ10.mem := hmem10 ▸ hfp9
  have hap10 : ArmPinsLoaded σ10.mem := hmem10 ▸ hap9
  have hsb10 : σ10.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem10 ▸ hsb9
  have hdig10 : σ10.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem10 ▸ hdig9

  -- === 0x80008ea8: li a6,1 ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80008ea8_fs2 σ10 i10 (c.steps+1+1+1+1+1+1+1+1+1+1) (0x80008ea8#64) vmi10
      hG10 hpc10 hmi10 hap10 rfl hi10
  have hstep11 : Step ⟨σ10,i10,c.steps+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ11,i11,c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80008eac#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x80008ea8#64 : BitVec 64) 4 = (0x80008eac#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hx16_11 : σ11.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_11 : σ11.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs11 Register.x2 (by decide) hx2_10
  have hx6_11 : σ11.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs11 Register.x6 (by decide) hx6_10
  have hx20_11 : σ11.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs11 Register.x20 (by decide) hx20_10
  have hx23_11 : σ11.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs11 Register.x23 (by decide) hx23_10
  have hx8_11 : σ11.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs11 Register.x8 (by decide) hx8_10
  have hx28_11 : σ11.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs11 Register.x28 (by decide) hx28_10
  have hx30_11 : σ11.regs.get? Register.x30 = some (0#64) :=
    obs_alu_other' hobs11 Register.x30 (by decide) hx30_10
  have hload11 : SvfprintfSliceLoaded σ11.mem := hmem11 ▸ hload10
  have hfp11 : FlushPinsLoaded σ11.mem := hmem11 ▸ hfp10
  have hap11 : ArmPinsLoaded σ11.mem := hmem11 ▸ hap10
  have hsb11 : σ11.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem11 ▸ hsb10
  have hdig11 : σ11.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem11 ▸ hdig10

  -- === 0x80008eac: li t6,0 ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80008eac_fs2 σ11 i11 (c.steps+1+1+1+1+1+1+1+1+1+1+1) (0x80008eac#64) vmi11
      hG11 hpc11 hmi11 hap11 rfl hi11
  have hstep12 : Step ⟨σ11,i11,c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ12,i12,c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x80008eb0#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80008eac#64 : BitVec 64) 4 = (0x80008eb0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hx31_12 : σ12.regs.get? Register.x31 = some ((0#64) + sign_extend (m := 64) (0x000#12)) :=
    obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = (0#64) from by decide] at hx31_12
  have hx2_12 : σ12.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs12 Register.x2 (by decide) hx2_11
  have hx6_12 : σ12.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs12 Register.x6 (by decide) hx6_11
  have hx20_12 : σ12.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs12 Register.x20 (by decide) hx20_11
  have hx23_12 : σ12.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs12 Register.x23 (by decide) hx23_11
  have hx8_12 : σ12.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs12 Register.x8 (by decide) hx8_11
  have hx28_12 : σ12.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs12 Register.x28 (by decide) hx28_11
  have hx30_12 : σ12.regs.get? Register.x30 = some (0#64) :=
    obs_alu_other' hobs12 Register.x30 (by decide) hx30_11
  have hx16_12 : σ12.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other' hobs12 Register.x16 (by decide) hx16_11
  have hload12 : SvfprintfSliceLoaded σ12.mem := hmem12 ▸ hload11
  have hfp12 : FlushPinsLoaded σ12.mem := hmem12 ▸ hfp11
  have hap12 : ArmPinsLoaded σ12.mem := hmem12 ▸ hap11
  have hsb12 : σ12.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem12 ▸ hsb11
  have hdig12 : σ12.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem12 ▸ hdig11

  -- === 0x80008eb0: li s6,1 — the length ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80008eb0_fs2 σ12 i12 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008eb0#64) vmi12
      hG12 hpc12 hmi12 hap12 rfl hi12
  have hstep13 : Step ⟨σ12,i12,c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ13,i13,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80008eb4#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x80008eb0#64 : BitVec 64) 4 = (0x80008eb4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hx22_13 : σ13.regs.get? Register.x22 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_13 : σ13.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs13 Register.x2 (by decide) hx2_12
  have hx6_13 : σ13.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs13 Register.x6 (by decide) hx6_12
  have hx20_13 : σ13.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs13 Register.x20 (by decide) hx20_12
  have hx23_13 : σ13.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs13 Register.x23 (by decide) hx23_12
  have hx8_13 : σ13.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs13 Register.x8 (by decide) hx8_12
  have hx28_13 : σ13.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs13 Register.x28 (by decide) hx28_12
  have hx30_13 : σ13.regs.get? Register.x30 = some (0#64) :=
    obs_alu_other' hobs13 Register.x30 (by decide) hx30_12
  have hx16_13 : σ13.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other' hobs13 Register.x16 (by decide) hx16_12
  have hx31_13 : σ13.regs.get? Register.x31 = some (0#64) :=
    obs_alu_other' hobs13 Register.x31 (by decide) hx31_12
  have hload13 : SvfprintfSliceLoaded σ13.mem := hmem13 ▸ hload12
  have hfp13 : FlushPinsLoaded σ13.mem := hmem13 ▸ hfp12
  have hap13 : ArmPinsLoaded σ13.mem := hmem13 ▸ hap12
  have hsb13 : σ13.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem13 ▸ hsb12
  have hdig13 : σ13.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem13 ▸ hdig12

  -- === 0x80008eb4: addi s10,sp,347 — the digit base ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80008eb4_fs2 σ13 i13 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008eb4#64) vmi13 vsp
      hG13 hpc13 hmi13 hx2_13 hap13 rfl hi13
  have hstep14 : Step ⟨σ13,i13,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ14,i14,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x80008eb8#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x80008eb4#64 : BitVec 64) 4 = (0x80008eb8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hx26_14 : σ14.regs.get? Register.x26 = some (vsp + sign_extend (m := 64) (0x15b#12)) :=
    obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx2_14 : σ14.regs.get? Register.x2 = some vsp :=
    obs_alu_other' hobs14 Register.x2 (by decide) hx2_13
  have hx6_14 : σ14.regs.get? Register.x6 = some vt1 :=
    obs_alu_other' hobs14 Register.x6 (by decide) hx6_13
  have hx20_14 : σ14.regs.get? Register.x20 = some v20 :=
    obs_alu_other' hobs14 Register.x20 (by decide) hx20_13
  have hx23_14 : σ14.regs.get? Register.x23 = some v23 :=
    obs_alu_other' hobs14 Register.x23 (by decide) hx23_13
  have hx8_14 : σ14.regs.get? Register.x8 = some v8 :=
    obs_alu_other' hobs14 Register.x8 (by decide) hx8_13
  have hx28_14 : σ14.regs.get? Register.x28 = some v28 :=
    obs_alu_other' hobs14 Register.x28 (by decide) hx28_13
  have hx30_14 : σ14.regs.get? Register.x30 = some (0#64) :=
    obs_alu_other' hobs14 Register.x30 (by decide) hx30_13
  have hx16_14 : σ14.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other' hobs14 Register.x16 (by decide) hx16_13
  have hx31_14 : σ14.regs.get? Register.x31 = some (0#64) :=
    obs_alu_other' hobs14 Register.x31 (by decide) hx31_13
  have hx22_14 : σ14.regs.get? Register.x22 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_other' hobs14 Register.x22 (by decide) hx22_13
  have hload14 : SvfprintfSliceLoaded σ14.mem := hmem14 ▸ hload13
  have hfp14 : FlushPinsLoaded σ14.mem := hmem14 ▸ hfp13
  have hap14 : ArmPinsLoaded σ14.mem := hmem14 ▸ hap13
  have hsb14 : σ14.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem14 ▸ hsb13
  have hdig14 : σ14.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem14 ▸ hdig13

  -- === 0x80008eb8: j 0x80008128 ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80008eb8_fs2 σ14 i14 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008eb8#64) vmi14
      hG14 hpc14 hmi14 hap14 rfl (by decide) hi14
  have hstep15 : Step ⟨σ14,i14,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ15,i15,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80008128#64) := by
    have := obs_jx0_pc_sn5 hobs15
    rwa [show (0x80008eb8#64 : BitVec 64) + sign_extend (m := 64) (0x1ff270#21)
      = (0x80008128#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := hG15.minstret
  have hx2_15 : σ15.regs.get? Register.x2 = some vsp :=
    obs_jr_other' hobs15 Register.x2 (by decide) hx2_14
  have hx6_15 : σ15.regs.get? Register.x6 = some vt1 :=
    obs_jr_other' hobs15 Register.x6 (by decide) hx6_14
  have hx20_15 : σ15.regs.get? Register.x20 = some v20 :=
    obs_jr_other' hobs15 Register.x20 (by decide) hx20_14
  have hx23_15 : σ15.regs.get? Register.x23 = some v23 :=
    obs_jr_other' hobs15 Register.x23 (by decide) hx23_14
  have hx8_15 : σ15.regs.get? Register.x8 = some v8 :=
    obs_jr_other' hobs15 Register.x8 (by decide) hx8_14
  have hx28_15 : σ15.regs.get? Register.x28 = some v28 :=
    obs_jr_other' hobs15 Register.x28 (by decide) hx28_14
  have hx30_15 : σ15.regs.get? Register.x30 = some (0#64) :=
    obs_jr_other' hobs15 Register.x30 (by decide) hx30_14
  have hx16_15 : σ15.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_jr_other' hobs15 Register.x16 (by decide) hx16_14
  have hx31_15 : σ15.regs.get? Register.x31 = some (0#64) :=
    obs_jr_other' hobs15 Register.x31 (by decide) hx31_14
  have hx22_15 : σ15.regs.get? Register.x22 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_jr_other' hobs15 Register.x22 (by decide) hx22_14
  have hx26_15 : σ15.regs.get? Register.x26 = some (vsp + sign_extend (m := 64) (0x15b#12)) :=
    obs_jr_other' hobs15 Register.x26 (by decide) hx26_14
  have hload15 : SvfprintfSliceLoaded σ15.mem := hmem15 ▸ hload14
  have hfp15 : FlushPinsLoaded σ15.mem := hmem15 ▸ hfp14
  have hap15 : ArmPinsLoaded σ15.mem := hmem15 ▸ hap14
  have hsb15 : σ15.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem15 ▸ hsb14
  have hdig15 : σ15.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem15 ▸ hdig14

  -- === 0x80008128: sd zero,32(sp) ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80008128_fs σ15 i15 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008128#64) vmi15 vsp
      hG15 hpc15 hmi15 hx2_15 hload15 rfl (by rw [hoff32]; omega) (by rw [hoff32]; omega) (by rw [hoff32]; omega) (by rw [hoff32]; omega) hi15
  have hstep16 : Step ⟨σ15,i15,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ16,i16,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x8000812c#64) := by
    have := obs_store_pc_sn4 hobs16
    rwa [show BitVec.addInt (0x80008128#64 : BitVec 64) 4 = (0x8000812c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_store_minstret_sn4 hobs16
  have hx2_16 : σ16.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4' Register.x2 hobs16 (by decide) hx2_15
  have hx6_16 : σ16.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4' Register.x6 hobs16 (by decide) hx6_15
  have hx20_16 : σ16.regs.get? Register.x20 = some v20 :=
    obs_store_other_sn4' Register.x20 hobs16 (by decide) hx20_15
  have hx23_16 : σ16.regs.get? Register.x23 = some v23 :=
    obs_store_other_sn4' Register.x23 hobs16 (by decide) hx23_15
  have hx8_16 : σ16.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4' Register.x8 hobs16 (by decide) hx8_15
  have hx28_16 : σ16.regs.get? Register.x28 = some v28 :=
    obs_store_other_sn4' Register.x28 hobs16 (by decide) hx28_15
  have hx30_16 : σ16.regs.get? Register.x30 = some (0#64) :=
    obs_store_other_sn4' Register.x30 hobs16 (by decide) hx30_15
  have hx16_16 : σ16.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_store_other_sn4' Register.x16 hobs16 (by decide) hx16_15
  have hx31_16 : σ16.regs.get? Register.x31 = some (0#64) :=
    obs_store_other_sn4' Register.x31 hobs16 (by decide) hx31_15
  have hx22_16 : σ16.regs.get? Register.x22 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_store_other_sn4' Register.x22 hobs16 (by decide) hx22_15
  have hx26_16 : σ16.regs.get? Register.x26 = some (vsp + sign_extend (m := 64) (0x15b#12)) :=
    obs_store_other_sn4' Register.x26 hobs16 (by decide) hx26_15
  have hNP15b : (afterNextPC (afterPrelude σ15) (0x80008128#64)).mem = σ15.mem := rfl
  have hload16 : SvfprintfSliceLoaded σ16.mem := by
    rw [hmem16, hNP15b]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff32]; omega) hload15
  have hfp16 : FlushPinsLoaded σ16.mem := by
    rw [hmem16, hNP15b]; exact flushPins_writeMap8_fl _ _ _ (by rw [hoff32]; omega) hfp15
  have hap16 : ArmPinsLoaded σ16.mem := by
    rw [hmem16, hNP15b]; exact armPins_writeMap8_43 _ _ _ (by rw [hoff32]; omega) hap15
  have hsb16 : σ16.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := by
    rw [hmem16, hNP15b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff32, hoff167]; omega)]
    exact hsb15
  have hdig16 : σ16.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := by
    rw [hmem16, hNP15b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff32]; omega)]
    exact hdig15
  have hs32z16 : SlotHolds vsp 0x020 (0#64) σ16.mem := by
    rw [hmem16, hNP15b]
    exact slotHolds_self vsp 0x020 _ (0#64) σ15.mem rfl

  -- === 0x8000812c: beqz t5 TAKEN (no sign byte) ===
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_8000812c_taken_fs σ16 i16 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000812c#64) vmi16 (0#64)
      hG16 hpc16 hmi16 hx30_16 hload16 rfl (by decide) hi16
  have hstep17 : Step ⟨σ16,i16,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ17,i17,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x80008088#64) := by
    have := obs_btaken_pc hobs17
    rwa [site_8000812c_taken_fs_tgt] at this
  obtain ⟨vmi17, hmi17⟩ := obs_btaken_minstret hobs17
  have hx2_17 : σ17.regs.get? Register.x2 = some vsp :=
    obs_btaken_other' hobs17 Register.x2 (by decide) hx2_16
  have hx6_17 : σ17.regs.get? Register.x6 = some vt1 :=
    obs_btaken_other' hobs17 Register.x6 (by decide) hx6_16
  have hx20_17 : σ17.regs.get? Register.x20 = some v20 :=
    obs_btaken_other' hobs17 Register.x20 (by decide) hx20_16
  have hx23_17 : σ17.regs.get? Register.x23 = some v23 :=
    obs_btaken_other' hobs17 Register.x23 (by decide) hx23_16
  have hx8_17 : σ17.regs.get? Register.x8 = some v8 :=
    obs_btaken_other' hobs17 Register.x8 (by decide) hx8_16
  have hx28_17 : σ17.regs.get? Register.x28 = some v28 :=
    obs_btaken_other' hobs17 Register.x28 (by decide) hx28_16
  have hx30_17 : σ17.regs.get? Register.x30 = some (0#64) :=
    obs_btaken_other' hobs17 Register.x30 (by decide) hx30_16
  have hx16_17 : σ17.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_btaken_other' hobs17 Register.x16 (by decide) hx16_16
  have hx31_17 : σ17.regs.get? Register.x31 = some (0#64) :=
    obs_btaken_other' hobs17 Register.x31 (by decide) hx31_16
  have hx22_17 : σ17.regs.get? Register.x22 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_btaken_other' hobs17 Register.x22 (by decide) hx22_16
  have hx26_17 : σ17.regs.get? Register.x26 = some (vsp + sign_extend (m := 64) (0x15b#12)) :=
    obs_btaken_other' hobs17 Register.x26 (by decide) hx26_16
  have hload17 : SvfprintfSliceLoaded σ17.mem := hmem17 ▸ hload16
  have hfp17 : FlushPinsLoaded σ17.mem := hmem17 ▸ hfp16
  have hap17 : ArmPinsLoaded σ17.mem := hmem17 ▸ hap16
  have hsb17 : σ17.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem17 ▸ hsb16
  have hdig17 : σ17.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem17 ▸ hdig16
  have hs32z17 : SlotHolds vsp 0x020 (0#64) σ17.mem := hmem17 ▸ hs32z16

  -- === 0x80008088: bnez t6 NOT taken ===
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_80008088_nottaken_fl σ17 i17 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008088#64) vmi17 (0#64)
      hG17 hpc17 hmi17 hx31_17 hload17 rfl (by decide) hi17
  have hstep18 : Step ⟨σ17,i17,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ18,i18,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x8000808c#64) := by
    have := obs_bnottaken_pc hobs18
    rwa [show BitVec.addInt (0x80008088#64 : BitVec 64) 4 = (0x8000808c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi18, hmi18⟩ := obs_bnottaken_minstret hobs18
  have hx2_18 : σ18.regs.get? Register.x2 = some vsp :=
    obs_bnottaken_other' hobs18 Register.x2 (by decide) hx2_17
  have hx6_18 : σ18.regs.get? Register.x6 = some vt1 :=
    obs_bnottaken_other' hobs18 Register.x6 (by decide) hx6_17
  have hx20_18 : σ18.regs.get? Register.x20 = some v20 :=
    obs_bnottaken_other' hobs18 Register.x20 (by decide) hx20_17
  have hx23_18 : σ18.regs.get? Register.x23 = some v23 :=
    obs_bnottaken_other' hobs18 Register.x23 (by decide) hx23_17
  have hx8_18 : σ18.regs.get? Register.x8 = some v8 :=
    obs_bnottaken_other' hobs18 Register.x8 (by decide) hx8_17
  have hx28_18 : σ18.regs.get? Register.x28 = some v28 :=
    obs_bnottaken_other' hobs18 Register.x28 (by decide) hx28_17
  have hx30_18 : σ18.regs.get? Register.x30 = some (0#64) :=
    obs_bnottaken_other' hobs18 Register.x30 (by decide) hx30_17
  have hx16_18 : σ18.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_bnottaken_other' hobs18 Register.x16 (by decide) hx16_17
  have hx31_18 : σ18.regs.get? Register.x31 = some (0#64) :=
    obs_bnottaken_other' hobs18 Register.x31 (by decide) hx31_17
  have hx22_18 : σ18.regs.get? Register.x22 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_bnottaken_other' hobs18 Register.x22 (by decide) hx22_17
  have hx26_18 : σ18.regs.get? Register.x26 = some (vsp + sign_extend (m := 64) (0x15b#12)) :=
    obs_bnottaken_other' hobs18 Register.x26 (by decide) hx26_17
  have hload18 : SvfprintfSliceLoaded σ18.mem := hmem18 ▸ hload17
  have hfp18 : FlushPinsLoaded σ18.mem := hmem18 ▸ hfp17
  have hap18 : ArmPinsLoaded σ18.mem := hmem18 ▸ hap17
  have hsb18 : σ18.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem18 ▸ hsb17
  have hdig18 : σ18.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem18 ▸ hdig17
  have hs32z18 : SlotHolds vsp 0x020 (0#64) σ18.mem := hmem18 ▸ hs32z17

  -- === 0x8000808c: j 0x8000a830 ===
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_8000808c_fl σ18 i18 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000808c#64) vmi18
      hG18 hpc18 hmi18 hload18 rfl (by decide) hi18
  have hstep19 : Step ⟨σ18,i18,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ19,i19,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs19
  have hpc19 : σ19.regs.get? Register.PC = some (0x8000a830#64) := by
    have := obs_jx0_pc_sn5 hobs19
    rwa [show (0x8000808c#64 : BitVec 64) + sign_extend (m := 64) (0x0027a4#21)
      = (0x8000a830#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi19, hmi19⟩ := hG19.minstret
  have hx2_19 : σ19.regs.get? Register.x2 = some vsp :=
    obs_jr_other' hobs19 Register.x2 (by decide) hx2_18
  have hx6_19 : σ19.regs.get? Register.x6 = some vt1 :=
    obs_jr_other' hobs19 Register.x6 (by decide) hx6_18
  have hx20_19 : σ19.regs.get? Register.x20 = some v20 :=
    obs_jr_other' hobs19 Register.x20 (by decide) hx20_18
  have hx23_19 : σ19.regs.get? Register.x23 = some v23 :=
    obs_jr_other' hobs19 Register.x23 (by decide) hx23_18
  have hx8_19 : σ19.regs.get? Register.x8 = some v8 :=
    obs_jr_other' hobs19 Register.x8 (by decide) hx8_18
  have hx28_19 : σ19.regs.get? Register.x28 = some v28 :=
    obs_jr_other' hobs19 Register.x28 (by decide) hx28_18
  have hx30_19 : σ19.regs.get? Register.x30 = some (0#64) :=
    obs_jr_other' hobs19 Register.x30 (by decide) hx30_18
  have hx16_19 : σ19.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_jr_other' hobs19 Register.x16 (by decide) hx16_18
  have hx31_19 : σ19.regs.get? Register.x31 = some (0#64) :=
    obs_jr_other' hobs19 Register.x31 (by decide) hx31_18
  have hx22_19 : σ19.regs.get? Register.x22 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_jr_other' hobs19 Register.x22 (by decide) hx22_18
  have hx26_19 : σ19.regs.get? Register.x26 = some (vsp + sign_extend (m := 64) (0x15b#12)) :=
    obs_jr_other' hobs19 Register.x26 (by decide) hx26_18
  have hload19 : SvfprintfSliceLoaded σ19.mem := hmem19 ▸ hload18
  have hfp19 : FlushPinsLoaded σ19.mem := hmem19 ▸ hfp18
  have hap19 : ArmPinsLoaded σ19.mem := hmem19 ▸ hap18
  have hsb19 : σ19.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem19 ▸ hsb18
  have hdig19 : σ19.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem19 ▸ hdig18
  have hs32z19 : SlotHolds vsp 0x020 (0#64) σ19.mem := hmem19 ▸ hs32z18

  -- === 0x8000a830: sd zero,56(sp) ===
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_8000a830_fl σ19 i19 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000a830#64) vmi19 vsp
      hG19 hpc19 hmi19 hx2_19 hfp19 rfl (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega) hi19
  have hstep20 : Step ⟨σ19,i19,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ20,i20,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs20
  have hpc20 : σ20.regs.get? Register.PC = some (0x8000a834#64) := by
    have := obs_store_pc_sn4 hobs20
    rwa [show BitVec.addInt (0x8000a830#64 : BitVec 64) 4 = (0x8000a834#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi20, hmi20⟩ := obs_store_minstret_sn4 hobs20
  have hx2_20 : σ20.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4' Register.x2 hobs20 (by decide) hx2_19
  have hx6_20 : σ20.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4' Register.x6 hobs20 (by decide) hx6_19
  have hx20_20 : σ20.regs.get? Register.x20 = some v20 :=
    obs_store_other_sn4' Register.x20 hobs20 (by decide) hx20_19
  have hx23_20 : σ20.regs.get? Register.x23 = some v23 :=
    obs_store_other_sn4' Register.x23 hobs20 (by decide) hx23_19
  have hx8_20 : σ20.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4' Register.x8 hobs20 (by decide) hx8_19
  have hx28_20 : σ20.regs.get? Register.x28 = some v28 :=
    obs_store_other_sn4' Register.x28 hobs20 (by decide) hx28_19
  have hx30_20 : σ20.regs.get? Register.x30 = some (0#64) :=
    obs_store_other_sn4' Register.x30 hobs20 (by decide) hx30_19
  have hx16_20 : σ20.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_store_other_sn4' Register.x16 hobs20 (by decide) hx16_19
  have hx31_20 : σ20.regs.get? Register.x31 = some (0#64) :=
    obs_store_other_sn4' Register.x31 hobs20 (by decide) hx31_19
  have hx22_20 : σ20.regs.get? Register.x22 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_store_other_sn4' Register.x22 hobs20 (by decide) hx22_19
  have hx26_20 : σ20.regs.get? Register.x26 = some (vsp + sign_extend (m := 64) (0x15b#12)) :=
    obs_store_other_sn4' Register.x26 hobs20 (by decide) hx26_19
  have hNP19b : (afterNextPC (afterPrelude σ19) (0x8000a830#64)).mem = σ19.mem := rfl
  have hload20 : SvfprintfSliceLoaded σ20.mem := by
    rw [hmem20, hNP19b]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff56]; omega) hload19
  have hfp20 : FlushPinsLoaded σ20.mem := by
    rw [hmem20, hNP19b]; exact flushPins_writeMap8_fl _ _ _ (by rw [hoff56]; omega) hfp19
  have hap20 : ArmPinsLoaded σ20.mem := by
    rw [hmem20, hNP19b]; exact armPins_writeMap8_43 _ _ _ (by rw [hoff56]; omega) hap19
  have hsb20 : σ20.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := by
    rw [hmem20, hNP19b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff56, hoff167]; omega)]
    exact hsb19
  have hdig20 : σ20.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := by
    rw [hmem20, hNP19b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff56]; omega)]
    exact hdig19
  have hs32z20 : SlotHolds vsp 0x020 (0#64) σ20.mem := by
    rw [hmem20, hNP19b]
    exact slotHolds_writeMap8 vsp 0x020 (0#64) σ19.mem _ _ (by rw [hoff32, hoff56]; omega) hs32z19

  -- === 0x8000a834: sd zero,48(sp) ===
  obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
    site_8000a834_fl σ20 i20 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000a834#64) vmi20 vsp
      hG20 hpc20 hmi20 hx2_20 hfp20 rfl (by rw [hoff48]; omega) (by rw [hoff48]; omega) (by rw [hoff48]; omega) (by rw [hoff48]; omega) hi20
  have hstep21 : Step ⟨σ20,i20,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ21,i21,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs21
  have hpc21 : σ21.regs.get? Register.PC = some (0x8000a838#64) := by
    have := obs_store_pc_sn4 hobs21
    rwa [show BitVec.addInt (0x8000a834#64 : BitVec 64) 4 = (0x8000a838#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi21, hmi21⟩ := obs_store_minstret_sn4 hobs21
  have hx2_21 : σ21.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4' Register.x2 hobs21 (by decide) hx2_20
  have hx6_21 : σ21.regs.get? Register.x6 = some vt1 :=
    obs_store_other_sn4' Register.x6 hobs21 (by decide) hx6_20
  have hx20_21 : σ21.regs.get? Register.x20 = some v20 :=
    obs_store_other_sn4' Register.x20 hobs21 (by decide) hx20_20
  have hx23_21 : σ21.regs.get? Register.x23 = some v23 :=
    obs_store_other_sn4' Register.x23 hobs21 (by decide) hx23_20
  have hx8_21 : σ21.regs.get? Register.x8 = some v8 :=
    obs_store_other_sn4' Register.x8 hobs21 (by decide) hx8_20
  have hx28_21 : σ21.regs.get? Register.x28 = some v28 :=
    obs_store_other_sn4' Register.x28 hobs21 (by decide) hx28_20
  have hx30_21 : σ21.regs.get? Register.x30 = some (0#64) :=
    obs_store_other_sn4' Register.x30 hobs21 (by decide) hx30_20
  have hx16_21 : σ21.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_store_other_sn4' Register.x16 hobs21 (by decide) hx16_20
  have hx31_21 : σ21.regs.get? Register.x31 = some (0#64) :=
    obs_store_other_sn4' Register.x31 hobs21 (by decide) hx31_20
  have hx22_21 : σ21.regs.get? Register.x22 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_store_other_sn4' Register.x22 hobs21 (by decide) hx22_20
  have hx26_21 : σ21.regs.get? Register.x26 = some (vsp + sign_extend (m := 64) (0x15b#12)) :=
    obs_store_other_sn4' Register.x26 hobs21 (by decide) hx26_20
  have hNP20b : (afterNextPC (afterPrelude σ20) (0x8000a834#64)).mem = σ20.mem := rfl
  have hload21 : SvfprintfSliceLoaded σ21.mem := by
    rw [hmem21, hNP20b]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff48]; omega) hload20
  have hfp21 : FlushPinsLoaded σ21.mem := by
    rw [hmem21, hNP20b]; exact flushPins_writeMap8_fl _ _ _ (by rw [hoff48]; omega) hfp20
  have hap21 : ArmPinsLoaded σ21.mem := by
    rw [hmem21, hNP20b]; exact armPins_writeMap8_43 _ _ _ (by rw [hoff48]; omega) hap20
  have hsb21 : σ21.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := by
    rw [hmem21, hNP20b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff48, hoff167]; omega)]
    exact hsb20
  have hdig21 : σ21.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := by
    rw [hmem21, hNP20b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff48]; omega)]
    exact hdig20
  have hs32z21 : SlotHolds vsp 0x020 (0#64) σ21.mem := by
    rw [hmem21, hNP20b]
    exact slotHolds_writeMap8 vsp 0x020 (0#64) σ20.mem _ _ (by rw [hoff32, hoff48]; omega) hs32z20

  -- === 0x8000a838: j 0x8000782c — the PRINT entry ===
  obtain ⟨σ22, i22, hs22, hi22, hG22, hmem22, hobs22⟩ :=
    site_8000a838_fl σ21 i21 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000a838#64) vmi21
      hG21 hpc21 hmi21 hfp21 rfl (by decide) hi21
  have hstep22 : Step ⟨σ21,i21,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ22,i22,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs22
  have hpc22 : σ22.regs.get? Register.PC = some (0x8000782c#64) := by
    have := obs_jx0_pc_sn5 hobs22
    rwa [show (0x8000a838#64 : BitVec 64) + sign_extend (m := 64) (0x1fcff4#21)
      = (0x8000782c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi22, hmi22⟩ := hG22.minstret
  have hx2_22 : σ22.regs.get? Register.x2 = some vsp :=
    obs_jr_other' hobs22 Register.x2 (by decide) hx2_21
  have hx6_22 : σ22.regs.get? Register.x6 = some vt1 :=
    obs_jr_other' hobs22 Register.x6 (by decide) hx6_21
  have hx20_22 : σ22.regs.get? Register.x20 = some v20 :=
    obs_jr_other' hobs22 Register.x20 (by decide) hx20_21
  have hx23_22 : σ22.regs.get? Register.x23 = some v23 :=
    obs_jr_other' hobs22 Register.x23 (by decide) hx23_21
  have hx8_22 : σ22.regs.get? Register.x8 = some v8 :=
    obs_jr_other' hobs22 Register.x8 (by decide) hx8_21
  have hx28_22 : σ22.regs.get? Register.x28 = some v28 :=
    obs_jr_other' hobs22 Register.x28 (by decide) hx28_21
  have hx30_22 : σ22.regs.get? Register.x30 = some (0#64) :=
    obs_jr_other' hobs22 Register.x30 (by decide) hx30_21
  have hx16_22 : σ22.regs.get? Register.x16 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_jr_other' hobs22 Register.x16 (by decide) hx16_21
  have hx31_22 : σ22.regs.get? Register.x31 = some (0#64) :=
    obs_jr_other' hobs22 Register.x31 (by decide) hx31_21
  have hx22_22 : σ22.regs.get? Register.x22 = some ((0#64) + sign_extend (m := 64) (0x001#12)) :=
    obs_jr_other' hobs22 Register.x22 (by decide) hx22_21
  have hx26_22 : σ22.regs.get? Register.x26 = some (vsp + sign_extend (m := 64) (0x15b#12)) :=
    obs_jr_other' hobs22 Register.x26 (by decide) hx26_21
  have hload22 : SvfprintfSliceLoaded σ22.mem := hmem22 ▸ hload21
  have hfp22 : FlushPinsLoaded σ22.mem := hmem22 ▸ hfp21
  have hap22 : ArmPinsLoaded σ22.mem := hmem22 ▸ hap21
  have hsb22 : σ22.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := hmem22 ▸ hsb21
  have hdig22 : σ22.mem[vsp.toNat + 347]? = some (BitVec.ofNat 8 (48 + v.toNat)) := hmem22 ▸ hdig21
  have hs32z22 : SlotHolds vsp 0x020 (0#64) σ22.mem := hmem22 ▸ hs32z21

  -- x22 = 1 and x16 = 1 (fold the li forms)
  rw [show ((0#64) + sign_extend (m := 64) (0x001#12) : BitVec 64) = BitVec.ofNat 64 1 from by
    apply BitVec.eq_of_toNat_eq; decide] at hx22_22 hx16_22
  -- x26 = ofNat (top−1)
  rw [show (vsp + sign_extend (m := 64) (0x15b#12) : BitVec 64)
      = BitVec.ofNat 64 ((entryTop vsp).toNat - 1) from by
    apply BitVec.eq_of_toNat_eq
    rw [hoff347, htop_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega] at hx26_22
  -- the one-digit buffer
  have hbuf : BufInv (entryTop vsp) v.toNat 1 σ22.mem := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    have hkey : (entryTop vsp).toNat - 1 - 0 = vsp.toNat + 347 := by
      rw [htop_toNat]; omega
    have hval : 48 + (v.toNat / 10 ^ 0) % 10 = 48 + v.toNat := by
      simp only [Nat.pow_zero, Nat.div_one]
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [hkey, hval]
    exact hdig22
  -- mid-register preservation across all 22 steps
  have hkeep : KeepRegs midRegs5 c.σ σ22 := by
    have h0 := keep_rfl midRegs5 c.σ
    have h1 := keep_alu hobs1 (by decide) h0
    have h2 := keep_btaken hobs2 (by decide) h1
    have h3 := keep_btaken hobs3 (by decide) h2
    have h4 := keep_alu hobs4 (by decide) h3
    have h5 := keep_bnottaken hobs5 (by decide) h4
    have h6 := keep_alu hobs6 (by decide) h5
    have h7 := keep_store hobs7 (by decide) h6
    have h8 := keep_alu hobs8 (by decide) h7
    have h9 := keep_btaken hobs9 (by decide) h8
    have h10 := keep_alu hobs10 (by decide) h9
    have h11 := keep_alu hobs11 (by decide) h10
    have h12 := keep_alu hobs12 (by decide) h11
    have h13 := keep_alu hobs13 (by decide) h12
    have h14 := keep_alu hobs14 (by decide) h13
    have h15 := keep_jr hobs15 (by decide) h14
    have h16 := keep_store hobs16 (by decide) h15
    have h17 := keep_btaken hobs17 (by decide) h16
    have h18 := keep_bnottaken hobs18 (by decide) h17
    have h19 := keep_jr hobs19 (by decide) h18
    have h20 := keep_store hobs20 (by decide) h19
    have h21 := keep_store hobs21 (by decide) h20
    exact keep_jr hobs22 (by decide) h21
  -- pointwise frame
  have hmframe : ∀ a : Nat, a ≠ vsp.toNat + 347 →
      ¬(vsp.toNat + 32 ≤ a ∧ a < vsp.toNat + 40) →
      ¬(vsp.toNat + 48 ≤ a ∧ a < vsp.toNat + 64) →
      σ22.mem[a]? = c.σ.mem[a]? := by
    intro a hd hA hB
    rw [hmem22, hmem21, hNP20b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff48]; omega),
      hmem20, hNP19b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff56]; omega),
      hmem19, hmem18, hmem17,
      hmem16, hNP15b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff32]; omega),
      hmem15, hmem14, hmem13, hmem12, hmem11, hmem10, hmem9, hmem8,
      hmem7, hNP6b, getElem_insert_ne _ a ((vsp + sign_extend (m := 64) (0x15b#12)).toNat) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; rw [hoff347]; omega),
      hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  refine ⟨⟨σ22, i22, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩, ?_, hG22, hpc22, hx22_22, hx16_22,
    hx30_22, hx31_22, hx20_22, hx6_22, hx28_22, hx23_22, hx8_22, hx2_22, hx26_22,
    hi22, hG22.minstret, hs32z22, hbuf, hkeep, hmframe, hsb22, hload22, hfp22, hap22⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans ((Steps.single hstep19).trans ((Steps.single hstep20).trans ((Steps.single hstep21).trans (Steps.single hstep22)))))))))))))))))))))

end Vsa.Sim
