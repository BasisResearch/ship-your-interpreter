import Vsa.Sim.SnprintfSpec43

/-!
# M3 Layer-3 — `SnprintfSpec47` : the NONNEG arm entry (`0x800080e4 → 0x80008100`)

The nonneg twin of the sign block + split: `mv a4,a3` (a4 := the value — the
magnitude IS the value, no negate), `bgez a3` **TAKEN** to `0x80008050`, and
`bltz s4` **TAKEN** (default precision `-1 < 0`) to the fast/multi split
`0x80008100`.  NO byte is written (`sp+167` keeps the prologue-cleared `0x00`),
the flag word `t1` is untouched (no `andi -129` on this path), memory is
unchanged.  Feeds `entryToDigits_spec` (Spec5, magnitude > 9) or the
single-digit fast path.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **The nonneg arm entry**: `0x800080e4 → 0x80008100`, 3 steps, memory
unchanged, `a4 = v` (the nonneg value = the magnitude), everything else
carried. -/
theorem armEntryNN_spec
    (v vsp vt1 v8 v20 v23 v28 v12 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800080e4#64))
    (hx13 : c.σ.regs.get? Register.x13 = some v)
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx23 : c.σ.regs.get? Register.x23 = some v23)
    (hx28 : c.σ.regs.get? Register.x28 = some v28)
    (hx12 : c.σ.regs.get? Register.x12 = some v12)
    (hnn : zopz0zKzJ_s v (0#64) = true)
    (hwneg : v20.toInt < 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧ c'.σ.mem = c.σ.mem ∧
      c'.σ.regs.get? Register.PC = some (0x80008100#64) ∧
      c'.σ.regs.get? Register.x14 = some v ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some vt1 ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x23 = some v23 ∧
      c'.σ.regs.get? Register.x28 = some v28 ∧
      c'.σ.regs.get? Register.x12 = some v12 ∧
      c'.σ.regs.get? Register.x13 = some v ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧
      KeepRegs midRegs5 c.σ c'.σ := by
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  -- the bltz guard: s4 < 0 (default precision -1)
  have hgbltz : zopz0zI_s v20 (0#64) = true := by
    unfold zopz0zI_s
    apply decide_eq_true
    simp only [BitVec.toInt_zero]
    omega
  -- === 0x800080e4: mv a4,a3 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800080e4_sn4 c.σ c.tick c.steps (0x800080e4#64) vmi0 v hG hpc hmi0 hx13 hload rfl htick
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
  have hx13_1 : σ1.regs.get? Register.x13 = some v :=
    obs_alu_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
  have hx6_1 : σ1.regs.get? Register.x6 = some vt1 :=
    obs_alu_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
  have hx8_1 : σ1.regs.get? Register.x8 = some v8 :=
    obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8
  have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20
  have hx23_1 : σ1.regs.get? Register.x23 = some v23 :=
    obs_alu_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23
  have hx28_1 : σ1.regs.get? Register.x28 = some v28 :=
    obs_alu_other hobs1 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28
  have hx12_1 : σ1.regs.get? Register.x12 = some v12 :=
    obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  -- === 0x800080e8: bgez a3 TAKEN → 0x80008050 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800080e8_taken_fs σ1 i1 (c.steps+1) (0x800080e8#64) vmi1 v
      hG1 hpc1 hmi1 hx13_1 hload1 rfl hnn hi1
  have hstep2 : Step ⟨σ1,i1,c.steps+1⟩ ⟨σ2,i2,c.steps+1+1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80008050#64) := by
    have := obs_btaken_pc hobs2
    rwa [site_800080e8_taken_fs_tgt] at this
  obtain ⟨vmi2, hmi2⟩ := obs_btaken_minstret hobs2
  have hx14_2 : σ2.regs.get? Register.x14 = some v :=
    obs_btaken_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_1
  have hx13_2 : σ2.regs.get? Register.x13 = some v :=
    obs_btaken_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_btaken_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx6_2 : σ2.regs.get? Register.x6 = some vt1 :=
    obs_btaken_other hobs2 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_1
  have hx8_2 : σ2.regs.get? Register.x8 = some v8 :=
    obs_btaken_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
  have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
    obs_btaken_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
  have hx23_2 : σ2.regs.get? Register.x23 = some v23 :=
    obs_btaken_other hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_1
  have hx28_2 : σ2.regs.get? Register.x28 = some v28 :=
    obs_btaken_other hobs2 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_1
  have hx12_2 : σ2.regs.get? Register.x12 = some v12 :=
    obs_btaken_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  -- === 0x80008050: bltz s4 TAKEN → 0x80008100 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80008050_taken_fs σ2 i2 (c.steps+1+1) (0x80008050#64) vmi2 v20
      hG2 hpc2 hmi2 hx20_2 hload2 rfl hgbltz hi2
  have hstep3 : Step ⟨σ2,i2,c.steps+1+1⟩ ⟨σ3,i3,c.steps+1+1+1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80008100#64) := by
    have := obs_btaken_pc hobs3
    rwa [site_80008050_taken_fs_tgt] at this
  have hx14_3 : σ3.regs.get? Register.x14 = some v :=
    obs_btaken_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_2
  have hx13_3 : σ3.regs.get? Register.x13 = some v :=
    obs_btaken_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_2
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_btaken_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx6_3 : σ3.regs.get? Register.x6 = some vt1 :=
    obs_btaken_other hobs3 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 :=
    obs_btaken_other hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_2
  have hx20_3 : σ3.regs.get? Register.x20 = some v20 :=
    obs_btaken_other hobs3 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_2
  have hx23_3 : σ3.regs.get? Register.x23 = some v23 :=
    obs_btaken_other hobs3 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_2
  have hx28_3 : σ3.regs.get? Register.x28 = some v28 :=
    obs_btaken_other hobs3 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_2
  have hx12_3 : σ3.regs.get? Register.x12 = some v12 :=
    obs_btaken_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
  have hkeep : KeepRegs midRegs5 c.σ σ3 := by
    have h0 := keep_rfl midRegs5 c.σ
    have h1 := keep_alu hobs1 (by decide) h0
    have h2 := keep_btaken hobs2 (by decide) h1
    exact keep_btaken hobs3 (by decide) h2
  refine ⟨⟨σ3, i3, c.steps+1+1+1⟩, ?_, hG3, by rw [hmem3, hmem2, hmem1], hpc3, hx14_3,
    hx2_3, hx6_3, hx8_3, hx20_3, hx23_3, hx28_3, hx12_3, hx13_3, hi3, hG3.minstret, hkeep⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans (Steps.single hstep3))

end Vsa.Sim
