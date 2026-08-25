import Vsa.Sim.SnprintfSpec22

/-!
# M3 Layer-3 — `SnprintfSpec23` : flush return, segment C
## `0x80007960` (mbtowc = 0 arm) → `0x800079b0` (svfprintf epilogue head)

The NUL-exit hop: `mbtowc` returned 0, so the loop computes the length of the
pending literal text (`s6 - fmt0 = 0` — the cursor never moved past the NUL)
and, finding it zero, falls through to the epilogue:

```
  80007960: ld   a5,0(sp)          a5 := fmt cursor (= s6)
  80007964: mv   s4,a0             s4 := 0 (the mbtowc result)
  80007968: subw s8,s6,a5          s8 := sext32(s6₃₂ - a5₃₂) = 0
  8000796c: beqz s8,800079b0       TAKEN → epilogue
```

`retC_spec`: 4 sites, no memory writes.  The `subw` guard closes structurally
(`x - x = 0`) — `s6` and `a5` are the *same* slot value `vcur`. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

theorem pins_drop2_rt {σ : MState} {a b : Pin} {L : List Pin}
    (h : PinsHold σ (a :: b :: L)) : PinsHold σ (a :: L) :=
  ⟨h.1, h.2.2⟩

/-- `subw` of a register against itself is zero. -/
theorem subw_self_rt (v : BitVec 64) :
    (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb v 31 0) - (Sail.BitVec.extractLsb v 31 0)) : BitVec 64)
      = 0#64 := by
  rw [BitVec.sub_self]
  apply BitVec.eq_of_toNat_eq; decide

/-- **Segment C of the flush return**: `0x80007960 → 0x800079b0`. -/
theorem retC_spec (vsp vcur va0 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007960#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx10 : c.σ.regs.get? Register.x10 = some va0)
    (hx22 : c.σ.regs.get? Register.x22 = some vcur)
    (hslot0 : SlotHolds vsp 0x000 vcur c.σ.mem)
    (hsplo : 0x8001b900 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800079b0#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.mem = c.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hnw : vsp.toNat + 592 < 2 ^ 64 := by omega
  have hoff0 : (vsp + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat := by
    rw [sext0_add_rt vsp]
  -- pins L0: [x10, x2, x22]
  have hp0 : PinsHold c.σ [⟨Register.x10, va0⟩, ⟨Register.x2, vsp⟩, ⟨Register.x22, vcur⟩] :=
    ⟨hx10, hx2, hx22, trivial⟩
  -- === 7960: ld a5,0(sp)  (a5 := vcur) ===
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := slot_reload_bytes vsp 0x000 vcur c.σ.mem hslot0
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80007960_rt c.σ c.tick c.steps _ vmi0 vsp _ _ _ _ _ _ _ _
      hG hpc hmi0 hp0.2.1 hload rfl
      (by rw [hoff0]; omega) (by rw [hoff0]; omega) (Or.inr (by rw [hoff0]; omega))
      (by rw [hoff0]; omega) ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80007964#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80007960#64) 4 = (0x80007964#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx15_1 : σ1.regs.get? Register.x15 = some vcur := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vcur] at this
  -- L1: [x15, x10, x2, x22]
  have hp1 := pins_cons_rt hx15_1 (pins_alu hobs1 (by rfl) hp0)
  have hmE1 : σ1.mem = c.σ.mem := hmem1
  -- === 7964: mv s4,a0 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80007964_rt σ1 i1 (c.steps + 1) _ vmi1 va0
      hG1 hpc1 hmi1 hp1.2.1 (hmE1 ▸ hload) rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80007968#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80007964#64) 4 = (0x80007968#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  -- L2: [x15, x2, x22]  (a0 pin dropped — dead from here)
  have hp2 := pins_drop2_rt (pins_alu hobs2 (by rfl) hp1)
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1
  -- === 7968: subw s8,s6,a5  (s8 := vcur₃₂ - vcur₃₂ = 0) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80007968_rt σ2 i2 (c.steps + 1 + 1) _ vmi2 vcur vcur
      hG2 hpc2 hmi2 hp2.2.2.1 hp2.1 (hmE2 ▸ hload) rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000796c#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80007968#64) 4 = (0x8000796c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hx24_3 : σ3.regs.get? Register.x24 = some (0#64) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [subw_self_rt vcur] at this
  -- L3: [x24, x15, x2, x22]
  have hp3 := pins_cons_rt hx24_3 (pins_alu hobs3 (by rfl) hp2)
  have hmE3 : σ3.mem = c.σ.mem := hmem3.trans hmE2
  -- === 796c: beqz s8 → 0x800079b0 (TAKEN) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_8000796c_taken_rt σ3 i3 (c.steps + 1 + 1 + 1) _ vmi3 (0#64)
      hG3 hpc3 hmi3 hp3.1 (hmE3 ▸ hload) rfl (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x800079b0#64) := by
    have := obs_btaken_pc hobs4
    rwa [site_8000796c_taken_rt_tgt] at this
  obtain ⟨vmi4, hmi4⟩ := obs_btaken_minstret hobs4
  have hp4 := pins_btaken hobs4 (by rfl) hp3
  have hmE4 : σ4.mem = c.σ.mem := hmem4.trans hmE3
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, ?_, hG4, hpc4, hp4.2.2.1, hmE4, hi4,
    ⟨vmi4, hmi4⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    (Steps.single hstep4)))

end Vsa.Sim
