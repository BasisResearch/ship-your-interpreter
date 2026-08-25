import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro

/-!
# M3 Layer-3 — `SnprintfSpec30` : svfprintf prologue segment D
## `0x800076bc` (second spill block) → `0x800076f4`

The nine `s2…s11` callee-save spills to `sp+0x1e8…0x230` (Spec26's
`hsv1e8…hsv230` residuals) and the uio/iov init (`resid := 0` at `sp+240`,
`count := 0` at `sp+232`, iov base `sp+352` at `sp+224`, `s5 = s7 := sp+352`).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec30.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **Segment D of the svfprintf prologue**: `0x800076bc → 0x800076f4`.

The nine remaining callee-save spills (`s2…s11` to `sp+0x1e8…0x230`), the iov
machinery init: `addi s5,sp,352` (iov array base), `sd zero,240(sp)` (uio
resid), `sw zero,232(sp)` (iov count), `sd s5,224(sp)` (iov base slot),
`mv s7,s5`. -/
theorem svfProD_spec
    (vsp va0 vfile vfmt : BitVec 64)
    (vS2o vS3o vS4o vS5o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hms0 : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm0 : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800076bc#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some vfile)
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800076f4#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some vfile ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      SlotHolds vsp 0x230 vS2o c'.σ.mem ∧
      SlotHolds vsp 0x228 vS3o c'.σ.mem ∧
      SlotHolds vsp 0x220 vS4o c'.σ.mem ∧
      SlotHolds vsp 0x218 vS5o c'.σ.mem ∧
      SlotHolds vsp 0x208 vS7o c'.σ.mem ∧
      SlotHolds vsp 0x200 vS8o c'.σ.mem ∧
      SlotHolds vsp 0x1f8 vS9o c'.σ.mem ∧
      SlotHolds vsp 0x1f0 vS10o c'.σ.mem ∧
      SlotHolds vsp 0x1e8 vS11o c'.σ.mem ∧
      SlotHolds vsp 0x0f0 (0#64) c'.σ.mem ∧
      Pin4 c'.σ.mem (vsp.toNat + 232) (swData (0#64)) ∧
      SlotHolds vsp 0x0e0 (vsp + sign_extend (m := 64) (0x160#12)) c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 560 ≤ a ∧ a < vsp.toNat + 568) →
      ¬(vsp.toNat + 552 ≤ a ∧ a < vsp.toNat + 560) →
      ¬(vsp.toNat + 544 ≤ a ∧ a < vsp.toNat + 552) →
      ¬(vsp.toNat + 536 ≤ a ∧ a < vsp.toNat + 544) →
      ¬(vsp.toNat + 520 ≤ a ∧ a < vsp.toNat + 528) →
      ¬(vsp.toNat + 512 ≤ a ∧ a < vsp.toNat + 520) →
      ¬(vsp.toNat + 504 ≤ a ∧ a < vsp.toNat + 512) →
      ¬(vsp.toNat + 496 ≤ a ∧ a < vsp.toNat + 504) →
      ¬(vsp.toNat + 488 ≤ a ∧ a < vsp.toNat + 496) →
      ¬(vsp.toNat + 240 ≤ a ∧ a < vsp.toNat + 248) →
      ¬(vsp.toNat + 232 ≤ a ∧ a < vsp.toNat + 236) →
      ¬(vsp.toNat + 224 ≤ a ∧ a < vsp.toNat + 232) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.MemsetLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff560 : (vsp + sign_extend (m := 64) (0x230#12)).toNat = vsp.toNat + 560 := ptr_addoff vsp _ 560 (by decide) (by omega)
  have hoff552 : (vsp + sign_extend (m := 64) (0x228#12)).toNat = vsp.toNat + 552 := ptr_addoff vsp _ 552 (by decide) (by omega)
  have hoff544 : (vsp + sign_extend (m := 64) (0x220#12)).toNat = vsp.toNat + 544 := ptr_addoff vsp _ 544 (by decide) (by omega)
  have hoff536 : (vsp + sign_extend (m := 64) (0x218#12)).toNat = vsp.toNat + 536 := ptr_addoff vsp _ 536 (by decide) (by omega)
  have hoff520 : (vsp + sign_extend (m := 64) (0x208#12)).toNat = vsp.toNat + 520 := ptr_addoff vsp _ 520 (by decide) (by omega)
  have hoff512 : (vsp + sign_extend (m := 64) (0x200#12)).toNat = vsp.toNat + 512 := ptr_addoff vsp _ 512 (by decide) (by omega)
  have hoff504 : (vsp + sign_extend (m := 64) (0x1f8#12)).toNat = vsp.toNat + 504 := ptr_addoff vsp _ 504 (by decide) (by omega)
  have hoff496 : (vsp + sign_extend (m := 64) (0x1f0#12)).toNat = vsp.toNat + 496 := ptr_addoff vsp _ 496 (by decide) (by omega)
  have hoff488 : (vsp + sign_extend (m := 64) (0x1e8#12)).toNat = vsp.toNat + 488 := ptr_addoff vsp _ 488 (by decide) (by omega)
  have hoff240 : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat = vsp.toNat + 240 := ptr_addoff vsp _ 240 (by decide) (by omega)
  have hoff232 : (vsp + sign_extend (m := 64) (0x0e8#12)).toNat = vsp.toNat + 232 := ptr_addoff vsp _ 232 (by decide) (by omega)
  have hoff224 : (vsp + sign_extend (m := 64) (0x0e0#12)).toNat = vsp.toNat + 224 := ptr_addoff vsp _ 224 (by decide) (by omega)
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp⟩, ⟨Register.x3, (0x8001b510#64)⟩, ⟨Register.x8, va0⟩, ⟨Register.x9, vfile⟩, ⟨Register.x22, vfmt⟩, ⟨Register.x18, vS2o⟩, ⟨Register.x19, vS3o⟩, ⟨Register.x20, vS4o⟩, ⟨Register.x21, vS5o⟩, ⟨Register.x23, vS7o⟩, ⟨Register.x24, vS8o⟩, ⟨Register.x25, vS9o⟩, ⟨Register.x26, vS10o⟩, ⟨Register.x27, vS11o⟩] :=
    ⟨hx2, hx3, hx8, hx9, hx22, hx18, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, trivial⟩
  -- === 0x800076bc: sd -> sp+560 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800076bc_pr c.σ c.tick c.steps _ vmi0 vsp _
      hG hpc hmi0 hp0.1 hp0.2.2.2.2.2.1 hsl0 rfl (by rw [hoff560]; omega) (by rw [hoff560]; omega) (by rw [hoff560, htoh]; omega) (by rw [hoff560]; omega) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x800076c0#64) := by
    have := obs_store_pc hobs1
    rwa [show BitVec.addInt (0x800076bc#64) 4 = (0x800076c0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_store_minstret hobs1
  have hp1 := pins_store hobs1 (by rfl) hp0
  have hmE1 : σ1.mem = writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o) := by
    rw [hmem1, mem_afterNextPC, hoff560]
  have hsl1 : Vsa.Sim.Code.SvfprintfSliceLoaded σ1.mem := by
    rw [hmem1, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff560]; omega) hsl0

  -- === 0x800076c0: sd -> sp+552 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800076c0_pr σ1 i1 (c.steps + 1) _ vmi1 vsp _
      hG1 hpc1 hmi1 hp1.1 hp1.2.2.2.2.2.2.1 hsl1 rfl (by rw [hoff552]; omega) (by rw [hoff552]; omega) (by rw [hoff552, htoh]; omega) (by rw [hoff552]; omega) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 2⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x800076c4#64) := by
    have := obs_store_pc hobs2
    rwa [show BitVec.addInt (0x800076c0#64) 4 = (0x800076c4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret hobs2
  have hp2 := pins_store hobs2 (by rfl) hp1
  have hmE2 : σ2.mem = writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o) := by
    rw [hmem2, mem_afterNextPC, hmE1, hoff552]
  have hsl2 : Vsa.Sim.Code.SvfprintfSliceLoaded σ2.mem := by
    rw [hmem2, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff552]; omega) hsl1

  -- === 0x800076c4: sd -> sp+544 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_800076c4_pr σ2 i2 (c.steps + 2) _ vmi2 vsp _
      hG2 hpc2 hmi2 hp2.1 hp2.2.2.2.2.2.2.2.1 hsl2 rfl (by rw [hoff544]; omega) (by rw [hoff544]; omega) (by rw [hoff544, htoh]; omega) (by rw [hoff544]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 2⟩ ⟨σ3, i3, c.steps + 3⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x800076c8#64) := by
    have := obs_store_pc hobs3
    rwa [show BitVec.addInt (0x800076c4#64) 4 = (0x800076c8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  have hp3 := pins_store hobs3 (by rfl) hp2
  have hmE3 : σ3.mem = writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o) := by
    rw [hmem3, mem_afterNextPC, hmE2, hoff544]
  have hsl3 : Vsa.Sim.Code.SvfprintfSliceLoaded σ3.mem := by
    rw [hmem3, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff544]; omega) hsl2

  -- === 0x800076c8: sd -> sp+536 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_800076c8_pr σ3 i3 (c.steps + 3) _ vmi3 vsp _
      hG3 hpc3 hmi3 hp3.1 hp3.2.2.2.2.2.2.2.2.1 hsl3 rfl (by rw [hoff536]; omega) (by rw [hoff536]; omega) (by rw [hoff536, htoh]; omega) (by rw [hoff536]; omega) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 3⟩ ⟨σ4, i4, c.steps + 4⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x800076cc#64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x800076c8#64) 4 = (0x800076cc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have hp4 := pins_store hobs4 (by rfl) hp3
  have hmE4 : σ4.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o) := by
    rw [hmem4, mem_afterNextPC, hmE3, hoff536]
  have hsl4 : Vsa.Sim.Code.SvfprintfSliceLoaded σ4.mem := by
    rw [hmem4, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff536]; omega) hsl3

  -- === 0x800076cc: sd -> sp+520 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_800076cc_pr σ4 i4 (c.steps + 4) _ vmi4 vsp _
      hG4 hpc4 hmi4 hp4.1 hp4.2.2.2.2.2.2.2.2.2.1 hsl4 rfl (by rw [hoff520]; omega) (by rw [hoff520]; omega) (by rw [hoff520, htoh]; omega) (by rw [hoff520]; omega) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 4⟩ ⟨σ5, i5, c.steps + 5⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x800076d0#64) := by
    have := obs_store_pc hobs5
    rwa [show BitVec.addInt (0x800076cc#64) 4 = (0x800076d0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret hobs5
  have hp5 := pins_store hobs5 (by rfl) hp4
  have hmE5 : σ5.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o)) (vsp.toNat + 520) (sdData_val vS7o) := by
    rw [hmem5, mem_afterNextPC, hmE4, hoff520]
  have hsl5 : Vsa.Sim.Code.SvfprintfSliceLoaded σ5.mem := by
    rw [hmem5, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff520]; omega) hsl4

  -- === 0x800076d0: sd -> sp+512 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_800076d0_pr σ5 i5 (c.steps + 5) _ vmi5 vsp _
      hG5 hpc5 hmi5 hp5.1 hp5.2.2.2.2.2.2.2.2.2.2.1 hsl5 rfl (by rw [hoff512]; omega) (by rw [hoff512]; omega) (by rw [hoff512, htoh]; omega) (by rw [hoff512]; omega) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 5⟩ ⟨σ6, i6, c.steps + 6⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x800076d4#64) := by
    have := obs_store_pc hobs6
    rwa [show BitVec.addInt (0x800076d0#64) 4 = (0x800076d4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret hobs6
  have hp6 := pins_store hobs6 (by rfl) hp5
  have hmE6 : σ6.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o)) (vsp.toNat + 520) (sdData_val vS7o)) (vsp.toNat + 512) (sdData_val vS8o) := by
    rw [hmem6, mem_afterNextPC, hmE5, hoff512]
  have hsl6 : Vsa.Sim.Code.SvfprintfSliceLoaded σ6.mem := by
    rw [hmem6, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff512]; omega) hsl5

  -- === 0x800076d4: sd -> sp+504 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_800076d4_pr σ6 i6 (c.steps + 6) _ vmi6 vsp _
      hG6 hpc6 hmi6 hp6.1 hp6.2.2.2.2.2.2.2.2.2.2.2.1 hsl6 rfl (by rw [hoff504]; omega) (by rw [hoff504]; omega) (by rw [hoff504, htoh]; omega) (by rw [hoff504]; omega) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 7⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x800076d8#64) := by
    have := obs_store_pc hobs7
    rwa [show BitVec.addInt (0x800076d4#64) 4 = (0x800076d8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret hobs7
  have hp7 := pins_store hobs7 (by rfl) hp6
  have hmE7 : σ7.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o)) (vsp.toNat + 520) (sdData_val vS7o)) (vsp.toNat + 512) (sdData_val vS8o)) (vsp.toNat + 504) (sdData_val vS9o) := by
    rw [hmem7, mem_afterNextPC, hmE6, hoff504]
  have hsl7 : Vsa.Sim.Code.SvfprintfSliceLoaded σ7.mem := by
    rw [hmem7, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff504]; omega) hsl6

  -- === 0x800076d8: sd -> sp+496 ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_800076d8_pr σ7 i7 (c.steps + 7) _ vmi7 vsp _
      hG7 hpc7 hmi7 hp7.1 hp7.2.2.2.2.2.2.2.2.2.2.2.2.1 hsl7 rfl (by rw [hoff496]; omega) (by rw [hoff496]; omega) (by rw [hoff496, htoh]; omega) (by rw [hoff496]; omega) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 7⟩ ⟨σ8, i8, c.steps + 8⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x800076dc#64) := by
    have := obs_store_pc hobs8
    rwa [show BitVec.addInt (0x800076d8#64) 4 = (0x800076dc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret hobs8
  have hp8 := pins_store hobs8 (by rfl) hp7
  have hmE8 : σ8.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o)) (vsp.toNat + 520) (sdData_val vS7o)) (vsp.toNat + 512) (sdData_val vS8o)) (vsp.toNat + 504) (sdData_val vS9o)) (vsp.toNat + 496) (sdData_val vS10o) := by
    rw [hmem8, mem_afterNextPC, hmE7, hoff496]
  have hsl8 : Vsa.Sim.Code.SvfprintfSliceLoaded σ8.mem := by
    rw [hmem8, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff496]; omega) hsl7

  -- === 0x800076dc: sd -> sp+488 ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_800076dc_pr σ8 i8 (c.steps + 8) _ vmi8 vsp _
      hG8 hpc8 hmi8 hp8.1 hp8.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hsl8 rfl (by rw [hoff488]; omega) (by rw [hoff488]; omega) (by rw [hoff488, htoh]; omega) (by rw [hoff488]; omega) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 8⟩ ⟨σ9, i9, c.steps + 9⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x800076e0#64) := by
    have := obs_store_pc hobs9
    rwa [show BitVec.addInt (0x800076dc#64) 4 = (0x800076e0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret hobs9
  have hp9 := pins_store hobs9 (by rfl) hp8
  have hmE9 : σ9.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o)) (vsp.toNat + 520) (sdData_val vS7o)) (vsp.toNat + 512) (sdData_val vS8o)) (vsp.toNat + 504) (sdData_val vS9o)) (vsp.toNat + 496) (sdData_val vS10o)) (vsp.toNat + 488) (sdData_val vS11o) := by
    rw [hmem9, mem_afterNextPC, hmE8, hoff488]
  have hsl9 : Vsa.Sim.Code.SvfprintfSliceLoaded σ9.mem := by
    rw [hmem9, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff488]; omega) hsl8

  -- === 0x800076e0: addi s5,sp,352 — the iov array base ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_800076e0_pr σ9 i9 (c.steps + 9) _ vmi9 vsp
      hG9 hpc9 hmi9 hp9.1 hsl9 rfl hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 9⟩ ⟨σ10, i10, c.steps + 10⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x800076e4#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x800076e0#64) 4 = (0x800076e4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hrd10 : σ10.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) :=
    obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp10 := pins_cons_pro hrd10 (pins_alu hobs10 (by rfl) (pins_drop9_pro hp9))
  have hmE10 : σ10.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o)) (vsp.toNat + 520) (sdData_val vS7o)) (vsp.toNat + 512) (sdData_val vS8o)) (vsp.toNat + 504) (sdData_val vS9o)) (vsp.toNat + 496) (sdData_val vS10o)) (vsp.toNat + 488) (sdData_val vS11o) := hmem10.trans hmE9
  have hsl10 : Vsa.Sim.Code.SvfprintfSliceLoaded σ10.mem := by rw [hmem10]; exact hsl9

  -- === 0x800076e4: sd zero,240(sp) — uio resid init ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_800076e4_pr σ10 i10 (c.steps + 10) _ vmi10 vsp
      hG10 hpc10 hmi10 hp10.2.1 hsl10 rfl (by rw [hoff240]; omega) (by rw [hoff240]; omega) (by rw [hoff240, htoh]; omega) (by rw [hoff240]; omega) hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 10⟩ ⟨σ11, i11, c.steps + 11⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x800076e8#64) := by
    have := obs_store_pc hobs11
    rwa [show BitVec.addInt (0x800076e4#64) 4 = (0x800076e8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_store_minstret hobs11
  have hp11 := pins_store hobs11 (by rfl) hp10
  have hmE11 : σ11.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o)) (vsp.toNat + 520) (sdData_val vS7o)) (vsp.toNat + 512) (sdData_val vS8o)) (vsp.toNat + 504) (sdData_val vS9o)) (vsp.toNat + 496) (sdData_val vS10o)) (vsp.toNat + 488) (sdData_val vS11o)) (vsp.toNat + 240) (sdData_val (0#64)) := by
    rw [hmem11, mem_afterNextPC, hmE10, hoff240]
  have hsl11 : Vsa.Sim.Code.SvfprintfSliceLoaded σ11.mem := by
    rw [hmem11, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff240]; omega) hsl10

  -- === 0x800076e8: sw zero,232(sp) — iov count init ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_800076e8_pr σ11 i11 (c.steps + 11) _ vmi11 vsp
      hG11 hpc11 hmi11 hp11.2.1 hsl11 rfl (by rw [hoff232]; omega) (by rw [hoff232]; omega) (by rw [hoff232, htoh]; omega) (by rw [hoff232]; omega) hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 11⟩ ⟨σ12, i12, c.steps + 12⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x800076ec#64) := by
    have := obs_store_pc hobs12
    rwa [show BitVec.addInt (0x800076e8#64) 4 = (0x800076ec#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_store_minstret hobs12
  have hp12 := pins_store hobs12 (by rfl) hp11
  have hmE12 : σ12.mem = writeMap4 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o)) (vsp.toNat + 520) (sdData_val vS7o)) (vsp.toNat + 512) (sdData_val vS8o)) (vsp.toNat + 504) (sdData_val vS9o)) (vsp.toNat + 496) (sdData_val vS10o)) (vsp.toNat + 488) (sdData_val vS11o)) (vsp.toNat + 240) (sdData_val (0#64))) (vsp.toNat + 232) (swData (0#64)) := by
    rw [hmem12, mem_afterNextPC, hmE11, hoff232]
  have hsl12 : Vsa.Sim.Code.SvfprintfSliceLoaded σ12.mem := by
    rw [hmem12, mem_afterNextPC]
    exact svf_w4_pro _ _ _ (by rw [hoff232]; omega) hsl11

  -- === 0x800076ec: sd s5,224(sp) — iov base slot ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_800076ec_pr σ12 i12 (c.steps + 12) _ vmi12 vsp _
      hG12 hpc12 hmi12 hp12.2.1 hp12.1 hsl12 rfl (by rw [hoff224]; omega) (by rw [hoff224]; omega) (by rw [hoff224, htoh]; omega) (by rw [hoff224]; omega) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 12⟩ ⟨σ13, i13, c.steps + 13⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x800076f0#64) := by
    have := obs_store_pc hobs13
    rwa [show BitVec.addInt (0x800076ec#64) 4 = (0x800076f0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_store_minstret hobs13
  have hp13 := pins_store hobs13 (by rfl) hp12
  have hmE13 : σ13.mem = writeMap8 (writeMap4 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o)) (vsp.toNat + 520) (sdData_val vS7o)) (vsp.toNat + 512) (sdData_val vS8o)) (vsp.toNat + 504) (sdData_val vS9o)) (vsp.toNat + 496) (sdData_val vS10o)) (vsp.toNat + 488) (sdData_val vS11o)) (vsp.toNat + 240) (sdData_val (0#64))) (vsp.toNat + 232) (swData (0#64))) (vsp.toNat + 224) (sdData_val (vsp + sign_extend (m := 64) (0x160#12))) := by
    rw [hmem13, mem_afterNextPC, hmE12, hoff224]
  have hsl13 : Vsa.Sim.Code.SvfprintfSliceLoaded σ13.mem := by
    rw [hmem13, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff224]; omega) hsl12

  -- === 0x800076f0: mv s7,s5 ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_800076f0_pr σ13 i13 (c.steps + 13) _ vmi13 (vsp + sign_extend (m := 64) (0x160#12))
      hG13 hpc13 hmi13 hp13.1 hsl13 rfl hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 13⟩ ⟨σ14, i14, c.steps + 14⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x800076f4#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x800076f0#64) 4 = (0x800076f4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hrd14 : σ14.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro (vsp + sign_extend (m := 64) (0x160#12))] at this
  have hp14 := pins_cons_pro hrd14 (pins_alu hobs14 (by rfl) (pins_drop10_pro hp13))
  have hmE14 : σ14.mem = writeMap8 (writeMap4 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 560) (sdData_val vS2o)) (vsp.toNat + 552) (sdData_val vS3o)) (vsp.toNat + 544) (sdData_val vS4o)) (vsp.toNat + 536) (sdData_val vS5o)) (vsp.toNat + 520) (sdData_val vS7o)) (vsp.toNat + 512) (sdData_val vS8o)) (vsp.toNat + 504) (sdData_val vS9o)) (vsp.toNat + 496) (sdData_val vS10o)) (vsp.toNat + 488) (sdData_val vS11o)) (vsp.toNat + 240) (sdData_val (0#64))) (vsp.toNat + 232) (swData (0#64))) (vsp.toNat + 224) (sdData_val (vsp + sign_extend (m := 64) (0x160#12))) := hmem14.trans hmE13
  have hsl14 : Vsa.Sim.Code.SvfprintfSliceLoaded σ14.mem := by rw [hmem14]; exact hsl13

  have hmsN : Vsa.Sim.Code.MemsetLoaded σ14.mem := by
    rw [hmE14]
    exact memset_w8_pro _ _ _ (by omega) (memset_w4_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega) hms0)))))))))))
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ14.mem := by
    rw [hmE14]
    exact localemb_w8_pro _ _ _ (by omega) (localemb_w4_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega) hlm0)))))))))))
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ14.mem := by
    rw [hmE14]
    exact amb_w8_pro _ _ _ (by omega) (amb_w4_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega) hamb0)))))))))))
  have hS230 : SlotHolds vsp 0x230 vS2o σ14.mem := by
    rw [hmE14]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff560]; omega) ?_
    exact slot_save vsp 0x230 vS2o _ _ _ hoff560 rfl
  have hS228 : SlotHolds vsp 0x228 vS3o σ14.mem := by
    rw [hmE14]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff552]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff552]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff552]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff552]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff552]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff552]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff552]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff552]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff552]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff552]; omega) ?_
    exact slot_save vsp 0x228 vS3o _ _ _ hoff552 rfl
  have hS220 : SlotHolds vsp 0x220 vS4o σ14.mem := by
    rw [hmE14]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff544]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff544]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff544]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff544]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff544]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff544]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff544]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff544]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff544]; omega) ?_
    exact slot_save vsp 0x220 vS4o _ _ _ hoff544 rfl
  have hS218 : SlotHolds vsp 0x218 vS5o σ14.mem := by
    rw [hmE14]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff536]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff536]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff536]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff536]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff536]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff536]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff536]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff536]; omega) ?_
    exact slot_save vsp 0x218 vS5o _ _ _ hoff536 rfl
  have hS208 : SlotHolds vsp 0x208 vS7o σ14.mem := by
    rw [hmE14]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff520]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff520]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff520]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff520]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff520]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff520]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff520]; omega) ?_
    exact slot_save vsp 0x208 vS7o _ _ _ hoff520 rfl
  have hS200 : SlotHolds vsp 0x200 vS8o σ14.mem := by
    rw [hmE14]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff512]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff512]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff512]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff512]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff512]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff512]; omega) ?_
    exact slot_save vsp 0x200 vS8o _ _ _ hoff512 rfl
  have hS1f8 : SlotHolds vsp 0x1f8 vS9o σ14.mem := by
    rw [hmE14]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff504]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff504]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff504]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff504]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff504]; omega) ?_
    exact slot_save vsp 0x1f8 vS9o _ _ _ hoff504 rfl
  have hS1f0 : SlotHolds vsp 0x1f0 vS10o σ14.mem := by
    rw [hmE14]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff496]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff496]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff496]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff496]; omega) ?_
    exact slot_save vsp 0x1f0 vS10o _ _ _ hoff496 rfl
  have hS1e8 : SlotHolds vsp 0x1e8 vS11o σ14.mem := by
    rw [hmE14]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff488]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff488]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff488]; omega) ?_
    exact slot_save vsp 0x1e8 vS11o _ _ _ hoff488 rfl
  have hS0f0 : SlotHolds vsp 0x0f0 (0#64) σ14.mem := by
    rw [hmE14]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff240]; omega) ?_
    refine slot_survives_writeMap4 _ _ _ _ _ _ (by rw [hoff240]; omega) ?_
    exact slot_save vsp 0x0f0 (0#64) _ _ _ hoff240 rfl
  have hS0e0 : SlotHolds vsp 0x0e0 (vsp + sign_extend (m := 64) (0x160#12)) σ14.mem := by
    rw [hmE14]
    exact slot_save vsp 0x0e0 (vsp + sign_extend (m := 64) (0x160#12)) _ _ _ hoff224 rfl
  have hP232 : Pin4 σ14.mem (vsp.toNat + 232) (swData (0#64)) := by
    rw [hmE14]
    refine Pin4_frame (fun k hk1 hk2 =>
      getElem?_writeMap8_out _ (vsp.toNat + 224) _ k (by omega)) ?_
    exact Pin4_writeMap4 _ _ _
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 560 ≤ a ∧ a < vsp.toNat + 568) →
      ¬(vsp.toNat + 552 ≤ a ∧ a < vsp.toNat + 560) →
      ¬(vsp.toNat + 544 ≤ a ∧ a < vsp.toNat + 552) →
      ¬(vsp.toNat + 536 ≤ a ∧ a < vsp.toNat + 544) →
      ¬(vsp.toNat + 520 ≤ a ∧ a < vsp.toNat + 528) →
      ¬(vsp.toNat + 512 ≤ a ∧ a < vsp.toNat + 520) →
      ¬(vsp.toNat + 504 ≤ a ∧ a < vsp.toNat + 512) →
      ¬(vsp.toNat + 496 ≤ a ∧ a < vsp.toNat + 504) →
      ¬(vsp.toNat + 488 ≤ a ∧ a < vsp.toNat + 496) →
      ¬(vsp.toNat + 240 ≤ a ∧ a < vsp.toNat + 248) →
      ¬(vsp.toNat + 232 ≤ a ∧ a < vsp.toNat + 236) →
      ¬(vsp.toNat + 224 ≤ a ∧ a < vsp.toNat + 232) →
      σ14.mem[a]? = c.σ.mem[a]? := by
    intro a hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11
    rw [hmE14,
      getElem?_writeMap8_out _ (vsp.toNat + 224) _ a (by omega),
      getElem?_writeMap4_out_pro _ (vsp.toNat + 232) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 240) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 488) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 496) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 504) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 512) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 520) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 536) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 544) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 552) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 560) _ a (by omega)]
  refine ⟨⟨σ14, i14, c.steps + 14⟩, ?_,
    hG14,
    hpc14,
    hp14.2.2.1,
    hp14.2.2.2.1,
    hp14.2.2.2.2.1,
    hp14.2.2.2.2.2.1,
    hp14.2.2.2.2.2.2.1,
    hp14.2.2.2.2.2.2.2.1,
    hp14.2.2.2.2.2.2.2.2.1,
    hp14.2.2.2.2.2.2.2.2.2.1,
    hp14.2.1,
    hp14.1,
    hp14.2.2.2.2.2.2.2.2.2.2.1,
    hp14.2.2.2.2.2.2.2.2.2.2.2.1,
    hp14.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp14.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hS230,
    hS228,
    hS220,
    hS218,
    hS208,
    hS200,
    hS1f8,
    hS1f0,
    hS1e8,
    hS0f0,
    hP232,
    hS0e0,
    hagN,
    hsl14,
    hmsN,
    hlmN,
    hambN,
    hi14,
    ⟨vmi14, hmi14⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans (Steps.single hstep14)))))))))))))

end Vsa.Sim
