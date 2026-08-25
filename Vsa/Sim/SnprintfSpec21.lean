import Vsa.Sim.SnprintfSpec11
import Vsa.Sim.SlotFrame
import Vsa.Sim.RegPins
import Vsa.Sim.PtrArith
import Vsa.Sim.SnprintfSitesRet
import Vsa.Sim.SnprintfSitesRet2

/-!
# M3 Layer-3 — `SnprintfSpec21` : flush return, segment A
## `0x80008688` (post-`__ssprint_r` `beqz a0`) → `0x80007720` (parse-loop head)

The first segment of the `%lld` flush **return path** (pctrace "Flush part 3",
step after `ssprint_iov2_spec`): the `jal __ssprint_r` at `0x80008684` has
returned with `a0 = 0`, and svfprintf cleans up the gather state and jumps back
to the parse-loop head:

```
  80008688: beqz a0,80007918      a0 = 0 (ssprint_iov2_post) ⇒ TAKEN
  80007918: ld   a5,32(sp)        a5 := mem[sp+32]  (= 0: no malloc'd conv buffer)
  8000791c: sw   zero,232(sp)     iov count := 0
  80007920: beqz a5,80007930      TAKEN (no _free_r call — a5 = 0)
  80007930: mv   s7,s5            iov cursor := iov array base
  80007934: j    80007720         back to the parse-loop head
```

`retA_spec`: one `Steps` chain over the six sites, memory changed only by the
`sw` (`writeMap4` at `sp+232`), `x2/x3/x8/x9/x21` carried, `x23 := s5`.  The
`mem[sp+32] = 0` slot is a caller obligation (the conversion path never
allocates for `%lld`; the slot is `sd zero`-initialized in the prologue).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Re-add a freshly written register pin at the head of the list (local copy of
`SegState.pins_cons`, kept here to avoid the heavy import). -/
theorem pins_cons_rt {σ : MState} {R : Register} {v : RegisterType R} {L : List Pin}
    (h1 : σ.regs.get? R = some v) (h : PinsHold σ L) :
    PinsHold σ (⟨R, v⟩ :: L) := ⟨h1, h⟩

/-- `v + sext 0x000 = v` (local twin of `StrlenSpec.sext0_add`). -/
theorem sext0_add_rt (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
    apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]

/-- **Segment A of the flush return**: `0x80008688 → 0x80007720`.

Entry: the state `ssprint_iov2_post` leaves at the return point (`a0 = 0`,
`sp = vsp` restored, callee-saves restored).  Exit: parse-loop head, with the
iov count slot `mem32[sp+232]` cleared and `s7 := s5`. -/
theorem retA_spec (vsp vs5 v3 v8 v9 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80008688#64))
    (hx10 : c.σ.regs.get? Register.x10 = some (0#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some v3)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx9 : c.σ.regs.get? Register.x9 = some v9)
    (hx21 : c.σ.regs.get? Register.x21 = some vs5)
    (hslot32 : SlotHolds vsp 0x020 (0#64) c.σ.mem)
    (hsplo : 0x8001b900 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80007720#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x3 = some v3 ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x9 = some v9 ∧
      c'.σ.regs.get? Register.x21 = some vs5 ∧
      c'.σ.regs.get? Register.x23 = some vs5 ∧
      c'.σ.mem = writeMap4 c.σ.mem (vsp.toNat + 232) (swData (0#64)) ∧
      SvfprintfSliceLoaded c'.σ.mem ∧ FlushPinsLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hnw : vsp.toNat + 592 < 2 ^ 64 := by omega
  have hoff32 : (vsp + sign_extend (m := 64) (0x020#12)).toNat = vsp.toNat + 32 :=
    ptr_addoff vsp _ 32 (by decide) (by omega)
  have hoff232 : (vsp + sign_extend (m := 64) (0x0e8#12)).toNat = vsp.toNat + 232 :=
    ptr_addoff vsp _ 232 (by decide) (by omega)
  -- pin bundle: [x2, x3, x8, x9, x21]
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp⟩, ⟨Register.x3, v3⟩, ⟨Register.x8, v8⟩,
      ⟨Register.x9, v9⟩, ⟨Register.x21, vs5⟩] := ⟨hx2, hx3, hx8, hx9, hx21, trivial⟩
  -- === 8688: beqz a0 → 0x80007918 (TAKEN, a0 = 0) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80008688_taken_rt2 c.σ c.tick c.steps _ vmi0 (0#64)
      hG hpc hmi0 hx10 hfp rfl (by decide) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80007918#64) := by
    have := obs_btaken_pc hobs1
    rwa [site_80008688_taken_rt2_tgt] at this
  obtain ⟨vmi1, hmi1⟩ := obs_btaken_minstret hobs1
  have hp1 := pins_btaken hobs1 (by rfl) hp0
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
  have hfp1 : FlushPinsLoaded σ1.mem := hmem1 ▸ hfp
  -- === 7918: ld a5,32(sp)  (a5 := 0, the never-allocated conv buffer slot) ===
  have hs32 : SlotHolds vsp 0x020 (0#64) σ1.mem := by rw [hmem1]; exact hslot32
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := slot_reload_bytes vsp 0x020 (0#64) σ1.mem hs32
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80007918_rt σ1 i1 (c.steps + 1) _ vmi1 vsp _ _ _ _ _ _ _ _
      hG1 hpc1 hmi1 hp1.1 hload1 rfl
      (by rw [hoff32]; omega) (by rw [hoff32]; omega) (Or.inr (by rw [hoff32]; omega))
      (by rw [hoff32]; omega) h0 h1 h2 h3 h4 h5 h6 h7 hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x8000791c#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80007918#64) 4 = (0x8000791c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hx15_2 : σ2.regs.get? Register.x15 = some (0#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble (0#64)] at this
  -- pins: [x15, x2, x3, x8, x9, x21]
  have hp2 := pins_cons_rt hx15_2 (pins_alu hobs2 (by rfl) hp1)
  have hload2 : SvfprintfSliceLoaded σ2.mem := hmem2 ▸ hload1
  have hfp2 : FlushPinsLoaded σ2.mem := hmem2 ▸ hfp1
  -- === 791c: sw zero,232(sp)  (iov count := 0) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_8000791c_rt σ2 i2 (c.steps + 1 + 1) _ vmi2 vsp
      hG2 hpc2 hmi2 hp2.2.1 hload2 rfl
      (by rw [hoff232]; omega) (by rw [hoff232]; omega) (by rw [hoff232]; omega)
      (by rw [hoff232]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80007920#64) := by
    have := obs_store_pc hobs3
    rwa [show BitVec.addInt (0x8000791c#64) 4 = (0x80007920#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  have hp3 := pins_store hobs3 (by rfl) hp2
  have hm3 : σ3.mem = writeMap4 c.σ.mem (vsp.toNat + 232) (swData (0#64)) := by
    rw [hmem3, mem_afterNextPC, hmem2, hmem1, hoff232]
  have hload3 : SvfprintfSliceLoaded σ3.mem := by
    rw [hm3]; exact svfprintfSlice_writeMap4_pe _ _ _ (by omega) hload
  have hfp3 : FlushPinsLoaded σ3.mem := by
    rw [hm3]; exact flushPins_writeMap4_pe _ _ _ (by omega) hfp
  -- === 7920: beqz a5 → 0x80007930 (TAKEN, a5 = 0) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80007920_taken_rt σ3 i3 (c.steps + 1 + 1 + 1) _ vmi3 (0#64)
      hG3 hpc3 hmi3 hp3.1 hload3 rfl (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80007930#64) := by
    have := obs_btaken_pc hobs4
    rwa [site_80007920_taken_rt_tgt] at this
  obtain ⟨vmi4, hmi4⟩ := obs_btaken_minstret hobs4
  have hp4 := pins_btaken hobs4 (by rfl) hp3
  have hload4 : SvfprintfSliceLoaded σ4.mem := hmem4 ▸ hload3
  have hfp4 : FlushPinsLoaded σ4.mem := hmem4 ▸ hfp3
  -- === 7930: mv s7,s5  (iov cursor := iov base) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80007930_rt σ4 i4 (c.steps + 1 + 1 + 1 + 1) _ vmi4 vs5
      hG4 hpc4 hmi4 hp4.2.2.2.2.2.1 hload4 rfl hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩
      ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80007934#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80007930#64) 4 = (0x80007934#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx23_5 : σ5.regs.get? Register.x23 = some vs5 := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_rt vs5] at this
  -- pins: [x23, x15, x2, x3, x8, x9, x21]
  have hp5 := pins_cons_rt hx23_5 (pins_alu hobs5 (by rfl) hp4)
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  have hfp5 : FlushPinsLoaded σ5.mem := hmem5 ▸ hfp4
  -- === 7934: j 0x80007720 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80007934_rt σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) _ vmi5
      hG5 hpc5 hmi5 hload5 rfl
      (by rw [show (0x80007934#64 : BitVec 64) + sign_extend (m := 64) (0x1ffdec#21)
          = (0x80007720#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide]; decide)
      hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80007720#64) := by
    have := obs_jr_pc hobs6
    rwa [show (0x80007934#64 : BitVec 64) + sign_extend (m := 64) (0x1ffdec#21)
      = (0x80007720#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_jr_minstret hobs6
  have hp6 := pins_jr hobs6 (by rfl) hp5
  have hm6 : σ6.mem = writeMap4 c.σ.mem (vsp.toNat + 232) (swData (0#64)) := by
    rw [hmem6, hmem5, hmem4, hm3]
  have hload6 : SvfprintfSliceLoaded σ6.mem := hmem6 ▸ hload5
  have hfp6 : FlushPinsLoaded σ6.mem := hmem6 ▸ hfp5
  refine ⟨⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, hG6, hpc6,
    hp6.2.2.1, hp6.2.2.2.1, hp6.2.2.2.2.1, hp6.2.2.2.2.2.1, hp6.2.2.2.2.2.2.1, hp6.1,
    hm6, hload6, hfp6, hi6, ⟨vmi6, hmi6⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    ((Steps.single hstep4).trans ((Steps.single hstep5).trans (Steps.single hstep6)))))

end Vsa.Sim
