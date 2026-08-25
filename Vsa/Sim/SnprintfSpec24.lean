import Vsa.Sim.SnprintfSpec23

/-!
# M3 Layer-3 — `SnprintfSpec24` : flush return, segment D
## `0x800079b0` (epilogue head) → `ret` (svfprintf returns `a0 = total`)

The svfprintf epilogue on the `%lld` path:

```
  800079b0: ld   a5,240(sp)        gather cursor (= 0 — __ssprint_r cleared it)
  800079b4: beqz a5,800079bc       TAKEN (no final flush at 0x80009e40)
  800079bc: ld   a5,8(sp)          a5 := the fake FILE (string sink) ptr
  800079c0: lhu  a5,16(a5)         a5 := FILE->_flags
  800079c4: andi a5,a5,64          __SMBF test — 0 (no malloc'd buffer)
  800079c8–800079e8: ld s2/s3/s4/s5/s7/s8/s9/s10/s11 from the spill slots
  800079ec: beqz a5,800079f4       TAKEN (no 0x8000a75c cleanup)
  800079f4: ld   ra,584(sp)
  800079f8: ld   s0,576(sp)
  800079fc: ld   a0,16(sp)         a0 := THE TOTAL (accumulated ret at sp+16)
  80007a00: ld   s1,568(sp)        ── the 4 FlushPins tail instructions ──
  80007a04: ld   s6,528(sp)
  80007a08: addi sp,sp,592
  80007a0c: ret                    PC := saved ra, a0 = total
```

`retD_spec`: 22 sites, no memory writes; every reload fed from a `SlotHolds`
carried by the caller (the prologue's spills, transported across the whole
body by the sub-call frames). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded FlushPinsLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Drop the 16th pin of a ≥16 list (the epilogue's `sp` rewrite). -/
theorem pins_drop16_rt {σ : MState} {a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 : Pin}
    {L : List Pin}
    (h : PinsHold σ (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 ::
      a13 :: a14 :: a15 :: a16 :: L)) :
    PinsHold σ (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: a10 :: a11 :: a12 ::
      a13 :: a14 :: a15 :: L) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

/-- **Segment D of the flush return**: the svfprintf epilogue
`0x800079b0 → ret`, with `a0 = vtot` (the total) at `PC = vra0`. -/
theorem retD_spec (vsp vstr vra0 vtot vS0o vS1o vS2 vS3 vS4 vS5 vS6o vS7 vS8 vS9 vS10
      vS11 : BitVec 64) (fl0 fl1 : BitVec 8) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800079b0#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (h0f0 : SlotHolds vsp 0x0f0 (0#64) c.σ.mem)
    (h008 : SlotHolds vsp 0x008 vstr c.σ.mem)
    (h230 : SlotHolds vsp 0x230 vS2 c.σ.mem)
    (h228 : SlotHolds vsp 0x228 vS3 c.σ.mem)
    (h220 : SlotHolds vsp 0x220 vS4 c.σ.mem)
    (h218 : SlotHolds vsp 0x218 vS5 c.σ.mem)
    (h208 : SlotHolds vsp 0x208 vS7 c.σ.mem)
    (h200 : SlotHolds vsp 0x200 vS8 c.σ.mem)
    (h1f8 : SlotHolds vsp 0x1f8 vS9 c.σ.mem)
    (h1f0 : SlotHolds vsp 0x1f0 vS10 c.σ.mem)
    (h1e8 : SlotHolds vsp 0x1e8 vS11 c.σ.mem)
    (h248 : SlotHolds vsp 0x248 vra0 c.σ.mem)
    (h240 : SlotHolds vsp 0x240 vS0o c.σ.mem)
    (h010 : SlotHolds vsp 0x010 vtot c.σ.mem)
    (h238 : SlotHolds vsp 0x238 vS1o c.σ.mem)
    (h210 : SlotHolds vsp 0x210 vS6o c.σ.mem)
    (hfl0 : c.σ.mem[vstr.toNat + 16]? = some fl0)
    (hfl1 : c.σ.mem[vstr.toNat + 17]? = some fl1)
    (hflag : ((zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
      &&& sign_extend (m := 64) (0x040#12)) = 0#64)
    (hstrlo : 0x80000000 ≤ vstr.toNat)
    (hstrhi : vstr.toNat + 18 ≤ 0x100000000)
    (hstrhtif : vstr.toNat + 18 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vstr.toNat)
    (hstral : vstr.toNat % 2 = 0)
    (hra0align : vra0.toNat % 4 = 0)
    (hsplo : 0x8001b900 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some vra0 ∧
      c'.σ.regs.get? Register.x1 = some vra0 ∧
      c'.σ.regs.get? Register.x2 = some (vsp + (592#64)) ∧
      c'.σ.regs.get? Register.x10 = some vtot ∧
      c'.σ.regs.get? Register.x8 = some vS0o ∧
      c'.σ.regs.get? Register.x9 = some vS1o ∧
      c'.σ.regs.get? Register.x18 = some vS2 ∧
      c'.σ.regs.get? Register.x19 = some vS3 ∧
      c'.σ.regs.get? Register.x20 = some vS4 ∧
      c'.σ.regs.get? Register.x21 = some vS5 ∧
      c'.σ.regs.get? Register.x22 = some vS6o ∧
      c'.σ.regs.get? Register.x23 = some vS7 ∧
      c'.σ.regs.get? Register.x24 = some vS8 ∧
      c'.σ.regs.get? Register.x25 = some vS9 ∧
      c'.σ.regs.get? Register.x26 = some vS10 ∧
      c'.σ.regs.get? Register.x27 = some vS11 ∧
      c'.σ.mem = c.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hnw : vsp.toNat + 592 < 2 ^ 64 := by omega
  have hstrnw : vstr.toNat + 18 < 2 ^ 64 := by omega
  have hoff240 : (vsp + sign_extend (m := 64) (0x0f0#12)).toNat = vsp.toNat + 240 :=
    ptr_addoff vsp _ 240 (by decide) (by omega)
  have hoff8 : (vsp + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat + 8 :=
    ptr_addoff vsp _ 8 (by decide) (by omega)
  have hoffstr : (vstr + sign_extend (m := 64) (0x010#12)).toNat = vstr.toNat + 16 :=
    ptr_addoff vstr _ 16 (by decide) (by omega)
  have hoff560 : (vsp + sign_extend (m := 64) (0x230#12)).toNat = vsp.toNat + 560 :=
    ptr_addoff vsp _ 560 (by decide) (by omega)
  have hoff552 : (vsp + sign_extend (m := 64) (0x228#12)).toNat = vsp.toNat + 552 :=
    ptr_addoff vsp _ 552 (by decide) (by omega)
  have hoff544 : (vsp + sign_extend (m := 64) (0x220#12)).toNat = vsp.toNat + 544 :=
    ptr_addoff vsp _ 544 (by decide) (by omega)
  have hoff536 : (vsp + sign_extend (m := 64) (0x218#12)).toNat = vsp.toNat + 536 :=
    ptr_addoff vsp _ 536 (by decide) (by omega)
  have hoff520 : (vsp + sign_extend (m := 64) (0x208#12)).toNat = vsp.toNat + 520 :=
    ptr_addoff vsp _ 520 (by decide) (by omega)
  have hoff512 : (vsp + sign_extend (m := 64) (0x200#12)).toNat = vsp.toNat + 512 :=
    ptr_addoff vsp _ 512 (by decide) (by omega)
  have hoff504 : (vsp + sign_extend (m := 64) (0x1f8#12)).toNat = vsp.toNat + 504 :=
    ptr_addoff vsp _ 504 (by decide) (by omega)
  have hoff496 : (vsp + sign_extend (m := 64) (0x1f0#12)).toNat = vsp.toNat + 496 :=
    ptr_addoff vsp _ 496 (by decide) (by omega)
  have hoff488 : (vsp + sign_extend (m := 64) (0x1e8#12)).toNat = vsp.toNat + 488 :=
    ptr_addoff vsp _ 488 (by decide) (by omega)
  have hoff584 : (vsp + sign_extend (m := 64) (0x248#12)).toNat = vsp.toNat + 584 :=
    ptr_addoff vsp _ 584 (by decide) (by omega)
  have hoff576 : (vsp + sign_extend (m := 64) (0x240#12)).toNat = vsp.toNat + 576 :=
    ptr_addoff vsp _ 576 (by decide) (by omega)
  have hoff16 : (vsp + sign_extend (m := 64) (0x010#12)).toNat = vsp.toNat + 16 :=
    ptr_addoff vsp _ 16 (by decide) (by omega)
  have hoff568 : (vsp + sign_extend (m := 64) (0x238#12)).toNat = vsp.toNat + 568 :=
    ptr_addoff vsp _ 568 (by decide) (by omega)
  have hoff528 : (vsp + sign_extend (m := 64) (0x210#12)).toNat = vsp.toNat + 528 :=
    ptr_addoff vsp _ 528 (by decide) (by omega)
  -- pins L0: [x2]
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp⟩] := ⟨hx2, trivial⟩
  -- === 79b0: ld a5,240(sp)  (a5 := 0, cleared by __ssprint_r) ===
  obtain ⟨ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ :=
    slot_reload_bytes vsp 0x0f0 (0#64) c.σ.mem h0f0
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800079b0_rt c.σ c.tick c.steps _ vmi0 vsp _ _ _ _ _ _ _ _
      hG hpc hmi0 hp0.1 hload rfl
      (by rw [hoff240]; omega) (by rw [hoff240]; omega) (Or.inr (by rw [hoff240]; omega))
      (by rw [hoff240]; omega) ha0 ha1 ha2 ha3 ha4 ha5 ha6 ha7 htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x800079b4#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800079b0#64) 4 = (0x800079b4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx15_1 : σ1.regs.get? Register.x15 = some (0#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble (0#64)] at this
  have hp1 := pins_cons_rt hx15_1 (pins_alu hobs1 (by rfl) hp0)  -- [x15, x2]
  have hmE1 : σ1.mem = c.σ.mem := hmem1
  -- === 79b4: beqz a5 → 0x800079bc (TAKEN — no final flush) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800079b4_taken_rt σ1 i1 (c.steps + 1) _ vmi1 (0#64)
      hG1 hpc1 hmi1 hp1.1 (hmE1 ▸ hload) rfl (by decide) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x800079bc#64) := by
    have := obs_btaken_pc hobs2
    rwa [site_800079b4_taken_rt_tgt] at this
  obtain ⟨vmi2, hmi2⟩ := obs_btaken_minstret hobs2
  have hp2 := pins_btaken hobs2 (by rfl) hp1
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1
  -- === 79bc: ld a5,8(sp)  (a5 := the FILE ptr) ===
  have hs8m : SlotHolds vsp 0x008 vstr σ2.mem := by rw [hmE2]; exact h008
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := slot_reload_bytes vsp 0x008 vstr σ2.mem hs8m
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_800079bc_rt σ2 i2 (c.steps + 1 + 1) _ vmi2 vsp _ _ _ _ _ _ _ _
      hG2 hpc2 hmi2 hp2.2.1 (hmE2 ▸ hload) rfl
      (by rw [hoff8]; omega) (by rw [hoff8]; omega) (Or.inr (by rw [hoff8]; omega))
      (by rw [hoff8]; omega) hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x800079c0#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800079bc#64) 4 = (0x800079c0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hx15_3 : σ3.regs.get? Register.x15 = some vstr := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vstr] at this
  have hp3 := pins_cons_rt hx15_3 (pins_alu hobs3 (by rfl) hp2.2)  -- [x15, x2]
  have hmE3 : σ3.mem = c.σ.mem := hmem3.trans hmE2
  -- === 79c0: lhu a5,16(a5)  (a5 := FILE->_flags) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_800079c0_rt5 σ3 i3 (c.steps + 1 + 1 + 1) _ vmi3 vstr fl0 fl1
      hG3 hpc3 hmi3 hp3.1 (hmE3 ▸ hload) rfl
      (by rw [hoffstr]; omega) (by rw [hoffstr]; omega) (by rw [hoffstr]; omega)
      (by rw [hoffstr]; omega)
      (by rw [hoffstr, hmE3]; exact hfl0) (by rw [hoffstr, hmE3]; exact hfl1) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x800079c4#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x800079c0#64) 4 = (0x800079c4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hx15_4 : σ4.regs.get? Register.x15
      = some (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2))) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp4 := pins_cons_rt hx15_4 (pins_alu hobs4 (by rfl) hp3.2)  -- [x15z, x2]
  have hmE4 : σ4.mem = c.σ.mem := hmem4.trans hmE3
  -- === 79c4: andi a5,a5,64  (__SMBF clear ⇒ 0) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_800079c4_rt5 σ4 i4 (c.steps + 1 + 1 + 1 + 1) _ vmi4 _
      hG4 hpc4 hmi4 hp4.1 (hmE4 ▸ hload) rfl hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩
      ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x800079c8#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x800079c4#64) 4 = (0x800079c8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx15_5 : σ5.regs.get? Register.x15 = some (0#64) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hflag] at this
  have hp5 := pins_cons_rt hx15_5 (pins_alu hobs5 (by rfl) hp4.2)  -- [x15, x2]
  have hmE5 : σ5.mem = c.σ.mem := hmem5.trans hmE4
  -- === 79c8 … 79e8: the nine callee-save reloads ===
  have hs6m : SlotHolds vsp 0x230 vS2 σ5.mem := by rw [hmE5]; exact h230
  obtain ⟨hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7⟩ := slot_reload_bytes vsp 0x230 vS2 σ5.mem hs6m
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_800079c8_rt σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) _ vmi5 vsp _ _ _ _ _ _ _ _
      hG5 hpc5 hmi5 hp5.2.1 (hmE5 ▸ hload) rfl
      (by rw [hoff560]; omega) (by rw [hoff560]; omega) (Or.inr (by rw [hoff560]; omega))
      (by rw [hoff560]; omega) hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x800079cc#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x800079c8#64) 4 = (0x800079cc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hx18_6 : σ6.regs.get? Register.x18 = some vS2 := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS2] at this
  have hp6 := pins_cons_rt hx18_6 (pins_alu hobs6 (by rfl) hp5)  -- [x18, x15, x2]
  have hmE6 : σ6.mem = c.σ.mem := hmem6.trans hmE5
  -- 79cc: ld s3,552(sp)
  have hs7m : SlotHolds vsp 0x228 vS3 σ6.mem := by rw [hmE6]; exact h228
  obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7⟩ := slot_reload_bytes vsp 0x228 vS3 σ6.mem hs7m
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_800079cc_rt σ6 i6 (c.steps + 6) _ vmi6 vsp _ _ _ _ _ _ _ _
      hG6 hpc6 hmi6 hp6.2.2.1 (hmE6 ▸ hload) rfl
      (by rw [hoff552]; omega) (by rw [hoff552]; omega) (Or.inr (by rw [hoff552]; omega))
      (by rw [hoff552]; omega) hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7 hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 6 + 1⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x800079d0#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x800079cc#64) 4 = (0x800079d0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hx19_7 : σ7.regs.get? Register.x19 = some vS3 := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS3] at this
  have hp7 := pins_cons_rt hx19_7 (pins_alu hobs7 (by rfl) hp6)  -- [x19, x18, x15, x2]
  have hmE7 : σ7.mem = c.σ.mem := hmem7.trans hmE6
  -- 79d0: ld s4,544(sp)
  have hs8m' : SlotHolds vsp 0x220 vS4 σ7.mem := by rw [hmE7]; exact h220
  obtain ⟨he0, he1, he2, he3, he4, he5, he6, he7⟩ := slot_reload_bytes vsp 0x220 vS4 σ7.mem hs8m'
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_800079d0_rt σ7 i7 (c.steps + 6 + 1) _ vmi7 vsp _ _ _ _ _ _ _ _
      hG7 hpc7 hmi7 hp7.2.2.2.1 (hmE7 ▸ hload) rfl
      (by rw [hoff544]; omega) (by rw [hoff544]; omega) (Or.inr (by rw [hoff544]; omega))
      (by rw [hoff544]; omega) he0 he1 he2 he3 he4 he5 he6 he7 hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 6 + 1⟩ ⟨σ8, i8, c.steps + 6 + 1 + 1⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x800079d4#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x800079d0#64) 4 = (0x800079d4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hx20_8 : σ8.regs.get? Register.x20 = some vS4 := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS4] at this
  have hp8 := pins_cons_rt hx20_8 (pins_alu hobs8 (by rfl) hp7)  -- [x20, x19, x18, x15, x2]
  have hmE8 : σ8.mem = c.σ.mem := hmem8.trans hmE7
  -- 79d4: ld s5,536(sp)
  have hs9m : SlotHolds vsp 0x218 vS5 σ8.mem := by rw [hmE8]; exact h218
  obtain ⟨hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ := slot_reload_bytes vsp 0x218 vS5 σ8.mem hs9m
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_800079d4_rt σ8 i8 (c.steps + 6 + 1 + 1) _ vmi8 vsp _ _ _ _ _ _ _ _
      hG8 hpc8 hmi8 hp8.2.2.2.2.1 (hmE8 ▸ hload) rfl
      (by rw [hoff536]; omega) (by rw [hoff536]; omega) (Or.inr (by rw [hoff536]; omega))
      (by rw [hoff536]; omega) hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 6 + 1 + 1⟩ ⟨σ9, i9, c.steps + 6 + 1 + 1 + 1⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x800079d8#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x800079d4#64) 4 = (0x800079d8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hx21_9 : σ9.regs.get? Register.x21 = some vS5 := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS5] at this
  have hp9 := pins_cons_rt hx21_9 (pins_alu hobs9 (by rfl) hp8)  -- [x21, x20, x19, x18, x15, x2]
  have hmE9 : σ9.mem = c.σ.mem := hmem9.trans hmE8
  -- 79d8: ld s7,520(sp)
  have hs10m : SlotHolds vsp 0x208 vS7 σ9.mem := by rw [hmE9]; exact h208
  obtain ⟨hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7⟩ := slot_reload_bytes vsp 0x208 vS7 σ9.mem hs10m
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_800079d8_rt σ9 i9 (c.steps + 6 + 1 + 1 + 1) _ vmi9 vsp _ _ _ _ _ _ _ _
      hG9 hpc9 hmi9 hp9.2.2.2.2.2.1 (hmE9 ▸ hload) rfl
      (by rw [hoff520]; omega) (by rw [hoff520]; omega) (Or.inr (by rw [hoff520]; omega))
      (by rw [hoff520]; omega) hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 6 + 1 + 1 + 1⟩
      ⟨σ10, i10, c.steps + 6 + 1 + 1 + 1 + 1⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x800079dc#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x800079d8#64) 4 = (0x800079dc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hx23_10 : σ10.regs.get? Register.x23 = some vS7 := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS7] at this
  have hp10 := pins_cons_rt hx23_10 (pins_alu hobs10 (by rfl) hp9)
  -- L10: [x23, x21, x20, x19, x18, x15, x2]
  have hmE10 : σ10.mem = c.σ.mem := hmem10.trans hmE9
  -- 79dc: ld s8,512(sp)
  have hs11m : SlotHolds vsp 0x200 vS8 σ10.mem := by rw [hmE10]; exact h200
  obtain ⟨hh0, hh1, hh2, hh3, hh4, hh5, hh6, hh7⟩ :=
    slot_reload_bytes vsp 0x200 vS8 σ10.mem hs11m
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_800079dc_rt σ10 i10 (c.steps + 10) _ vmi10 vsp _ _ _ _ _ _ _ _
      hG10 hpc10 hmi10 hp10.2.2.2.2.2.2.1 (hmE10 ▸ hload) rfl
      (by rw [hoff512]; omega) (by rw [hoff512]; omega) (Or.inr (by rw [hoff512]; omega))
      (by rw [hoff512]; omega) hh0 hh1 hh2 hh3 hh4 hh5 hh6 hh7 hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 10⟩ ⟨σ11, i11, c.steps + 10 + 1⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x800079e0#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x800079dc#64) 4 = (0x800079e0#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hx24_11 : σ11.regs.get? Register.x24 = some vS8 := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS8] at this
  have hp11 := pins_cons_rt hx24_11 (pins_alu hobs11 (by rfl) hp10)
  -- L11: [x24, x23, x21, x20, x19, x18, x15, x2]
  have hmE11 : σ11.mem = c.σ.mem := hmem11.trans hmE10
  -- 79e0: ld s9,504(sp)
  have hs12m : SlotHolds vsp 0x1f8 vS9 σ11.mem := by rw [hmE11]; exact h1f8
  obtain ⟨hi0, hi1', hi2', hi3', hi4', hi5', hi6', hi7'⟩ :=
    slot_reload_bytes vsp 0x1f8 vS9 σ11.mem hs12m
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_800079e0_rt σ11 i11 (c.steps + 10 + 1) _ vmi11 vsp _ _ _ _ _ _ _ _
      hG11 hpc11 hmi11 hp11.2.2.2.2.2.2.2.1 (hmE11 ▸ hload) rfl
      (by rw [hoff504]; omega) (by rw [hoff504]; omega) (Or.inr (by rw [hoff504]; omega))
      (by rw [hoff504]; omega) hi0 hi1' hi2' hi3' hi4' hi5' hi6' hi7' hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 10 + 1⟩ ⟨σ12, i12, c.steps + 10 + 1 + 1⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x800079e4#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x800079e0#64) 4 = (0x800079e4#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hx25_12 : σ12.regs.get? Register.x25 = some vS9 := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS9] at this
  have hp12 := pins_cons_rt hx25_12 (pins_alu hobs12 (by rfl) hp11)
  -- L12: [x25, x24, x23, x21, x20, x19, x18, x15, x2]
  have hmE12 : σ12.mem = c.σ.mem := hmem12.trans hmE11
  -- 79e4: ld s10,496(sp)
  have hs13m : SlotHolds vsp 0x1f0 vS10 σ12.mem := by rw [hmE12]; exact h1f0
  obtain ⟨hj0, hj1, hj2, hj3, hj4, hj5, hj6, hj7⟩ :=
    slot_reload_bytes vsp 0x1f0 vS10 σ12.mem hs13m
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_800079e4_rt σ12 i12 (c.steps + 10 + 1 + 1) _ vmi12 vsp _ _ _ _ _ _ _ _
      hG12 hpc12 hmi12 hp12.2.2.2.2.2.2.2.2.1 (hmE12 ▸ hload) rfl
      (by rw [hoff496]; omega) (by rw [hoff496]; omega) (Or.inr (by rw [hoff496]; omega))
      (by rw [hoff496]; omega) hj0 hj1 hj2 hj3 hj4 hj5 hj6 hj7 hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 10 + 1 + 1⟩
      ⟨σ13, i13, c.steps + 10 + 1 + 1 + 1⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x800079e8#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x800079e4#64) 4 = (0x800079e8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hx26_13 : σ13.regs.get? Register.x26 = some vS10 := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS10] at this
  have hp13 := pins_cons_rt hx26_13 (pins_alu hobs13 (by rfl) hp12)
  -- L13: [x26, x25, x24, x23, x21, x20, x19, x18, x15, x2]
  have hmE13 : σ13.mem = c.σ.mem := hmem13.trans hmE12
  -- 79e8: ld s11,488(sp)
  have hs14m : SlotHolds vsp 0x1e8 vS11 σ13.mem := by rw [hmE13]; exact h1e8
  obtain ⟨hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7⟩ :=
    slot_reload_bytes vsp 0x1e8 vS11 σ13.mem hs14m
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_800079e8_rt σ13 i13 (c.steps + 10 + 1 + 1 + 1) _ vmi13 vsp _ _ _ _ _ _ _ _
      hG13 hpc13 hmi13 hp13.2.2.2.2.2.2.2.2.2.1 (hmE13 ▸ hload) rfl
      (by rw [hoff488]; omega) (by rw [hoff488]; omega) (Or.inr (by rw [hoff488]; omega))
      (by rw [hoff488]; omega) hk0 hk1 hk2 hk3 hk4 hk5 hk6 hk7 hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 10 + 1 + 1 + 1⟩
      ⟨σ14, i14, c.steps + 10 + 1 + 1 + 1 + 1⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x800079ec#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x800079e8#64) 4 = (0x800079ec#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hx27_14 : σ14.regs.get? Register.x27 = some vS11 := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS11] at this
  have hp14 := pins_cons_rt hx27_14 (pins_alu hobs14 (by rfl) hp13)
  -- L14: [x27, x26, x25, x24, x23, x21, x20, x19, x18, x15, x2]
  have hmE14 : σ14.mem = c.σ.mem := hmem14.trans hmE13
  -- === 79ec: beqz a5 → 0x800079f4 (TAKEN — no __SMBF cleanup) ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_800079ec_taken_rt σ14 i14 (c.steps + 14) _ vmi14 (0#64)
      hG14 hpc14 hmi14 hp14.2.2.2.2.2.2.2.2.2.1 (hmE14 ▸ hload) rfl (by decide) hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 14⟩ ⟨σ15, i15, c.steps + 14 + 1⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x800079f4#64) := by
    have := obs_btaken_pc hobs15
    rwa [site_800079ec_taken_rt_tgt] at this
  obtain ⟨vmi15, hmi15⟩ := obs_btaken_minstret hobs15
  have hp15 := pins_btaken hobs15 (by rfl) hp14
  have hmE15 : σ15.mem = c.σ.mem := hmem15.trans hmE14
  -- === 79f4: ld ra,584(sp) ===
  have hs16m : SlotHolds vsp 0x248 vra0 σ15.mem := by rw [hmE15]; exact h248
  obtain ⟨hl0, hl1, hl2, hl3, hl4, hl5, hl6, hl7⟩ :=
    slot_reload_bytes vsp 0x248 vra0 σ15.mem hs16m
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_800079f4_rt σ15 i15 (c.steps + 14 + 1) _ vmi15 vsp _ _ _ _ _ _ _ _
      hG15 hpc15 hmi15 hp15.2.2.2.2.2.2.2.2.2.2.1 (hmE15 ▸ hload) rfl
      (by rw [hoff584]; omega) (by rw [hoff584]; omega) (Or.inr (by rw [hoff584]; omega))
      (by rw [hoff584]; omega) hl0 hl1 hl2 hl3 hl4 hl5 hl6 hl7 hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 14 + 1⟩ ⟨σ16, i16, c.steps + 14 + 1 + 1⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x800079f8#64) := by
    have := obs_alu_pc hobs16
    rwa [show BitVec.addInt (0x800079f4#64) 4 = (0x800079f8#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  have hx1_16 : σ16.regs.get? Register.x1 = some vra0 := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vra0] at this
  have hp16 := pins_cons_rt hx1_16 (pins_alu hobs16 (by rfl) hp15)
  -- L16: [x1, x27, x26, x25, x24, x23, x21, x20, x19, x18, x15, x2]
  have hmE16 : σ16.mem = c.σ.mem := hmem16.trans hmE15
  -- === 79f8: ld s0,576(sp) ===
  have hs17m : SlotHolds vsp 0x240 vS0o σ16.mem := by rw [hmE16]; exact h240
  obtain ⟨hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7⟩ :=
    slot_reload_bytes vsp 0x240 vS0o σ16.mem hs17m
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_800079f8_rt σ16 i16 (c.steps + 14 + 1 + 1) _ vmi16 vsp _ _ _ _ _ _ _ _
      hG16 hpc16 hmi16 hp16.2.2.2.2.2.2.2.2.2.2.2.1 (hmE16 ▸ hload) rfl
      (by rw [hoff576]; omega) (by rw [hoff576]; omega) (Or.inr (by rw [hoff576]; omega))
      (by rw [hoff576]; omega) hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7 hi16
  have hstep17 : Step ⟨σ16, i16, c.steps + 14 + 1 + 1⟩
      ⟨σ17, i17, c.steps + 14 + 1 + 1 + 1⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x800079fc#64) := by
    have := obs_alu_pc hobs17
    rwa [show BitVec.addInt (0x800079f8#64) 4 = (0x800079fc#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi17, hmi17⟩ := obs_alu_minstret hobs17
  have hx8_17 : σ17.regs.get? Register.x8 = some vS0o := by
    have := obs_alu_rd hobs17 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS0o] at this
  have hp17 := pins_cons_rt hx8_17 (pins_alu hobs17 (by rfl) hp16)
  -- L17: [x8, x1, x27, x26, x25, x24, x23, x21, x20, x19, x18, x15, x2]
  have hmE17 : σ17.mem = c.σ.mem := hmem17.trans hmE16
  -- === 79fc: ld a0,16(sp)  ⇐ THE TOTAL ===
  have hs18m : SlotHolds vsp 0x010 vtot σ17.mem := by rw [hmE17]; exact h010
  obtain ⟨hn0, hn1, hn2, hn3, hn4, hn5, hn6, hn7⟩ :=
    slot_reload_bytes vsp 0x010 vtot σ17.mem hs18m
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_800079fc_rt σ17 i17 (c.steps + 14 + 1 + 1 + 1) _ vmi17 vsp _ _ _ _ _ _ _ _
      hG17 hpc17 hmi17 hp17.2.2.2.2.2.2.2.2.2.2.2.2.1 (hmE17 ▸ hload) rfl
      (by rw [hoff16]; omega) (by rw [hoff16]; omega) (Or.inr (by rw [hoff16]; omega))
      (by rw [hoff16]; omega) hn0 hn1 hn2 hn3 hn4 hn5 hn6 hn7 hi17
  have hstep18 : Step ⟨σ17, i17, c.steps + 14 + 1 + 1 + 1⟩
      ⟨σ18, i18, c.steps + 14 + 1 + 1 + 1 + 1⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x80007a00#64) := by
    have := obs_alu_pc hobs18
    rwa [show BitVec.addInt (0x800079fc#64) 4 = (0x80007a00#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi18, hmi18⟩ := obs_alu_minstret hobs18
  have hx10_18 : σ18.regs.get? Register.x10 = some vtot := by
    have := obs_alu_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vtot] at this
  have hp18 := pins_cons_rt hx10_18 (pins_alu hobs18 (by rfl) hp17)
  -- L18: [x10, x8, x1, x27, x26, x25, x24, x23, x21, x20, x19, x18, x15, x2]
  have hmE18 : σ18.mem = c.σ.mem := hmem18.trans hmE17
  -- === 7a00: ld s1,568(sp)  (FlushPins tail) ===
  have hs19m : SlotHolds vsp 0x238 vS1o σ18.mem := by rw [hmE18]; exact h238
  obtain ⟨ho0, ho1, ho2, ho3, ho4, ho5, ho6, ho7⟩ :=
    slot_reload_bytes vsp 0x238 vS1o σ18.mem hs19m
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_80007a00_rt2 σ18 i18 (c.steps + 18) _ vmi18 vsp _ _ _ _ _ _ _ _
      hG18 hpc18 hmi18 hp18.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hmE18 ▸ hfp) rfl
      (by rw [hoff568]; omega) (by rw [hoff568]; omega) (Or.inr (by rw [hoff568]; omega))
      (by rw [hoff568]; omega) ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7 hi18
  have hstep19 : Step ⟨σ18, i18, c.steps + 18⟩ ⟨σ19, i19, c.steps + 18 + 1⟩ := hs19
  have hpc19 : σ19.regs.get? Register.PC = some (0x80007a04#64) := by
    have := obs_alu_pc hobs19
    rwa [show BitVec.addInt (0x80007a00#64) 4 = (0x80007a04#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi19, hmi19⟩ := obs_alu_minstret hobs19
  have hx9_19 : σ19.regs.get? Register.x9 = some vS1o := by
    have := obs_alu_rd hobs19 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS1o] at this
  have hp19 := pins_cons_rt hx9_19 (pins_alu hobs19 (by rfl) hp18)
  -- L19: [x9, x10, x8, x1, x27, x26, x25, x24, x23, x21, x20, x19, x18, x15, x2]
  have hmE19 : σ19.mem = c.σ.mem := hmem19.trans hmE18
  -- === 7a04: ld s6,528(sp) ===
  have hs20m : SlotHolds vsp 0x210 vS6o σ19.mem := by rw [hmE19]; exact h210
  obtain ⟨hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7⟩ :=
    slot_reload_bytes vsp 0x210 vS6o σ19.mem hs20m
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_80007a04_rt2 σ19 i19 (c.steps + 18 + 1) _ vmi19 vsp _ _ _ _ _ _ _ _
      hG19 hpc19 hmi19 hp19.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hmE19 ▸ hfp) rfl
      (by rw [hoff528]; omega) (by rw [hoff528]; omega) (Or.inr (by rw [hoff528]; omega))
      (by rw [hoff528]; omega) hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7 hi19
  have hstep20 : Step ⟨σ19, i19, c.steps + 18 + 1⟩ ⟨σ20, i20, c.steps + 18 + 1 + 1⟩ := hs20
  have hpc20 : σ20.regs.get? Register.PC = some (0x80007a08#64) := by
    have := obs_alu_pc hobs20
    rwa [show BitVec.addInt (0x80007a04#64) 4 = (0x80007a08#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi20, hmi20⟩ := obs_alu_minstret hobs20
  have hx22_20 : σ20.regs.get? Register.x22 = some vS6o := by
    have := obs_alu_rd hobs20 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS6o] at this
  have hp20 := pins_cons_rt hx22_20 (pins_alu hobs20 (by rfl) hp19)
  -- L20: [x22, x9, x10, x8, x1, x27, x26, x25, x24, x23, x21, x20, x19, x18, x15, x2]
  have hmE20 : σ20.mem = c.σ.mem := hmem20.trans hmE19
  -- === 7a08: addi sp,sp,592 ===
  obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
    site_80007a08_rt2 σ20 i20 (c.steps + 18 + 1 + 1) _ vmi20 vsp
      hG20 hpc20 hmi20 hp20.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (hmE20 ▸ hfp) rfl hi20
  have hstep21 : Step ⟨σ20, i20, c.steps + 18 + 1 + 1⟩
      ⟨σ21, i21, c.steps + 18 + 1 + 1 + 1⟩ := hs21
  have hpc21 : σ21.regs.get? Register.PC = some (0x80007a0c#64) := by
    have := obs_alu_pc hobs21
    rwa [show BitVec.addInt (0x80007a08#64) 4 = (0x80007a0c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi21, hmi21⟩ := obs_alu_minstret hobs21
  have hx2_21 : σ21.regs.get? Register.x2 = some (vsp + (592#64)) := by
    have := obs_alu_rd hobs21 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) (0x250#12) : BitVec 64) = (592#64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hp21 := pins_cons_rt hx2_21 (pins_alu hobs21 (by rfl) (pins_drop16_rt hp20))
  -- L21: [x2, x22, x9, x10, x8, x1, x27, x26, x25, x24, x23, x21, x20, x19, x18]
  have hmE21 : σ21.mem = c.σ.mem := hmem21.trans hmE20
  -- === 7a0c: ret  (PC := vra0) ===
  obtain ⟨σ22, i22, hs22, hi22, hG22, hmem22, hobs22⟩ :=
    site_80007a0c_rt2 σ21 i21 (c.steps + 18 + 1 + 1 + 1) _ vmi21 vra0
      hG21 hpc21 hmi21 hp21.2.2.2.2.2.1 (hmE21 ▸ hfp) rfl
      (by rw [ret_tgt vra0 hra0align]; exact hra0align) hi21
  have hstep22 : Step ⟨σ21, i21, c.steps + 18 + 1 + 1 + 1⟩
      ⟨σ22, i22, c.steps + 18 + 1 + 1 + 1 + 1⟩ := hs22
  have hpc22 : σ22.regs.get? Register.PC = some vra0 := by
    have := obs_jr_pc hobs22
    rwa [ret_tgt vra0 hra0align] at this
  obtain ⟨vmi22, hmi22⟩ := obs_jr_minstret hobs22
  have hp22 := pins_jr hobs22 (by rfl) hp21
  have hmE22 : σ22.mem = c.σ.mem := hmem22.trans hmE21
  -- L22 = L21: [x2, x22, x9, x10, x8, x1, x27, x26, x25, x24, x23, x21, x20, x19, x18]
  refine ⟨⟨σ22, i22, c.steps + 18 + 1 + 1 + 1 + 1⟩, ?_, hG22, hpc22,
    hp22.2.2.2.2.2.1, hp22.1, hp22.2.2.2.1, hp22.2.2.2.2.1, hp22.2.2.1,
    hp22.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, hp22.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp22.2.2.2.2.2.2.2.2.2.2.2.2.1, hp22.2.2.2.2.2.2.2.2.2.2.2.1, hp22.2.1,
    hp22.2.2.2.2.2.2.2.2.2.2.1, hp22.2.2.2.2.2.2.2.2.2.1, hp22.2.2.2.2.2.2.2.2.1,
    hp22.2.2.2.2.2.2.2.1, hp22.2.2.2.2.2.2.1,
    hmE22, hi22, ⟨vmi22, hmi22⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
    ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
    ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
    ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans
    ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans
    ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans
    ((Steps.single hstep19).trans ((Steps.single hstep20).trans ((Steps.single hstep21).trans
    (Steps.single hstep22)))))))))))))))))))))

end Vsa.Sim
