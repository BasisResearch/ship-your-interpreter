import Vsa.Sim.SnprintfSpec40

/-!
# M3 Layer-3 — `SnprintfSpec41` : the snprintf wrapper POST-CALL segment
## `0x80005cbc` (return from `_svfprintf_r`) → snprintf's `ret`

The 10-instruction return path of newlib's `snprintf`: error check (`a0 ≥ -1`,
not taken), `bnez s0` to the NUL-terminate arm (`sz ≠ 0`), reload of the
updated FILE cursor from `sp+8`, the `sb zero,0(a5)` **NUL terminator** at
`d + total`, the three callee-save reloads, the frame release, and the `ret`.
`snprintf` returns `_svfprintf_r`'s total in `a0` unchanged.

Emitted by `scripts/pro_emitter/gen_spec41.py` (SnprintfSpec27/40 house style).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The `blt a0,a5` guard with `a5 = -1`: a small non-negative `a0` is not
signed-below `-1`. -/
theorem blt_m1_false_wr (x : BitVec 64) (hx : x.toNat < 2 ^ 63) :
    zopz0zI_s x ((0#64) + sign_extend (m := 64) (0xfff#12)) = false := by
  unfold zopz0zI_s
  rw [show (((0#64) + sign_extend (m := 64) (0xfff#12)) : BitVec 64).toInt = -1 from by decide,
    toInt_of_notop x hx]
  exact decide_eq_false (by omega)

/-- **The snprintf wrapper POST-CALL segment**: `0x80005cbc → ret` (`PC = wra0`).

From `_svfprintf_r`'s return (`a0 = va0r` = the total, small and non-negative;
`s0 = sz ≠ 0`) through the error check (`blt` not taken), the `bnez` to the
NUL-terminate arm, the reload of the updated FILE cursor `vcur = d + total`
from `sp+8` (`Pin8`), the `sb zero,0(a5)` NUL terminator, the three
`SlotHolds` epilogue reloads, the frame release, and the `ret`.

Post: `PC = x1 = wra0`, `sp = vsp + 864`, `a0 = va0r` preserved, `s0/s1`
restored, and the memory is exactly the entry memory plus the single NUL byte
at `vcur`. -/
theorem snprintfPostCall_spec
    (vsp wra0 vcur sz va0r : BitVec 64)
    (vS0o vS1o vS2o vS3o vS4o vS5o vS6o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SnprintfLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80005cbc#64))
    (hx2 : c.σ.regs.get? Register.x2 = some (vsp + (592#64)))
    (hx10 : c.σ.regs.get? Register.x10 = some va0r)
    (hx8 : c.σ.regs.get? Register.x8 = some sz)
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx22 : c.σ.regs.get? Register.x22 = some vS6o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    (hcur : Pin8 c.σ.mem (vsp.toNat + 600) vcur)
    (hS0c8 : SlotHolds (vsp + (592#64)) 0x0c8 vS1o c.σ.mem)
    (hS0d0 : SlotHolds (vsp + (592#64)) 0x0d0 vS0o c.σ.mem)
    (hS0d8 : SlotHolds (vsp + (592#64)) 0x0d8 wra0 c.σ.mem)
    (hva0r : va0r.toNat < 2 ^ 63)
    (hsz : 1 ≤ sz.toNat)
    (hcurge : 0x8001c000 ≤ vcur.toNat)
    (hcurhi : vcur.toNat + 1 ≤ 0x100000000)
    (hcurdisj : vcur.toNat + 1 ≤ vsp.toNat + 592 ∨ vsp.toNat + 864 ≤ vcur.toNat)
    (hwra : wra0.toNat % 4 = 0)
    (hsplo : 0x8001c100 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 864 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some wra0 ∧
      c'.σ.regs.get? Register.x1 = some wra0 ∧
      c'.σ.regs.get? Register.x2 = some (vsp + (864#64)) ∧
      c'.σ.regs.get? Register.x10 = some va0r ∧
      c'.σ.regs.get? Register.x8 = some vS0o ∧
      c'.σ.regs.get? Register.x9 = some vS1o ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some vS5o ∧
      c'.σ.regs.get? Register.x22 = some vS6o ∧
      c'.σ.regs.get? Register.x23 = some vS7o ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      c'.σ.mem = (c.σ.mem).insert (vcur.toNat) (stData 1 (0#64)) ∧
      Vsa.Sim.Code.SnprintfLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have h592 : ((vsp + (592#64)) : BitVec 64).toNat = vsp.toNat + 592 := by
    rw [BitVec.toNat_add, show ((592#64 : BitVec 64)).toNat = 592 from rfl]
    exact Nat.mod_eq_of_lt (by omega)
  have hoff600 : ((vsp + (592#64)) + sign_extend (m := 64) (0x008#12)).toNat = vsp.toNat + 600 := by
    rw [ptr_addoff (vsp + (592#64)) _ 8 (by decide) (by rw [h592]; omega), h592]
  have hoff792 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0c8#12)).toNat = vsp.toNat + 792 := by
    rw [ptr_addoff (vsp + (592#64)) _ 200 (by decide) (by rw [h592]; omega), h592]
  have hoff800 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0d0#12)).toNat = vsp.toNat + 800 := by
    rw [ptr_addoff (vsp + (592#64)) _ 208 (by decide) (by rw [h592]; omega), h592]
  have hoff808 : ((vsp + (592#64)) + sign_extend (m := 64) (0x0d8#12)).toNat = vsp.toNat + 808 := by
    rw [ptr_addoff (vsp + (592#64)) _ 216 (by decide) (by rw [h592]; omega), h592]
  have hoffcur : ((vcur + sign_extend (m := 64) (0x000#12)) : BitVec 64).toNat = vcur.toNat := by rw [sext0_add_pro vcur]
  have hp0 : PinsHold c.σ [⟨Register.x2, (vsp + (592#64))⟩, ⟨Register.x10, va0r⟩, ⟨Register.x8, sz⟩, ⟨Register.x18, vS2o⟩, ⟨Register.x19, vS3o⟩, ⟨Register.x20, vS4o⟩, ⟨Register.x21, vS5o⟩, ⟨Register.x22, vS6o⟩, ⟨Register.x23, vS7o⟩, ⟨Register.x24, vS8o⟩, ⟨Register.x25, vS9o⟩, ⟨Register.x26, vS10o⟩, ⟨Register.x27, vS11o⟩] :=
    ⟨hx2, hx10, hx8, hx18, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, trivial⟩
  -- === 0x80005cbc: li a5,-1 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80005cbc_wp c.σ c.tick c.steps _ vmi0
      hG hpc hmi0 hsl0 rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80005cc0#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80005cbc#64) 4 = (0x80005cc0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hrd1 : σ1.regs.get? Register.x15 = some (((0#64) + sign_extend (m := 64) (0xfff#12))) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp1 := pins_cons_pro hrd1 (pins_alu hobs1 (by rfl) hp0)
  have hmE1 : σ1.mem = c.σ.mem := hmem1
  have hsl1 : Vsa.Sim.Code.SnprintfLoaded σ1.mem := by rw [hmem1]; exact hsl0

  -- === 0x80005cc0: blt a0,a5 — NOT taken (a0 ≥ 0) ===
  have hgs2 : zopz0zI_s va0r ((0#64) + sign_extend (m := 64) (0xfff#12)) = false := blt_m1_false_wr va0r hva0r
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80005cc0_nottaken_wp σ1 i1 (c.steps + 1) _ vmi1 va0r _
      hG1 hpc1 hmi1 hp1.2.2.1 hp1.1 hsl1 rfl hgs2 hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 2⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80005cc4#64) := by
    have := obs_bnottaken_pc hobs2
    rwa [show BitVec.addInt (0x80005cc0#64) 4 = (0x80005cc4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_bnottaken_minstret hobs2
  have hp2 := pins_bnottaken hobs2 (by rfl) hp1
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1
  have hsl2 : Vsa.Sim.Code.SnprintfLoaded σ2.mem := by rw [hmem2]; exact hsl1

  -- === 0x80005cc4: bnez s0 — TAKEN (sz ≠ 0), to the NUL-terminate arm ===
  have hgn3 : (sz != (0#64)) = true := by simp only [bne]; rw [beq64_false_pro sz (0#64) (by rw [show ((0#64 : BitVec 64)).toNat = 0 from rfl]; omega)]; rfl
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80005cc4_taken_wp σ2 i2 (c.steps + 2) _ vmi2 sz
      hG2 hpc2 hmi2 hp2.2.2.2.1 hsl2 rfl hgn3 hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 2⟩ ⟨σ3, i3, c.steps + 3⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80005cdc#64) := by
    have := obs_btaken_pc hobs3
    rwa [show (0x80005cc4#64 : BitVec 64) + sign_extend (m := 64) (0x0018#13) = (0x80005cdc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_btaken_minstret hobs3
  have hp3 := pins_btaken hobs3 (by rfl) hp2
  have hmE3 : σ3.mem = c.σ.mem := hmem3.trans hmE2
  have hsl3 : Vsa.Sim.Code.SnprintfLoaded σ3.mem := by rw [hmem3]; exact hsl2

  -- === 0x80005cdc: ld a5,8(sp) — a5 := the updated cursor d+total ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80005cdc_wp σ3 i3 (c.steps + 3) _ vmi3 (vsp + (592#64)) _ _ _ _ _ _ _ _
      hG3 hpc3 hmi3 hp3.2.1 hsl3 rfl (by rw [hoff600]; omega) (by rw [hoff600]; omega) (by rw [hoff600, htoh]; omega) (by rw [hoff600]; omega) (by rw [hoff600, hmE3]; exact hcur.1) (by rw [hoff600, hmE3]; exact hcur.2.1) (by rw [hoff600, hmE3]; exact hcur.2.2.1) (by rw [hoff600, hmE3]; exact hcur.2.2.2.1) (by rw [hoff600, hmE3]; exact hcur.2.2.2.2.1) (by rw [hoff600, hmE3]; exact hcur.2.2.2.2.2.1) (by rw [hoff600, hmE3]; exact hcur.2.2.2.2.2.2.1) (by rw [hoff600, hmE3]; exact hcur.2.2.2.2.2.2.2) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 3⟩ ⟨σ4, i4, c.steps + 4⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80005ce0#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80005cdc#64) 4 = (0x80005ce0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hrd4 : σ4.regs.get? Register.x15 = some (vcur) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vcur] at this
  have hp4 := pins_cons_pro hrd4 (pins_alu hobs4 (by rfl) hp3.2)
  have hmE4 : σ4.mem = c.σ.mem := hmem4.trans hmE3
  have hsl4 : Vsa.Sim.Code.SnprintfLoaded σ4.mem := by rw [hmem4]; exact hsl3

  -- === 0x80005ce0: sb zero,0(a5) — NUL-terminate at d+total ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80005ce0_wp σ4 i4 (c.steps + 4) _ vmi4 vcur
      hG4 hpc4 hmi4 hp4.1 hsl4 rfl (by rw [hoffcur]; omega) (by rw [hoffcur]; omega) (by rw [hoffcur, htoh]; omega) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 4⟩ ⟨σ5, i5, c.steps + 5⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80005ce4#64) := by
    have := obs_store_pc hobs5
    rwa [show BitVec.addInt (0x80005ce0#64) 4 = (0x80005ce4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret hobs5
  have hp5 := pins_store hobs5 (by rfl) hp4
  have hmE5 : σ5.mem = (c.σ.mem).insert (vcur.toNat) (stData 1 (0#64)) := by
    rw [hmem5, mem_afterNextPC, hmE4, hoffcur]
  have hsl5 : Vsa.Sim.Code.SnprintfLoaded σ5.mem := by
    rw [hmem5, mem_afterNextPC]
    exact snprintf_insert_wr _ _ _ (by rw [hoffcur]; omega) hsl4

  -- the three save slots survive the NUL byte (vcur is outside the frame)
  have hS0d0x : SlotHolds (vsp + (592#64)) 0x0d0 vS0o σ5.mem := by
    rw [hmE5]
    exact slot_survives_insert _ _ _ _ _ _ (by rw [hoff800]; omega) hS0d0
  have hS0d8x : SlotHolds (vsp + (592#64)) 0x0d8 wra0 σ5.mem := by
    rw [hmE5]
    exact slot_survives_insert _ _ _ _ _ _ (by rw [hoff808]; omega) hS0d8
  have hS0c8x : SlotHolds (vsp + (592#64)) 0x0c8 vS1o σ5.mem := by
    rw [hmE5]
    exact slot_survives_insert _ _ _ _ _ _ (by rw [hoff792]; omega) hS0c8

  -- === 0x80005ce4: ld x8,208(sp) — reload vS0o ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80005ce4_wp σ5 i5 (c.steps + 5) _ vmi5 (vsp + (592#64)) _ _ _ _ _ _ _ _
      hG5 hpc5 hmi5 hp5.2.1 hsl5 rfl (by rw [hoff800]; omega) (by rw [hoff800]; omega) (by rw [hoff800, htoh]; omega) (by rw [hoff800]; omega) hS0d0x.1 hS0d0x.2.1 hS0d0x.2.2.1 hS0d0x.2.2.2.1 hS0d0x.2.2.2.2.1 hS0d0x.2.2.2.2.2.1 hS0d0x.2.2.2.2.2.2.1 hS0d0x.2.2.2.2.2.2.2 hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 5⟩ ⟨σ6, i6, c.steps + 6⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80005ce8#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80005ce4#64) 4 = (0x80005ce8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hrd6 : σ6.regs.get? Register.x8 = some (vS0o) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS0o] at this
  have hp6 := pins_cons_pro hrd6 (pins_alu hobs6 (by rfl) (pins_drop4_pro hp5))
  have hmE6 : σ6.mem = (c.σ.mem).insert (vcur.toNat) (stData 1 (0#64)) := hmem6.trans hmE5
  have hS0d8y : SlotHolds (vsp + (592#64)) 0x0d8 wra0 σ6.mem := by rw [hmem6]; exact hS0d8x
  have hS0c8y : SlotHolds (vsp + (592#64)) 0x0c8 vS1o σ6.mem := by rw [hmem6]; exact hS0c8x
  have hsl6 : Vsa.Sim.Code.SnprintfLoaded σ6.mem := by rw [hmem6]; exact hsl5

  -- === 0x80005ce8: ld x1,216(sp) — reload wra0 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80005ce8_wp σ6 i6 (c.steps + 6) _ vmi6 (vsp + (592#64)) _ _ _ _ _ _ _ _
      hG6 hpc6 hmi6 hp6.2.2.1 hsl6 rfl (by rw [hoff808]; omega) (by rw [hoff808]; omega) (by rw [hoff808, htoh]; omega) (by rw [hoff808]; omega) hS0d8y.1 hS0d8y.2.1 hS0d8y.2.2.1 hS0d8y.2.2.2.1 hS0d8y.2.2.2.2.1 hS0d8y.2.2.2.2.2.1 hS0d8y.2.2.2.2.2.2.1 hS0d8y.2.2.2.2.2.2.2 hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 7⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80005cec#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80005ce8#64) 4 = (0x80005cec#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hrd7 : σ7.regs.get? Register.x1 = some (wra0) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble wra0] at this
  have hp7 := pins_cons_pro hrd7 (pins_alu hobs7 (by rfl) hp6)
  have hmE7 : σ7.mem = (c.σ.mem).insert (vcur.toNat) (stData 1 (0#64)) := hmem7.trans hmE6
  have hS0c8z : SlotHolds (vsp + (592#64)) 0x0c8 vS1o σ7.mem := by rw [hmem7]; exact hS0c8y
  have hsl7 : Vsa.Sim.Code.SnprintfLoaded σ7.mem := by rw [hmem7]; exact hsl6

  -- === 0x80005cec: ld x9,200(sp) — reload vS1o ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80005cec_wp σ7 i7 (c.steps + 7) _ vmi7 (vsp + (592#64)) _ _ _ _ _ _ _ _
      hG7 hpc7 hmi7 hp7.2.2.2.1 hsl7 rfl (by rw [hoff792]; omega) (by rw [hoff792]; omega) (by rw [hoff792, htoh]; omega) (by rw [hoff792]; omega) hS0c8z.1 hS0c8z.2.1 hS0c8z.2.2.1 hS0c8z.2.2.2.1 hS0c8z.2.2.2.2.1 hS0c8z.2.2.2.2.2.1 hS0c8z.2.2.2.2.2.2.1 hS0c8z.2.2.2.2.2.2.2 hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 7⟩ ⟨σ8, i8, c.steps + 8⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80005cf0#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80005cec#64) 4 = (0x80005cf0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hrd8 : σ8.regs.get? Register.x9 = some (vS1o) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vS1o] at this
  have hp8 := pins_cons_pro hrd8 (pins_alu hobs8 (by rfl) hp7)
  have hmE8 : σ8.mem = (c.σ.mem).insert (vcur.toNat) (stData 1 (0#64)) := hmem8.trans hmE7
  have hsl8 : Vsa.Sim.Code.SnprintfLoaded σ8.mem := by rw [hmem8]; exact hsl7

  -- === 0x80005cf0: addi sp,sp,272 — frame released ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80005cf0_wp σ8 i8 (c.steps + 8) _ vmi8 (vsp + (592#64))
      hG8 hpc8 hmi8 hp8.2.2.2.2.1 hsl8 rfl hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 8⟩ ⟨σ9, i9, c.steps + 9⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80005cf4#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x80005cf0#64) 4 = (0x80005cf4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hrd9 : σ9.regs.get? Register.x2 = some ((vsp + (864#64))) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sp_inc272_wr vsp] at this
  have hp9 := pins_cons_pro hrd9 (pins_alu hobs9 (by rfl) (pins_drop5_pro hp8))
  have hmE9 : σ9.mem = (c.σ.mem).insert (vcur.toNat) (stData 1 (0#64)) := hmem9.trans hmE8
  have hsl9 : Vsa.Sim.Code.SnprintfLoaded σ9.mem := by rw [hmem9]; exact hsl8

  -- === 0x80005cf4: ret — back to the snprintf caller ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80005cf4_wp σ9 i9 (c.steps + 9) _ vmi9 wra0
      hG9 hpc9 hmi9 hp9.2.2.1 hsl9 rfl (by rw [ret_tgt _ hwra]; exact hwra) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 9⟩ ⟨σ10, i10, c.steps + 10⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some wra0 := by
    have := obs_jr_pc hobs10
    rwa [ret_tgt _ hwra] at this
  obtain ⟨vmi10, hmi10⟩ := obs_jr_minstret hobs10
  have hp10 := pins_jr hobs10 (by rfl) hp9
  have hmE10 : σ10.mem = (c.σ.mem).insert (vcur.toNat) (stData 1 (0#64)) := hmem10.trans hmE9
  have hsl10 : Vsa.Sim.Code.SnprintfLoaded σ10.mem := by rw [hmem10]; exact hsl9

  refine ⟨⟨σ10, i10, c.steps + 10⟩, ?_,
    hG10,
    hpc10,
    hp10.2.2.1,
    hp10.1,
    hp10.2.2.2.2.2.1,
    hp10.2.2.2.1,
    hp10.2.1,
    hp10.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hmE10,
    hsl10,
    hi10,
    ⟨vmi10, hmi10⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans (Steps.single hstep10)))))))))

end Vsa.Sim
