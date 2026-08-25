import Vsa.Sim.SnprintfSitesFlush
import Vsa.Sim.SnprintfSpec6
import Vsa.Sim.ValueEqualSpec3

/-!
# M3 Layer-3 — `SnprintfSpec7` : the exit-restore + flush hops, composed (`_fl`)

From the digit-loop exit `0x80008358` (the state `signToDigits_neg_spec`
delivers), step the restore block — five spill reloads folding back to their
stored 64-bit values (`ve_sext_reassemble`), `len = top − cursor` (32-bit
`subw`), the width test (`width < len`, not taken for `%lld`), the **sign-byte
read-back** `lbu t5,167(sp)`, `t6 := 0` — and the three hops, landing at the
PRINT entry `0x8000782c` with `a6 = len+1` (sign included) and every restored
register pinned.  The spill-slot contents arrive as `sdData_val`-shaped
hypotheses — exactly what the entry block stored (`SnprintfSpec5`) and the
digit loop preserved (`DigitFrame`); wiring those through `loopEntry_spec`'s
postcondition is the remaining glue, together with the PRINT/iov segment and
`__ssprint_r` + memcpy.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded SvfprintfSliceLoaded FlushPinsLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Read-over-write for the flush-pin region: stack stores sit above `0x8000b000`. -/
theorem getElem?_insert_aboveB_fl (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x8000b000 ≤ k) (a : Nat) (ha : a < 0x8000b000) :
    (mem.insert k v)[a]? = mem[a]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem flushPins_insert_fl (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : 0x8000b000 ≤ k) (h : FlushPinsLoaded mem) : FlushPinsLoaded (mem.insert k v) := by
  unfold FlushPinsLoaded Vsa.Sim.Code.flushPinsChunk0 at h ⊢
  simp (disch := omega) only [getElem?_insert_aboveB_fl mem k v hk]
  exact h

theorem flushPins_writeMap8_fl (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat)
    (d : BitVec (8 * 8)) (ha : 0x8000b000 ≤ a) (h : FlushPinsLoaded mem) :
    FlushPinsLoaded (writeMap8 mem a d) :=
  flushPins_insert_fl _ _ _ (by omega) (flushPins_insert_fl _ _ _ (by omega)
    (flushPins_insert_fl _ _ _ (by omega) (flushPins_insert_fl _ _ _ (by omega)
    (flushPins_insert_fl _ _ _ (by omega) (flushPins_insert_fl _ _ _ (by omega)
    (flushPins_insert_fl _ _ _ (by omega) (flushPins_insert_fl _ _ _ (by omega) h)))))))

/-- `extractLsb 31 0` undoes a 32→64 `sign_extend`. -/
theorem extract_sext32_fl (w : BitVec 32) :
    Sail.BitVec.extractLsb (sign_extend (m := 64) w : BitVec 64) 31 0 = w := by
  show ((sign_extend (m := 64) w : BitVec 64).extractLsb 31 0) = w
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat (31-0+1) (((w.signExtend 64)).toNat >>> 0)).toNat = w.toNat
  rw [Nat.shiftRight_zero, BitVec.toNat_ofNat, BitVec.toNat_signExtend]
  have hw := w.isLt
  have hsw : (w.setWidth 64).toNat = w.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.reduceSub, Nat.reduceAdd, hsw]
  rcases hmsb : w.msb with _ | _
  · simp only [hmsb, Bool.false_eq_true, if_false, Nat.add_zero]
    exact Nat.mod_eq_of_lt hw
  · simp only [hmsb, if_true]
    rw [show (2:Nat) ^ 64 - 2 ^ 32 = (2 ^ 32 - 1) * (2 ^ 32) from by decide,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]


theorem exitToPrint_spec
    (vsp vtop vwidth vflags vt3v vs7v vs0v vcur vs4j vcnt : BitVec 64) (sb : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80008358#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx26 : c.σ.regs.get? Register.x26 = some vcur)
    (hx20 : c.σ.regs.get? Register.x20 = some vs4j)
    (hx23 : c.σ.regs.get? Register.x23 = some vcnt)
    (hs112 : SlotHolds vsp 0x070 vtop c.σ.mem)
    (hs56 : SlotHolds vsp 0x038 vwidth c.σ.mem)
    (hs40 : SlotHolds vsp 0x028 vflags c.σ.mem)
    (hs32 : SlotHolds vsp 0x020 vt3v c.σ.mem)
    (hs48 : SlotHolds vsp 0x030 vs7v c.σ.mem)
    (hs120 : SlotHolds vsp 0x078 vs0v c.σ.mem)
    (hsb : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb)
    (hsbne : ((zero_extend (m := 64) sb : BitVec 64) == (0#64)) = false)
    (hwlt : zopz0zKzJ_s vwidth (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) = false)
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000782c#64) ∧
      c'.σ.regs.get? Register.x22 = some (sign_extend (m := 64)
        ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) ∧
      c'.σ.regs.get? Register.x16 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64)
          ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
          + sign_extend (m := 64) (0x001#12)) 31 0)) ∧
      c'.σ.regs.get? Register.x30 = some (zero_extend (m := 64) sb) ∧
      c'.σ.regs.get? Register.x31 = some (0#64) ∧
      c'.σ.regs.get? Register.x20 = some vwidth ∧
      c'.σ.regs.get? Register.x6 = some vflags ∧
      c'.σ.regs.get? Register.x28 = some vt3v ∧
      c'.σ.regs.get? Register.x23 = some vs7v ∧
      c'.σ.regs.get? Register.x8 = some vs0v ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧
      -- post-widening: parse slot sp+0x20 re-zeroed (`sd zero,32(sp)`), the
      -- mid-registers + the untouched digit cursor x26 preserved, the pointwise
      -- memory frame outside the two written windows, and the code pins
      SlotHolds vsp 0x020 (0#64) c'.σ.mem ∧
      KeepRegs (Register.x26 :: midRegs5) c.σ c'.σ ∧
      (∀ a : Nat, ¬(vsp.toNat + 32 ≤ a ∧ a < vsp.toNat + 64) →
        ¬(vsp.toNat + 104 ≤ a ∧ a < vsp.toNat + 112) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      SvfprintfSliceLoaded c'.σ.mem ∧ FlushPinsLoaded c'.σ.mem := by
  have htohv : tohostAddr = 0x8001ad00 := rfl
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff112 : (vsp + sign_extend (m := 64) (0x070#12)).toNat = vsp.toNat + 112 :=
    addoff_toNat_sn5 vsp (0x070#12) 112 (by omega) (by decide) hnw
  have hoff104 : (vsp + sign_extend (m := 64) (0x068#12)).toNat = vsp.toNat + 104 :=
    addoff_toNat_sn5 vsp (0x068#12) 104 (by omega) (by decide) hnw
  have hoff56 : (vsp + sign_extend (m := 64) (0x038#12)).toNat = vsp.toNat + 56 :=
    addoff_toNat_sn5 vsp (0x038#12) 56 (by omega) (by decide) hnw
  have hoff40 : (vsp + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat + 40 :=
    addoff_toNat_sn5 vsp (0x028#12) 40 (by omega) (by decide) hnw
  have hoff32 : (vsp + sign_extend (m := 64) (0x020#12)).toNat = vsp.toNat + 32 :=
    addoff_toNat_sn5 vsp (0x020#12) 32 (by omega) (by decide) hnw
  have hoff48 : (vsp + sign_extend (m := 64) (0x030#12)).toNat = vsp.toNat + 48 :=
    addoff_toNat_sn5 vsp (0x030#12) 48 (by omega) (by decide) hnw
  have hoff120 : (vsp + sign_extend (m := 64) (0x078#12)).toNat = vsp.toNat + 120 :=
    addoff_toNat_sn5 vsp (0x078#12) 120 (by omega) (by decide) hnw
  have hoff167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    addoff_toNat_sn5 vsp (0x0a7#12) 167 (by omega) (by decide) hnw
  -- name the entry hypotheses as step-0 facts
  have hx2_0 := hx2
  have hx26_0 := hx26
  have hx20_0 := hx20
  have hx23_0 := hx23
  have hload0 : SvfprintfSliceLoaded c.σ.mem := hload
  have hfp0 : FlushPinsLoaded c.σ.mem := hfp
  -- === 8358: ld s6,112(sp) ⇒ x22 := top ===
  obtain ⟨h112a, h112b, h112c, h112d, h112e, h112f, h112g, h112h⟩ := hs112
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80008358_fl c.σ c.tick c.steps (0x80008358#64) vmi0 vsp
      ((sdData_val vtop).extractLsb' 0 8) ((sdData_val vtop).extractLsb' 8 8)
      ((sdData_val vtop).extractLsb' 16 8) ((sdData_val vtop).extractLsb' 24 8)
      ((sdData_val vtop).extractLsb' 32 8) ((sdData_val vtop).extractLsb' 40 8)
      ((sdData_val vtop).extractLsb' 48 8) ((sdData_val vtop).extractLsb' 56 8)
      hG hpc hmi0 hx2_0 hload0 rfl
      (by rw [hoff112]; omega) (by rw [hoff112]; omega) (Or.inr (by rw [hoff112]; omega))
      (by rw [hoff112]; omega)
      h112a h112b h112c h112d h112e h112f h112g h112h htick
  have hstep1 : Step c ⟨σ1, i1, c.steps+1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000835c#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80008358#64 : BitVec 64) 4 = (0x8000835c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx22_1 : σ1.regs.get? Register.x22 = some vtop := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vtop] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_0
  have hx26_1 : σ1.regs.get? Register.x26 = some vcur :=
    obs_alu_other hobs1 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_0
  have hx20_1 : σ1.regs.get? Register.x20 = some vs4j :=
    obs_alu_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_0
  have hx23_1 : σ1.regs.get? Register.x23 = some vcnt :=
    obs_alu_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_0
  have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload0
  have hfp1 : FlushPinsLoaded σ1.mem := hmem1 ▸ hfp0
  have hs56_1 : SlotHolds vsp 0x038 vwidth σ1.mem := hmem1 ▸ hs56
  have hs40_1 : SlotHolds vsp 0x028 vflags σ1.mem := hmem1 ▸ hs40
  have hs32_1 : SlotHolds vsp 0x020 vt3v σ1.mem := hmem1 ▸ hs32
  have hs48_1 : SlotHolds vsp 0x030 vs7v σ1.mem := hmem1 ▸ hs48
  have hs120_1 : SlotHolds vsp 0x078 vs0v σ1.mem := hmem1 ▸ hs120
  have hsb_1 : σ1.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem1 ▸ hsb
  -- === 835c: sd s4,104(sp) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_8000835c_fl σ1 i1 (c.steps+1) (0x8000835c#64) vmi1 vsp vs4j
      hG1 hpc1 hmi1 hx2_1 hx20_1 hload1 rfl
      (by rw [hoff104]; omega) (by rw [hoff104]; omega) (by rw [hoff104]; omega)
      (by rw [hoff104]; omega) hi1
  have hstep2 : Step ⟨σ1,i1,c.steps+1⟩ ⟨σ2,i2,c.steps+1+1⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80008360#64) := by
    have := obs_store_pc_sn4 hobs2
    rwa [show BitVec.addInt (0x8000835c#64 : BitVec 64) 4 = (0x80008360#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_sn4 hobs2
  have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
  have hx26_2 : σ2.regs.get? Register.x26 = some vcur :=
    obs_store_other_sn4 Register.x26 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_1
  have hx23_2 : σ2.regs.get? Register.x23 = some vcnt :=
    obs_store_other_sn4 Register.x23 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_1
  have hx22_2 : σ2.regs.get? Register.x22 = some vtop :=
    obs_store_other_sn4 Register.x22 hobs2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_1
  have hNP1 : (afterNextPC (afterPrelude σ1) (0x8000835c#64)).mem = σ1.mem := rfl
  have hkey104 : 0x8000b000 ≤ (vsp + sign_extend (m := 64) (0x068#12)).toNat := by
    rw [hoff104]; omega
  have hload2 : SvfprintfSliceLoaded σ2.mem := by
    rw [hmem2, hNP1]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by omega) hload1
  have hfp2 : FlushPinsLoaded σ2.mem := by
    rw [hmem2, hNP1]; exact flushPins_writeMap8_fl _ _ _ hkey104 hfp1
  have hs56_2 : SlotHolds vsp 0x038 vwidth σ2.mem := by
    rw [hmem2, hNP1]
    exact slotHolds_writeMap8 vsp 0x038 vwidth σ1.mem _ _ (by rw [hoff104, hoff56]; omega) hs56_1
  have hs40_2 : SlotHolds vsp 0x028 vflags σ2.mem := by
    rw [hmem2, hNP1]
    exact slotHolds_writeMap8 vsp 0x028 vflags σ1.mem _ _ (by rw [hoff104, hoff40]; omega) hs40_1
  have hs32_2 : SlotHolds vsp 0x020 vt3v σ2.mem := by
    rw [hmem2, hNP1]
    exact slotHolds_writeMap8 vsp 0x020 vt3v σ1.mem _ _ (by rw [hoff104, hoff32]; omega) hs32_1
  have hs48_2 : SlotHolds vsp 0x030 vs7v σ2.mem := by
    rw [hmem2, hNP1]
    exact slotHolds_writeMap8 vsp 0x030 vs7v σ1.mem _ _ (by rw [hoff104, hoff48]; omega) hs48_1
  have hsb_2 : σ2.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := by
    rw [hmem2, hNP1, getElem?_writeMap8_out _ _ _ _ (by rw [hoff104, hoff167]; omega)]
    exact hsb_1
  have hs120_2 : SlotHolds vsp 0x078 vs0v σ2.mem := by
    rw [hmem2, hNP1]
    exact slotHolds_writeMap8 vsp 0x078 vs0v σ1.mem _ _ (by rw [hoff104, hoff120]; omega) hs120_1
  -- === 80008360: ld (slot 56) ⇒ x20 := vwidth ===
  obtain ⟨hA3, hB3, hC3, hD3, hE3, hF3, hGx3, hH3⟩ := hs56_2
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80008360_fl σ2 i2 (c.steps+1+1) (0x80008360#64) vmi2 vsp
      ((sdData_val vwidth).extractLsb' 0 8) ((sdData_val vwidth).extractLsb' 8 8)
      ((sdData_val vwidth).extractLsb' 16 8) ((sdData_val vwidth).extractLsb' 24 8)
      ((sdData_val vwidth).extractLsb' 32 8) ((sdData_val vwidth).extractLsb' 40 8)
      ((sdData_val vwidth).extractLsb' 48 8) ((sdData_val vwidth).extractLsb' 56 8)
      hG2 hpc2 hmi2 hx2_2 hload2 rfl
      (by rw [hoff56]; omega) (by rw [hoff56]; omega) (Or.inr (by rw [hoff56]; omega))
      (by rw [hoff56]; omega)
      hA3 hB3 hC3 hD3 hE3 hF3 hGx3 hH3 hi2
  have hstep3 : Step ⟨σ2,i2,c.steps+1+1⟩ ⟨σ3,i3,c.steps+1+1+1⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80008364#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80008360#64 : BitVec 64) 4 = (0x80008364#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx20w_3 : σ3.regs.get? Register.x20 = some vwidth := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vwidth] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hx2_3 : σ3.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_2
  have hx26_3 : σ3.regs.get? Register.x26 = some vcur :=
    obs_alu_other hobs3 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_2
  have hx23_3 : σ3.regs.get? Register.x23 = some vcnt :=
    obs_alu_other hobs3 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_2
  have hx22_3 : σ3.regs.get? Register.x22 = some vtop :=
    obs_alu_other hobs3 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_2
  have hload3 : SvfprintfSliceLoaded σ3.mem := hmem3 ▸ hload2
  have hfp3 : FlushPinsLoaded σ3.mem := hmem3 ▸ hfp2
  have hs40_3 : SlotHolds vsp 0x028 vflags σ3.mem := hmem3 ▸ hs40_2
  have hs32_3 : SlotHolds vsp 0x020 vt3v σ3.mem := hmem3 ▸ hs32_2
  have hs48_3 : SlotHolds vsp 0x030 vs7v σ3.mem := hmem3 ▸ hs48_2
  have hs120_3 : SlotHolds vsp 0x078 vs0v σ3.mem := hmem3 ▸ hs120_2
  have hsb_3 : σ3.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem3 ▸ hsb_2
  -- === 80008364: ld (slot 40) ⇒ x6 := vflags ===
  obtain ⟨hA4, hB4, hC4, hD4, hE4, hF4, hGx4, hH4⟩ := hs40_3
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80008364_fl σ3 i3 (c.steps+1+1+1) (0x80008364#64) vmi3 vsp
      ((sdData_val vflags).extractLsb' 0 8) ((sdData_val vflags).extractLsb' 8 8)
      ((sdData_val vflags).extractLsb' 16 8) ((sdData_val vflags).extractLsb' 24 8)
      ((sdData_val vflags).extractLsb' 32 8) ((sdData_val vflags).extractLsb' 40 8)
      ((sdData_val vflags).extractLsb' 48 8) ((sdData_val vflags).extractLsb' 56 8)
      hG3 hpc3 hmi3 hx2_3 hload3 rfl
      (by rw [hoff40]; omega) (by rw [hoff40]; omega) (Or.inr (by rw [hoff40]; omega))
      (by rw [hoff40]; omega)
      hA4 hB4 hC4 hD4 hE4 hF4 hGx4 hH4 hi3
  have hstep4 : Step ⟨σ3,i3,c.steps+1+1+1⟩ ⟨σ4,i4,c.steps+1+1+1+1⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80008368#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80008364#64 : BitVec 64) 4 = (0x80008368#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx6w_4 : σ4.regs.get? Register.x6 = some vflags := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vflags] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hx2_4 : σ4.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_3
  have hx26_4 : σ4.regs.get? Register.x26 = some vcur :=
    obs_alu_other hobs4 Register.x26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx26_3
  have hx23_4 : σ4.regs.get? Register.x23 = some vcnt :=
    obs_alu_other hobs4 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_3
  have hx22_4 : σ4.regs.get? Register.x22 = some vtop :=
    obs_alu_other hobs4 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_3
  have hx20w_4 : σ4.regs.get? Register.x20 = some vwidth :=
    obs_alu_other hobs4 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_3
  have hload4 : SvfprintfSliceLoaded σ4.mem := hmem4 ▸ hload3
  have hfp4 : FlushPinsLoaded σ4.mem := hmem4 ▸ hfp3
  have hs32_4 : SlotHolds vsp 0x020 vt3v σ4.mem := hmem4 ▸ hs32_3
  have hs48_4 : SlotHolds vsp 0x030 vs7v σ4.mem := hmem4 ▸ hs48_3
  have hs120_4 : SlotHolds vsp 0x078 vs0v σ4.mem := hmem4 ▸ hs120_3
  have hsb_4 : σ4.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem4 ▸ hsb_3
  -- === 8368: subw s6,s6,s10 ⇒ x22 := len ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80008368_fl σ4 i4 (c.steps+1+1+1+1) (0x80008368#64) vmi4 vtop vcur
      hG4 hpc4 hmi4 hx22_4 hx26_4 hload4 rfl hi4
  have hstep5 : Step ⟨σ4,i4,c.steps+1+1+1+1⟩ ⟨σ5,i5,c.steps+1+1+1+1+1⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000836c#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80008368#64 : BitVec 64) 4 = (0x8000836c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx22_5 : σ5.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hx2_5 : σ5.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_4
  have hx23_5 : σ5.regs.get? Register.x23 = some vcnt :=
    obs_alu_other hobs5 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_4
  have hx20w_5 : σ5.regs.get? Register.x20 = some vwidth :=
    obs_alu_other hobs5 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_4
  have hx6w_5 : σ5.regs.get? Register.x6 = some vflags :=
    obs_alu_other hobs5 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_4
  have hload5 : SvfprintfSliceLoaded σ5.mem := hmem5 ▸ hload4
  have hfp5 : FlushPinsLoaded σ5.mem := hmem5 ▸ hfp4
  have hs32_5 : SlotHolds vsp 0x020 vt3v σ5.mem := hmem5 ▸ hs32_4
  have hs48_5 : SlotHolds vsp 0x030 vs7v σ5.mem := hmem5 ▸ hs48_4
  have hs120_5 : SlotHolds vsp 0x078 vs0v σ5.mem := hmem5 ▸ hs120_4
  have hsb_5 : σ5.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem5 ▸ hsb_4
  -- === 836c: sd s7,40(sp) ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_8000836c_fl σ5 i5 (c.steps+1+1+1+1+1) (0x8000836c#64) vmi5 vsp vcnt
      hG5 hpc5 hmi5 hx2_5 hx23_5 hload5 rfl
      (by rw [hoff40]; omega) (by rw [hoff40]; omega) (by rw [hoff40]; omega)
      (by rw [hoff40]; omega) hi5
  have hstep6 : Step ⟨σ5,i5,c.steps+1+1+1+1+1⟩ ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80008370#64) := by
    have := obs_store_pc_sn4 hobs6
    rwa [show BitVec.addInt (0x8000836c#64 : BitVec 64) 4 = (0x80008370#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret_sn4 hobs6
  have hx2_6 : σ6.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_5
  have hx20w_6 : σ6.regs.get? Register.x20 = some vwidth :=
    obs_store_other_sn4 Register.x20 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_5
  have hx6w_6 : σ6.regs.get? Register.x6 = some vflags :=
    obs_store_other_sn4 Register.x6 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_5
  have hx22_6 : σ6.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_store_other_sn4 Register.x22 hobs6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_5
  have hNP5 : (afterNextPC (afterPrelude σ5) (0x8000836c#64)).mem = σ5.mem := rfl
  have hload6 : SvfprintfSliceLoaded σ6.mem := by
    rw [hmem6, hNP5]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff40]; omega) hload5
  have hfp6 : FlushPinsLoaded σ6.mem := by
    rw [hmem6, hNP5]; exact flushPins_writeMap8_fl _ _ _ (by rw [hoff40]; omega) hfp5
  have hs32_6 : SlotHolds vsp 0x020 vt3v σ6.mem := by
    rw [hmem6, hNP5]
    exact slotHolds_writeMap8 vsp 0x020 vt3v σ5.mem _ _ (by rw [hoff40, hoff32]; omega) hs32_5
  have hs48_6 : SlotHolds vsp 0x030 vs7v σ6.mem := by
    rw [hmem6, hNP5]
    exact slotHolds_writeMap8 vsp 0x030 vs7v σ5.mem _ _ (by rw [hoff40, hoff48]; omega) hs48_5
  have hs120_6 : SlotHolds vsp 0x078 vs0v σ6.mem := by
    rw [hmem6, hNP5]
    exact slotHolds_writeMap8 vsp 0x078 vs0v σ5.mem _ _ (by rw [hoff40, hoff120]; omega) hs120_5
  have hsb_6 : σ6.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := by
    rw [hmem6, hNP5, getElem?_writeMap8_out _ _ _ _ (by rw [hoff40, hoff167]; omega)]
    exact hsb_5
  -- === 80008370: ld (slot 32) ⇒ x28 := vt3v ===
  obtain ⟨hA7, hB7, hC7, hD7, hE7, hF7, hGx7, hH7⟩ := hs32_6
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80008370_fl σ6 i6 (c.steps+1+1+1+1+1+1) (0x80008370#64) vmi6 vsp
      ((sdData_val vt3v).extractLsb' 0 8) ((sdData_val vt3v).extractLsb' 8 8)
      ((sdData_val vt3v).extractLsb' 16 8) ((sdData_val vt3v).extractLsb' 24 8)
      ((sdData_val vt3v).extractLsb' 32 8) ((sdData_val vt3v).extractLsb' 40 8)
      ((sdData_val vt3v).extractLsb' 48 8) ((sdData_val vt3v).extractLsb' 56 8)
      hG6 hpc6 hmi6 hx2_6 hload6 rfl
      (by rw [hoff32]; omega) (by rw [hoff32]; omega) (Or.inr (by rw [hoff32]; omega))
      (by rw [hoff32]; omega)
      hA7 hB7 hC7 hD7 hE7 hF7 hGx7 hH7 hi6
  have hstep7 : Step ⟨σ6,i6,c.steps+1+1+1+1+1+1⟩ ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80008374#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80008370#64 : BitVec 64) 4 = (0x80008374#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx28w_7 : σ7.regs.get? Register.x28 = some vt3v := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vt3v] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hx2_7 : σ7.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_6
  have hx20w_7 : σ7.regs.get? Register.x20 = some vwidth :=
    obs_alu_other hobs7 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_6
  have hx6w_7 : σ7.regs.get? Register.x6 = some vflags :=
    obs_alu_other hobs7 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_6
  have hx22_7 : σ7.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_other hobs7 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_6
  have hload7 : SvfprintfSliceLoaded σ7.mem := hmem7 ▸ hload6
  have hfp7 : FlushPinsLoaded σ7.mem := hmem7 ▸ hfp6
  have hs48_7 : SlotHolds vsp 0x030 vs7v σ7.mem := hmem7 ▸ hs48_6
  have hs120_7 : SlotHolds vsp 0x078 vs0v σ7.mem := hmem7 ▸ hs120_6
  have hsb_7 : σ7.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem7 ▸ hsb_6
  -- === 80008374: ld (slot 48) ⇒ x23 := vs7v ===
  obtain ⟨hA8, hB8, hC8, hD8, hE8, hF8, hGx8, hH8⟩ := hs48_7
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80008374_fl σ7 i7 (c.steps+1+1+1+1+1+1+1) (0x80008374#64) vmi7 vsp
      ((sdData_val vs7v).extractLsb' 0 8) ((sdData_val vs7v).extractLsb' 8 8)
      ((sdData_val vs7v).extractLsb' 16 8) ((sdData_val vs7v).extractLsb' 24 8)
      ((sdData_val vs7v).extractLsb' 32 8) ((sdData_val vs7v).extractLsb' 40 8)
      ((sdData_val vs7v).extractLsb' 48 8) ((sdData_val vs7v).extractLsb' 56 8)
      hG7 hpc7 hmi7 hx2_7 hload7 rfl
      (by rw [hoff48]; omega) (by rw [hoff48]; omega) (Or.inr (by rw [hoff48]; omega))
      (by rw [hoff48]; omega)
      hA8 hB8 hC8 hD8 hE8 hF8 hGx8 hH8 hi7
  have hstep8 : Step ⟨σ7,i7,c.steps+1+1+1+1+1+1+1⟩ ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80008378#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80008374#64 : BitVec 64) 4 = (0x80008378#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx23w_8 : σ8.regs.get? Register.x23 = some vs7v := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vs7v] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hx2_8 : σ8.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_7
  have hx20w_8 : σ8.regs.get? Register.x20 = some vwidth :=
    obs_alu_other hobs8 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_7
  have hx6w_8 : σ8.regs.get? Register.x6 = some vflags :=
    obs_alu_other hobs8 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_7
  have hx22_8 : σ8.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_other hobs8 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_7
  have hx28w_8 : σ8.regs.get? Register.x28 = some vt3v :=
    obs_alu_other hobs8 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_7
  have hload8 : SvfprintfSliceLoaded σ8.mem := hmem8 ▸ hload7
  have hfp8 : FlushPinsLoaded σ8.mem := hmem8 ▸ hfp7
  have hs120_8 : SlotHolds vsp 0x078 vs0v σ8.mem := hmem8 ▸ hs120_7
  have hsb_8 : σ8.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem8 ▸ hsb_7
  -- === 80008378: ld (slot 120) ⇒ x8 := vs0v ===
  obtain ⟨hA9, hB9, hC9, hD9, hE9, hF9, hGx9, hH9⟩ := hs120_8
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80008378_fl σ8 i8 (c.steps+1+1+1+1+1+1+1+1) (0x80008378#64) vmi8 vsp
      ((sdData_val vs0v).extractLsb' 0 8) ((sdData_val vs0v).extractLsb' 8 8)
      ((sdData_val vs0v).extractLsb' 16 8) ((sdData_val vs0v).extractLsb' 24 8)
      ((sdData_val vs0v).extractLsb' 32 8) ((sdData_val vs0v).extractLsb' 40 8)
      ((sdData_val vs0v).extractLsb' 48 8) ((sdData_val vs0v).extractLsb' 56 8)
      hG8 hpc8 hmi8 hx2_8 hload8 rfl
      (by rw [hoff120]; omega) (by rw [hoff120]; omega) (Or.inr (by rw [hoff120]; omega))
      (by rw [hoff120]; omega)
      hA9 hB9 hC9 hD9 hE9 hF9 hGx9 hH9 hi8
  have hstep9 : Step ⟨σ8,i8,c.steps+1+1+1+1+1+1+1+1⟩ ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x8000837c#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x80008378#64 : BitVec 64) 4 = (0x8000837c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx8w_9 : σ9.regs.get? Register.x8 = some vs0v := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ve_sext_reassemble vs0v] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hx2_9 : σ9.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_8
  have hx20w_9 : σ9.regs.get? Register.x20 = some vwidth :=
    obs_alu_other hobs9 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_8
  have hx6w_9 : σ9.regs.get? Register.x6 = some vflags :=
    obs_alu_other hobs9 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_8
  have hx22_9 : σ9.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_other hobs9 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_8
  have hx28w_9 : σ9.regs.get? Register.x28 = some vt3v :=
    obs_alu_other hobs9 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_8
  have hx23w_9 : σ9.regs.get? Register.x23 = some vs7v :=
    obs_alu_other hobs9 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_8
  have hload9 : SvfprintfSliceLoaded σ9.mem := hmem9 ▸ hload8
  have hfp9 : FlushPinsLoaded σ9.mem := hmem9 ▸ hfp8
  have hsb_9 : σ9.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem9 ▸ hsb_8
  -- === 837c: addiw a6,s4,0 ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_8000837c_fl σ9 i9 (c.steps+1+1+1+1+1+1+1+1+1) (0x8000837c#64) vmi9 vwidth
      hG9 hpc9 hmi9 hx20w_9 hload9 rfl hi9
  have hstep10 : Step ⟨σ9,i9,c.steps+1+1+1+1+1+1+1+1+1⟩ ⟨σ10,i10,c.steps+1+1+1+1+1+1+1+1+1+1⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80008380#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x8000837c#64 : BitVec 64) 4 = (0x80008380#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hx2_10 : σ10.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_9
  have hx20w_10 : σ10.regs.get? Register.x20 = some vwidth :=
    obs_alu_other hobs10 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_9
  have hx6w_10 : σ10.regs.get? Register.x6 = some vflags :=
    obs_alu_other hobs10 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_9
  have hx22_10 : σ10.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_other hobs10 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_9
  have hx28w_10 : σ10.regs.get? Register.x28 = some vt3v :=
    obs_alu_other hobs10 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_9
  have hx23w_10 : σ10.regs.get? Register.x23 = some vs7v :=
    obs_alu_other hobs10 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_9
  have hx8w_10 : σ10.regs.get? Register.x8 = some vs0v :=
    obs_alu_other hobs10 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_9
  have hload10 : SvfprintfSliceLoaded σ10.mem := hmem10 ▸ hload9
  have hfp10 : FlushPinsLoaded σ10.mem := hmem10 ▸ hfp9
  have hsb_10 : σ10.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem10 ▸ hsb_9
  -- === 8380: bge s4,s6 NOT taken (width < len) ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80008380_nottaken_fl σ10 i10 (c.steps+1+1+1+1+1+1+1+1+1+1) (0x80008380#64) vmi10 vwidth (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
      hG10 hpc10 hmi10 hx20w_10 hx22_10 hload10 rfl hwlt hi10
  have hstep11 : Step ⟨σ10,i10,c.steps+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ11,i11,c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80008384#64) := by
    have := obs_bnottaken_pc hobs11
    rwa [show BitVec.addInt (0x80008380#64 : BitVec 64) 4 = (0x80008384#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_bnottaken_minstret hobs11
  have hx2_11 : σ11.regs.get? Register.x2 = some vsp :=
    obs_bnottaken_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_10
  have hx20w_11 : σ11.regs.get? Register.x20 = some vwidth :=
    obs_bnottaken_other hobs11 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_10
  have hx6w_11 : σ11.regs.get? Register.x6 = some vflags :=
    obs_bnottaken_other hobs11 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_10
  have hx22_11 : σ11.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_bnottaken_other hobs11 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_10
  have hx28w_11 : σ11.regs.get? Register.x28 = some vt3v :=
    obs_bnottaken_other hobs11 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_10
  have hx23w_11 : σ11.regs.get? Register.x23 = some vs7v :=
    obs_bnottaken_other hobs11 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_10
  have hx8w_11 : σ11.regs.get? Register.x8 = some vs0v :=
    obs_bnottaken_other hobs11 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_10
  have hload11 : SvfprintfSliceLoaded σ11.mem := hmem11 ▸ hload10
  have hfp11 : FlushPinsLoaded σ11.mem := hmem11 ▸ hfp10
  have hsb_11 : σ11.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem11 ▸ hsb_10
  -- === 8384: addiw a6,s6,0 ⇒ a6 := len ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80008384_fl σ11 i11 (c.steps+1+1+1+1+1+1+1+1+1+1+1) (0x80008384#64) vmi11 (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
      hG11 hpc11 hmi11 hx22_11 hload11 rfl hi11
  have hstep12 : Step ⟨σ11,i11,c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ12,i12,c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x80008388#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80008384#64 : BitVec 64) 4 = (0x80008388#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx16_12 : σ12.regs.get? Register.x16 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))), extract_sext32_fl
      ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))] at this
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hx2_12 : σ12.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_11
  have hx20w_12 : σ12.regs.get? Register.x20 = some vwidth :=
    obs_alu_other hobs12 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_11
  have hx6w_12 : σ12.regs.get? Register.x6 = some vflags :=
    obs_alu_other hobs12 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_11
  have hx22_12 : σ12.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_other hobs12 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_11
  have hx28w_12 : σ12.regs.get? Register.x28 = some vt3v :=
    obs_alu_other hobs12 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_11
  have hx23w_12 : σ12.regs.get? Register.x23 = some vs7v :=
    obs_alu_other hobs12 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_11
  have hx8w_12 : σ12.regs.get? Register.x8 = some vs0v :=
    obs_alu_other hobs12 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_11
  have hload12 : SvfprintfSliceLoaded σ12.mem := hmem12 ▸ hload11
  have hfp12 : FlushPinsLoaded σ12.mem := hmem12 ▸ hfp11
  have hsb_12 : σ12.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some sb := hmem12 ▸ hsb_11
  -- === 8388: lbu t5,167(sp) ⇒ t5 := sign byte ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80008388_fl σ12 i12 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008388#64) vmi12 vsp sb
      hG12 hpc12 hmi12 hx2_12 hload12 rfl
      (by rw [hoff167]; omega) (by rw [hoff167]; omega) (Or.inr (by rw [hoff167]; omega))
      hsb_12 hi12
  have hstep13 : Step ⟨σ12,i12,c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ13,i13,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x8000838c#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x80008388#64 : BitVec 64) 4 = (0x8000838c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx30_13 : σ13.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hx2_13 : σ13.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_12
  have hx20w_13 : σ13.regs.get? Register.x20 = some vwidth :=
    obs_alu_other hobs13 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_12
  have hx6w_13 : σ13.regs.get? Register.x6 = some vflags :=
    obs_alu_other hobs13 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_12
  have hx16_13 : σ13.regs.get? Register.x16 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_other hobs13 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_12
  have hx22_13 : σ13.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_other hobs13 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_12
  have hx28w_13 : σ13.regs.get? Register.x28 = some vt3v :=
    obs_alu_other hobs13 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_12
  have hx23w_13 : σ13.regs.get? Register.x23 = some vs7v :=
    obs_alu_other hobs13 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_12
  have hx8w_13 : σ13.regs.get? Register.x8 = some vs0v :=
    obs_alu_other hobs13 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_12
  have hload13 : SvfprintfSliceLoaded σ13.mem := hmem13 ▸ hload12
  have hfp13 : FlushPinsLoaded σ13.mem := hmem13 ▸ hfp12
  -- === 838c: li t6,0 ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_8000838c_fl σ13 i13 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000838c#64) vmi13 hG13 hpc13 hmi13 hload13 rfl hi13
  have hstep14 : Step ⟨σ13,i13,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ14,i14,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x80008390#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x8000838c#64 : BitVec 64) 4 = (0x80008390#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx31_14 : σ14.regs.get? Register.x31 = some (0#64) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0_sn3 (0#64)] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hx2_14 : σ14.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_13
  have hx20w_14 : σ14.regs.get? Register.x20 = some vwidth :=
    obs_alu_other hobs14 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_13
  have hx6w_14 : σ14.regs.get? Register.x6 = some vflags :=
    obs_alu_other hobs14 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_13
  have hx16_14 : σ14.regs.get? Register.x16 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_other hobs14 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_13
  have hx22_14 : σ14.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_other hobs14 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_13
  have hx28w_14 : σ14.regs.get? Register.x28 = some vt3v :=
    obs_alu_other hobs14 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_13
  have hx23w_14 : σ14.regs.get? Register.x23 = some vs7v :=
    obs_alu_other hobs14 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_13
  have hx8w_14 : σ14.regs.get? Register.x8 = some vs0v :=
    obs_alu_other hobs14 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_13
  have hx30_14 : σ14.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_alu_other hobs14 Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_13
  have hload14 : SvfprintfSliceLoaded σ14.mem := hmem14 ▸ hload13
  have hfp14 : FlushPinsLoaded σ14.mem := hmem14 ▸ hfp13
  -- === 8390: sd zero,32(sp) ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80008390_fl σ14 i14 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008390#64) vmi14 vsp
      hG14 hpc14 hmi14 hx2_14 hload14 rfl
      (by rw [hoff32]; omega) (by rw [hoff32]; omega) (by rw [hoff32]; omega)
      (by rw [hoff32]; omega) hi14
  have hstep15 : Step ⟨σ14,i14,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ15,i15,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80008394#64) := by
    have := obs_store_pc_sn4 hobs15
    rwa [show BitVec.addInt (0x80008390#64 : BitVec 64) 4 = (0x80008394#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_store_minstret_sn4 hobs15
  have hx2_15 : σ15.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_14
  have hx20w_15 : σ15.regs.get? Register.x20 = some vwidth :=
    obs_store_other_sn4 Register.x20 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_14
  have hx6w_15 : σ15.regs.get? Register.x6 = some vflags :=
    obs_store_other_sn4 Register.x6 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_14
  have hx16_15 : σ15.regs.get? Register.x16 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_store_other_sn4 Register.x16 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_14
  have hx22_15 : σ15.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_store_other_sn4 Register.x22 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_14
  have hx28w_15 : σ15.regs.get? Register.x28 = some vt3v :=
    obs_store_other_sn4 Register.x28 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_14
  have hx23w_15 : σ15.regs.get? Register.x23 = some vs7v :=
    obs_store_other_sn4 Register.x23 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_14
  have hx8w_15 : σ15.regs.get? Register.x8 = some vs0v :=
    obs_store_other_sn4 Register.x8 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_14
  have hx30_15 : σ15.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_store_other_sn4 Register.x30 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_14
  have hx31_15 : σ15.regs.get? Register.x31 = some (0#64) :=
    obs_store_other_sn4 Register.x31 hobs15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx31_14
  have hNP14 : (afterNextPC (afterPrelude σ14) (0x80008390#64)).mem = σ14.mem := rfl
  have hload15 : SvfprintfSliceLoaded σ15.mem := by
    rw [hmem15, hNP14]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff32]; omega) hload14
  have hfp15 : FlushPinsLoaded σ15.mem := by
    rw [hmem15, hNP14]; exact flushPins_writeMap8_fl _ _ _ (by rw [hoff32]; omega) hfp14
  -- === 80008394: j 0x8000812c ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80008394_fl σ15 i15 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008394#64) vmi15
      hG15 hpc15 hmi15 hload15 rfl (by decide) hi15
  have hstep16 : Step ⟨σ15,i15,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ16,i16,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x8000812c#64) := by
    have := obs_jx0_pc_sn5 hobs16
    rwa [show (0x80008394#64 : BitVec 64) + sign_extend (m := 64) (0x1ffd98#21)
      = (0x8000812c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := hG16.minstret
  have hx2_16 : σ16.regs.get? Register.x2 = some vsp :=
    obs_jr_other hobs16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_15
  have hx20w_16 : σ16.regs.get? Register.x20 = some vwidth :=
    obs_jr_other hobs16 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_15
  have hx6w_16 : σ16.regs.get? Register.x6 = some vflags :=
    obs_jr_other hobs16 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_15
  have hx16_16 : σ16.regs.get? Register.x16 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_jr_other hobs16 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_15
  have hx22_16 : σ16.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_jr_other hobs16 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_15
  have hx28w_16 : σ16.regs.get? Register.x28 = some vt3v :=
    obs_jr_other hobs16 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_15
  have hx23w_16 : σ16.regs.get? Register.x23 = some vs7v :=
    obs_jr_other hobs16 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_15
  have hx8w_16 : σ16.regs.get? Register.x8 = some vs0v :=
    obs_jr_other hobs16 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_15
  have hx30_16 : σ16.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_jr_other hobs16 Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_15
  have hx31_16 : σ16.regs.get? Register.x31 = some (0#64) :=
    obs_jr_other hobs16 Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx31_15
  have hload16 : SvfprintfSliceLoaded σ16.mem := hmem16 ▸ hload15
  have hfp16 : FlushPinsLoaded σ16.mem := hmem16 ▸ hfp15
  -- === 812c: beq t5,zero NOT taken ===
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_8000812c_nottaken_fl σ16 i16 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000812c#64) vmi16 (zero_extend (m := 64) sb)
      hG16 hpc16 hmi16 hx30_16 hload16 rfl hsbne hi16
  have hstep17 : Step ⟨σ16,i16,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ17,i17,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x80008130#64) := by
    have := obs_bnottaken_pc hobs17
    rwa [show BitVec.addInt (0x8000812c#64 : BitVec 64) 4 = (0x80008130#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi17, hmi17⟩ := obs_bnottaken_minstret hobs17
  have hx2_17 : σ17.regs.get? Register.x2 = some vsp :=
    obs_bnottaken_other hobs17 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_16
  have hx20w_17 : σ17.regs.get? Register.x20 = some vwidth :=
    obs_bnottaken_other hobs17 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_16
  have hx6w_17 : σ17.regs.get? Register.x6 = some vflags :=
    obs_bnottaken_other hobs17 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_16
  have hx16_17 : σ17.regs.get? Register.x16 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_bnottaken_other hobs17 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16_16
  have hx22_17 : σ17.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_bnottaken_other hobs17 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_16
  have hx28w_17 : σ17.regs.get? Register.x28 = some vt3v :=
    obs_bnottaken_other hobs17 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_16
  have hx23w_17 : σ17.regs.get? Register.x23 = some vs7v :=
    obs_bnottaken_other hobs17 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_16
  have hx8w_17 : σ17.regs.get? Register.x8 = some vs0v :=
    obs_bnottaken_other hobs17 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_16
  have hx30_17 : σ17.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_bnottaken_other hobs17 Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_16
  have hx31_17 : σ17.regs.get? Register.x31 = some (0#64) :=
    obs_bnottaken_other hobs17 Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx31_16
  have hload17 : SvfprintfSliceLoaded σ17.mem := hmem17 ▸ hload16
  have hfp17 : FlushPinsLoaded σ17.mem := hmem17 ▸ hfp16
  -- === 8130: addiw a6,a6,1 ⇒ a6 := len + 1 (sign byte) ===
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_80008130_fl σ17 i17 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008130#64) vmi17 (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
      hG17 hpc17 hmi17 hx16_17 hload17 rfl hi17
  have hstep18 : Step ⟨σ17,i17,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ18,i18,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x80008134#64) := by
    have := obs_alu_pc hobs18
    rwa [show BitVec.addInt (0x80008130#64 : BitVec 64) 4 = (0x80008134#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx16n_18 : σ18.regs.get? Register.x16 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
          + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_alu_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi18, hmi18⟩ := obs_alu_minstret hobs18
  have hx2_18 : σ18.regs.get? Register.x2 = some vsp :=
    obs_alu_other hobs18 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_17
  have hx20w_18 : σ18.regs.get? Register.x20 = some vwidth :=
    obs_alu_other hobs18 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_17
  have hx6w_18 : σ18.regs.get? Register.x6 = some vflags :=
    obs_alu_other hobs18 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_17
  have hx22_18 : σ18.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_alu_other hobs18 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_17
  have hx28w_18 : σ18.regs.get? Register.x28 = some vt3v :=
    obs_alu_other hobs18 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_17
  have hx23w_18 : σ18.regs.get? Register.x23 = some vs7v :=
    obs_alu_other hobs18 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_17
  have hx8w_18 : σ18.regs.get? Register.x8 = some vs0v :=
    obs_alu_other hobs18 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_17
  have hx30_18 : σ18.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_alu_other hobs18 Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_17
  have hx31_18 : σ18.regs.get? Register.x31 = some (0#64) :=
    obs_alu_other hobs18 Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx31_17
  have hload18 : SvfprintfSliceLoaded σ18.mem := hmem18 ▸ hload17
  have hfp18 : FlushPinsLoaded σ18.mem := hmem18 ▸ hfp17
  -- === 80008134: j 0x80008088 ===
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_80008134_fl σ18 i18 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008134#64) vmi18
      hG18 hpc18 hmi18 hload18 rfl (by decide) hi18
  have hstep19 : Step ⟨σ18,i18,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ19,i19,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs19
  have hpc19 : σ19.regs.get? Register.PC = some (0x80008088#64) := by
    have := obs_jx0_pc_sn5 hobs19
    rwa [show (0x80008134#64 : BitVec 64) + sign_extend (m := 64) (0x1fff54#21)
      = (0x80008088#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi19, hmi19⟩ := hG19.minstret
  have hx2_19 : σ19.regs.get? Register.x2 = some vsp :=
    obs_jr_other hobs19 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_18
  have hx20w_19 : σ19.regs.get? Register.x20 = some vwidth :=
    obs_jr_other hobs19 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_18
  have hx6w_19 : σ19.regs.get? Register.x6 = some vflags :=
    obs_jr_other hobs19 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_18
  have hx22_19 : σ19.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_jr_other hobs19 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_18
  have hx28w_19 : σ19.regs.get? Register.x28 = some vt3v :=
    obs_jr_other hobs19 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_18
  have hx23w_19 : σ19.regs.get? Register.x23 = some vs7v :=
    obs_jr_other hobs19 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_18
  have hx8w_19 : σ19.regs.get? Register.x8 = some vs0v :=
    obs_jr_other hobs19 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_18
  have hx30_19 : σ19.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_jr_other hobs19 Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_18
  have hx31_19 : σ19.regs.get? Register.x31 = some (0#64) :=
    obs_jr_other hobs19 Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx31_18
  have hx16n_19 : σ19.regs.get? Register.x16 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
          + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_jr_other hobs19 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16n_18
  have hload19 : SvfprintfSliceLoaded σ19.mem := hmem19 ▸ hload18
  have hfp19 : FlushPinsLoaded σ19.mem := hmem19 ▸ hfp18
  -- === 8088: bne t6,zero NOT taken ===
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_80008088_nottaken_fl σ19 i19 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x80008088#64) vmi19 (0#64)
      hG19 hpc19 hmi19 hx31_19 hload19 rfl (by decide) hi19
  have hstep20 : Step ⟨σ19,i19,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ20,i20,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs20
  have hpc20 : σ20.regs.get? Register.PC = some (0x8000808c#64) := by
    have := obs_bnottaken_pc hobs20
    rwa [show BitVec.addInt (0x80008088#64 : BitVec 64) 4 = (0x8000808c#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi20, hmi20⟩ := obs_bnottaken_minstret hobs20
  have hx2_20 : σ20.regs.get? Register.x2 = some vsp :=
    obs_bnottaken_other hobs20 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_19
  have hx20w_20 : σ20.regs.get? Register.x20 = some vwidth :=
    obs_bnottaken_other hobs20 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_19
  have hx6w_20 : σ20.regs.get? Register.x6 = some vflags :=
    obs_bnottaken_other hobs20 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_19
  have hx22_20 : σ20.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_bnottaken_other hobs20 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_19
  have hx28w_20 : σ20.regs.get? Register.x28 = some vt3v :=
    obs_bnottaken_other hobs20 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_19
  have hx23w_20 : σ20.regs.get? Register.x23 = some vs7v :=
    obs_bnottaken_other hobs20 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_19
  have hx8w_20 : σ20.regs.get? Register.x8 = some vs0v :=
    obs_bnottaken_other hobs20 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_19
  have hx30_20 : σ20.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_bnottaken_other hobs20 Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_19
  have hx31_20 : σ20.regs.get? Register.x31 = some (0#64) :=
    obs_bnottaken_other hobs20 Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx31_19
  have hx16n_20 : σ20.regs.get? Register.x16 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
          + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_bnottaken_other hobs20 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16n_19
  have hload20 : SvfprintfSliceLoaded σ20.mem := hmem20 ▸ hload19
  have hfp20 : FlushPinsLoaded σ20.mem := hmem20 ▸ hfp19
  -- === 8000808c: j 0x8000a830 ===
  obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
    site_8000808c_fl σ20 i20 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000808c#64) vmi20
      hG20 hpc20 hmi20 hload20 rfl (by decide) hi20
  have hstep21 : Step ⟨σ20,i20,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ21,i21,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs21
  have hpc21 : σ21.regs.get? Register.PC = some (0x8000a830#64) := by
    have := obs_jx0_pc_sn5 hobs21
    rwa [show (0x8000808c#64 : BitVec 64) + sign_extend (m := 64) (0x0027a4#21)
      = (0x8000a830#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi21, hmi21⟩ := hG21.minstret
  have hx2_21 : σ21.regs.get? Register.x2 = some vsp :=
    obs_jr_other hobs21 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_20
  have hx20w_21 : σ21.regs.get? Register.x20 = some vwidth :=
    obs_jr_other hobs21 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_20
  have hx6w_21 : σ21.regs.get? Register.x6 = some vflags :=
    obs_jr_other hobs21 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_20
  have hx22_21 : σ21.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_jr_other hobs21 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_20
  have hx28w_21 : σ21.regs.get? Register.x28 = some vt3v :=
    obs_jr_other hobs21 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_20
  have hx23w_21 : σ21.regs.get? Register.x23 = some vs7v :=
    obs_jr_other hobs21 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_20
  have hx8w_21 : σ21.regs.get? Register.x8 = some vs0v :=
    obs_jr_other hobs21 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_20
  have hx30_21 : σ21.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_jr_other hobs21 Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_20
  have hx31_21 : σ21.regs.get? Register.x31 = some (0#64) :=
    obs_jr_other hobs21 Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx31_20
  have hx16n_21 : σ21.regs.get? Register.x16 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
          + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_jr_other hobs21 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16n_20
  have hload21 : SvfprintfSliceLoaded σ21.mem := hmem21 ▸ hload20
  have hfp21 : FlushPinsLoaded σ21.mem := hmem21 ▸ hfp20
  -- === 8000a830: sd zero,56(sp) ===
  obtain ⟨σ22, i22, hs22, hi22, hG22, hmem22, hobs22⟩ :=
    site_8000a830_fl σ21 i21 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000a830#64) vmi21 vsp
      hG21 hpc21 hmi21 hx2_21 hfp21 rfl
      (by rw [hoff56]; omega) (by rw [hoff56]; omega) (by rw [hoff56]; omega)
      (by rw [hoff56]; omega) hi21
  have hstep22 : Step ⟨σ21,i21,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ22,i22,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs22
  have hpc22 : σ22.regs.get? Register.PC = some (0x8000a834#64) := by
    have := obs_store_pc_sn4 hobs22
    rwa [show BitVec.addInt (0x8000a830#64 : BitVec 64) 4 = (0x8000a834#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi22, hmi22⟩ := obs_store_minstret_sn4 hobs22
  have hx2_22 : σ22.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_21
  have hx20w_22 : σ22.regs.get? Register.x20 = some vwidth :=
    obs_store_other_sn4 Register.x20 hobs22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_21
  have hx6w_22 : σ22.regs.get? Register.x6 = some vflags :=
    obs_store_other_sn4 Register.x6 hobs22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_21
  have hx22_22 : σ22.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_store_other_sn4 Register.x22 hobs22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_21
  have hx28w_22 : σ22.regs.get? Register.x28 = some vt3v :=
    obs_store_other_sn4 Register.x28 hobs22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_21
  have hx23w_22 : σ22.regs.get? Register.x23 = some vs7v :=
    obs_store_other_sn4 Register.x23 hobs22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_21
  have hx8w_22 : σ22.regs.get? Register.x8 = some vs0v :=
    obs_store_other_sn4 Register.x8 hobs22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_21
  have hx30_22 : σ22.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_store_other_sn4 Register.x30 hobs22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_21
  have hx31_22 : σ22.regs.get? Register.x31 = some (0#64) :=
    obs_store_other_sn4 Register.x31 hobs22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx31_21
  have hx16n_22 : σ22.regs.get? Register.x16 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
          + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x16 hobs22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16n_21
  have hNP21b : (afterNextPC (afterPrelude σ21) (0x8000a830#64)).mem = σ21.mem := rfl
  have hload22 : SvfprintfSliceLoaded σ22.mem := by
    rw [hmem22, hNP21b]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff56]; omega) hload21
  have hfp22 : FlushPinsLoaded σ22.mem := by
    rw [hmem22, hNP21b]; exact flushPins_writeMap8_fl _ _ _ (by rw [hoff56]; omega) hfp21
  -- === 8000a834: sd zero,48(sp) ===
  obtain ⟨σ23, i23, hs23, hi23, hG23, hmem23, hobs23⟩ :=
    site_8000a834_fl σ22 i22 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000a834#64) vmi22 vsp
      hG22 hpc22 hmi22 hx2_22 hfp22 rfl
      (by rw [hoff48]; omega) (by rw [hoff48]; omega) (by rw [hoff48]; omega)
      (by rw [hoff48]; omega) hi22
  have hstep23 : Step ⟨σ22,i22,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ23,i23,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs23
  have hpc23 : σ23.regs.get? Register.PC = some (0x8000a838#64) := by
    have := obs_store_pc_sn4 hobs23
    rwa [show BitVec.addInt (0x8000a834#64 : BitVec 64) 4 = (0x8000a838#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi23, hmi23⟩ := obs_store_minstret_sn4 hobs23
  have hx2_23 : σ23.regs.get? Register.x2 = some vsp :=
    obs_store_other_sn4 Register.x2 hobs23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_22
  have hx20w_23 : σ23.regs.get? Register.x20 = some vwidth :=
    obs_store_other_sn4 Register.x20 hobs23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_22
  have hx6w_23 : σ23.regs.get? Register.x6 = some vflags :=
    obs_store_other_sn4 Register.x6 hobs23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_22
  have hx22_23 : σ23.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_store_other_sn4 Register.x22 hobs23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_22
  have hx28w_23 : σ23.regs.get? Register.x28 = some vt3v :=
    obs_store_other_sn4 Register.x28 hobs23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_22
  have hx23w_23 : σ23.regs.get? Register.x23 = some vs7v :=
    obs_store_other_sn4 Register.x23 hobs23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_22
  have hx8w_23 : σ23.regs.get? Register.x8 = some vs0v :=
    obs_store_other_sn4 Register.x8 hobs23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_22
  have hx30_23 : σ23.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_store_other_sn4 Register.x30 hobs23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_22
  have hx31_23 : σ23.regs.get? Register.x31 = some (0#64) :=
    obs_store_other_sn4 Register.x31 hobs23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx31_22
  have hx16n_23 : σ23.regs.get? Register.x16 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
          + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_store_other_sn4 Register.x16 hobs23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16n_22
  have hNP22b : (afterNextPC (afterPrelude σ22) (0x8000a834#64)).mem = σ22.mem := rfl
  have hload23 : SvfprintfSliceLoaded σ23.mem := by
    rw [hmem23, hNP22b]; exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff48]; omega) hload22
  have hfp23 : FlushPinsLoaded σ23.mem := by
    rw [hmem23, hNP22b]; exact flushPins_writeMap8_fl _ _ _ (by rw [hoff48]; omega) hfp22
  -- === 8000a838: j 0x8000782c ===
  obtain ⟨σ24, i24, hs24, hi24, hG24, hmem24, hobs24⟩ :=
    site_8000a838_fl σ23 i23 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x8000a838#64) vmi23
      hG23 hpc23 hmi23 hfp23 rfl (by decide) hi23
  have hstep24 : Step ⟨σ23,i23,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ24,i24,c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs24
  have hpc24 : σ24.regs.get? Register.PC = some (0x8000782c#64) := by
    have := obs_jx0_pc_sn5 hobs24
    rwa [show (0x8000a838#64 : BitVec 64) + sign_extend (m := 64) (0x1fcff4#21)
      = (0x8000782c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi24, hmi24⟩ := hG24.minstret
  have hx2_24 : σ24.regs.get? Register.x2 = some vsp :=
    obs_jr_other hobs24 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_23
  have hx20w_24 : σ24.regs.get? Register.x20 = some vwidth :=
    obs_jr_other hobs24 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20w_23
  have hx6w_24 : σ24.regs.get? Register.x6 = some vflags :=
    obs_jr_other hobs24 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6w_23
  have hx22_24 : σ24.regs.get? Register.x22 = some (sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0))) :=
    obs_jr_other hobs24 Register.x22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx22_23
  have hx28w_24 : σ24.regs.get? Register.x28 = some vt3v :=
    obs_jr_other hobs24 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28w_23
  have hx23w_24 : σ24.regs.get? Register.x23 = some vs7v :=
    obs_jr_other hobs24 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23w_23
  have hx8w_24 : σ24.regs.get? Register.x8 = some vs0v :=
    obs_jr_other hobs24 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8w_23
  have hx30_24 : σ24.regs.get? Register.x30 = some (zero_extend (m := 64) sb) :=
    obs_jr_other hobs24 Register.x30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx30_23
  have hx31_24 : σ24.regs.get? Register.x31 = some (0#64) :=
    obs_jr_other hobs24 Register.x31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx31_23
  have hx16n_24 : σ24.regs.get? Register.x16 = some (sign_extend (m := 64)
        (Sail.BitVec.extractLsb ((sign_extend (m := 64) ((Sail.BitVec.extractLsb vtop 31 0) - (Sail.BitVec.extractLsb vcur 31 0)))
          + sign_extend (m := 64) (0x001#12)) 31 0)) :=
    obs_jr_other hobs24 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx16n_23
  -- post-widening: slot sp+0x20 := 0 (σ15's `sd zero,32(sp)`), transported to σ24
  have hs32z_24 : SlotHolds vsp 0x020 (0#64) σ24.mem := by
    have h15 : SlotHolds vsp 0x020 (0#64) σ15.mem := by
      rw [hmem15, hNP14]
      exact slotHolds_self vsp 0x020 _ (0#64) σ14.mem rfl
    have h21 : SlotHolds vsp 0x020 (0#64) σ21.mem := by
      rw [hmem21, hmem20, hmem19, hmem18, hmem17, hmem16]; exact h15
    have h22 : SlotHolds vsp 0x020 (0#64) σ22.mem := by
      rw [hmem22, hNP21b]
      exact slotHolds_writeMap8 vsp 0x020 (0#64) σ21.mem _ _ (by rw [hoff32, hoff56]; omega) h21
    have h23 : SlotHolds vsp 0x020 (0#64) σ23.mem := by
      rw [hmem23, hNP22b]
      exact slotHolds_writeMap8 vsp 0x020 (0#64) σ22.mem _ _ (by rw [hoff32, hoff48]; omega) h22
    rw [hmem24]; exact h23
  -- post-widening: mid-register (+ x26) preservation across all 24 steps
  have hkeep24 : KeepRegs (Register.x26 :: midRegs5) c.σ σ24 := by
    have h0 := keep_rfl (Register.x26 :: midRegs5) c.σ
    have h1 := keep_alu hobs1 (by decide) h0
    have h2 := keep_store hobs2 (by decide) h1
    have h3 := keep_alu hobs3 (by decide) h2
    have h4 := keep_alu hobs4 (by decide) h3
    have h5 := keep_alu hobs5 (by decide) h4
    have h6 := keep_store hobs6 (by decide) h5
    have h7 := keep_alu hobs7 (by decide) h6
    have h8 := keep_alu hobs8 (by decide) h7
    have h9 := keep_alu hobs9 (by decide) h8
    have h10 := keep_alu hobs10 (by decide) h9
    have h11 := keep_bnottaken hobs11 (by decide) h10
    have h12 := keep_alu hobs12 (by decide) h11
    have h13 := keep_alu hobs13 (by decide) h12
    have h14 := keep_alu hobs14 (by decide) h13
    have h15 := keep_store hobs15 (by decide) h14
    have h16 := keep_jr hobs16 (by decide) h15
    have h17 := keep_bnottaken hobs17 (by decide) h16
    have h18 := keep_alu hobs18 (by decide) h17
    have h19 := keep_jr hobs19 (by decide) h18
    have h20 := keep_bnottaken hobs20 (by decide) h19
    have h21 := keep_jr hobs21 (by decide) h20
    have h22 := keep_store hobs22 (by decide) h21
    have h23 := keep_store hobs23 (by decide) h22
    exact keep_jr hobs24 (by decide) h23
  -- post-widening: the pointwise frame outside [sp+32,sp+64) ∪ [sp+104,sp+112)
  have hmframe : ∀ a : Nat, ¬(vsp.toNat + 32 ≤ a ∧ a < vsp.toNat + 64) →
      ¬(vsp.toNat + 104 ≤ a ∧ a < vsp.toNat + 112) →
      σ24.mem[a]? = c.σ.mem[a]? := by
    intro a hA hB
    rw [hmem24, hmem23, hNP22b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff48]; omega),
      hmem22, hNP21b, getElem?_writeMap8_out _ _ _ _ (by rw [hoff56]; omega),
      hmem21, hmem20, hmem19, hmem18, hmem17, hmem16,
      hmem15, hNP14, getElem?_writeMap8_out _ _ _ _ (by rw [hoff32]; omega),
      hmem14, hmem13, hmem12, hmem11, hmem10, hmem9, hmem8, hmem7,
      hmem6, hNP5, getElem?_writeMap8_out _ _ _ _ (by rw [hoff40]; omega),
      hmem5, hmem4, hmem3,
      hmem2, hNP1, getElem?_writeMap8_out _ _ _ _ (by rw [hoff104]; omega),
      hmem1]
  have hload24 : SvfprintfSliceLoaded σ24.mem := hmem24 ▸ hload23
  have hfp24 : FlushPinsLoaded σ24.mem := hmem24 ▸ hfp23
  refine ⟨⟨σ24, i24, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩, ?_, hG24, hpc24, hx22_24, hx16n_24, hx30_24, hx31_24,
    hx20w_24, hx6w_24, hx28w_24, hx23w_24, hx8w_24, hx2_24, hi24, hG24.minstret,
    hs32z_24, hkeep24, hmframe, hload24, hfp24⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans ((Steps.single hstep19).trans ((Steps.single hstep20).trans ((Steps.single hstep21).trans ((Steps.single hstep22).trans ((Steps.single hstep23).trans ((Steps.single hstep24))))))))))))))))))))))))

end Vsa.Sim
