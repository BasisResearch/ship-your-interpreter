import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro4

/-!
# M3 Layer-3 — `SnprintfSpec33` : svfprintf prologue segment G
## `0x8000775c → 0x80007798` — the `%`-directive entry + parse-state init

Establishes exactly the register block the `%lld` dispatch consumes: flags
`t1 = 0`, width `s4 = -1`, bound `s10 = 90`, table base `s6 = 0x8001a0fc`,
`s11 = 0`, cursor `s9 = vfmt+1` with `s8 = 'l'`; the sign-byte slot at
`sp+167` zeroed; the cursor slot at `sp+0` bumped to `vfmt+1`.
Generated in the SnprintfSpec22 house style by /tmp/gen_spec33.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **Segment G of the svfprintf prologue**: `0x8000775c → 0x80007798`.

The `%`-directive entry: cursor reload from the fmt slot, `subw s8,s6,a5 = 0`
(no literal text before the `%`), cursor bump + `lbu` of `format[1] = 'l'`,
the sign-byte slot zeroed at `sp+167`, the cursor slot updated to `vfmt+1`,
and the parse-loop register block: `s4 := -1` (default precision),
`t1 := 0` (flags), `s10 := 90`, `s6 := 0x8001a0fc` (parse jump-table base,
`auipc`/`addi`), `s11 := 0`, `s9 := vfmt+1`. -/
theorem svfProG_spec
    (vsp va0 vfmt : BitVec 64)
    (vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000775c#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some (0x8001b798#64))
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx10 : c.σ.regs.get? Register.x10 = some (1#64))
    (hx12 : c.σ.regs.get? Register.x12 = some vfmt)
    (hx18 : c.σ.regs.get? Register.x18 = some (16#64))
    (hx19 : c.σ.regs.get? Register.x19 = some (37#64))
    (hx21 : c.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx23 : c.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    (hx20 : c.σ.regs.get? Register.x20 = some (0x80012268#64))
    -- the fmt slot still holds vfmt, and format[1] = 'l'
    (hS000 : SlotHolds vsp 0x000 vfmt c.σ.mem)
    (hlB : c.σ.mem[vfmt.toNat + 1]? = some (0x6c#8))
    (hflo : 0x80000000 ≤ vfmt.toNat)
    (hfhi : vfmt.toNat + 8 ≤ 0x100000000)
    (hfhtif1 : vfmt.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vfmt.toNat + 1)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80007798#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some (0x8001b798#64) ∧
      c'.σ.regs.get? Register.x22 = some (0x8001a0fc#64) ∧
      c'.σ.regs.get? Register.x24 = some (0x6c#64) ∧
      c'.σ.regs.get? Register.x25 = some (vfmt + sign_extend (m := 64) (0x001#12)) ∧
      c'.σ.regs.get? Register.x26 = some (90#64) ∧
      c'.σ.regs.get? Register.x20 = some (0xffffffffffffffff#64) ∧
      c'.σ.regs.get? Register.x6 = some (0#64) ∧
      c'.σ.regs.get? Register.x27 = some (0#64) ∧
      c'.σ.regs.get? Register.x10 = some (1#64) ∧
      c'.σ.regs.get? Register.x12 = some vfmt ∧
      c'.σ.regs.get? Register.x18 = some (16#64) ∧
      c'.σ.regs.get? Register.x19 = some (37#64) ∧
      c'.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.mem[vsp.toNat + 167]? = some (0x00#8) ∧
      SlotHolds vsp 0x000 (vfmt + sign_extend (m := 64) (0x001#12)) c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 167 ≤ a ∧ a < vsp.toNat + 168) →
      ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 8) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff0 : (vsp + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat := by
    rw [sext0_add_pro]
  have hofff1 : (vfmt + sign_extend (m := 64) (0x001#12)).toNat = vfmt.toNat + 1 :=
    ptr_addoff vfmt _ 1 (by decide) (by omega)
  have hoff167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    ptr_addoff vsp _ 167 (by decide) (by omega)
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp⟩, ⟨Register.x3, (0x8001b510#64)⟩, ⟨Register.x8, va0⟩, ⟨Register.x9, (0x8001b798#64)⟩, ⟨Register.x22, vfmt⟩, ⟨Register.x10, (1#64)⟩, ⟨Register.x12, vfmt⟩, ⟨Register.x18, (16#64)⟩, ⟨Register.x19, (37#64)⟩, ⟨Register.x21, vsp + sign_extend (m := 64) (0x160#12)⟩, ⟨Register.x23, vsp + sign_extend (m := 64) (0x160#12)⟩, ⟨Register.x24, vS8o⟩, ⟨Register.x25, vS9o⟩, ⟨Register.x26, vS10o⟩, ⟨Register.x27, vS11o⟩, ⟨Register.x20, (0x80012268#64)⟩] :=
    ⟨hx2, hx3, hx8, hx9, hx22, hx10, hx12, hx18, hx19, hx21, hx23, hx24, hx25, hx26, hx27, hx20, trivial⟩
  -- === 0x8000775c: ld a5,0(sp) — the fmt slot (still = vfmt) ===
  obtain ⟨hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := slot_reload_bytes vsp 0x000 vfmt c.σ.mem hS000
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000775c_pr c.σ c.tick c.steps _ vmi0 vsp _ _ _ _ _ _ _ _
      hG hpc hmi0 hp0.1 hsl0 rfl (by rw [hoff0]; omega) (by rw [hoff0]; omega) (Or.inr (by rw [hoff0, htoh]; omega)) (by rw [hoff0]; omega) hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7 htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80007760#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000775c#64) 4 = (0x80007760#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hrd1 : σ1.regs.get? Register.x15 = some (vfmt) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vfmt] at this
  have hp1 := pins_cons_pro hrd1 (pins_alu hobs1 (by rfl) hp0)
  have hmE1 : σ1.mem = c.σ.mem := hmem1
  have hsl1 : Vsa.Sim.Code.SvfprintfSliceLoaded σ1.mem := by rw [hmem1]; exact hsl0

  -- === 0x80007760: mv s4,a0 (dead) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80007760_pr σ1 i1 (c.steps + 1) _ vmi1 (1#64)
      hG1 hpc1 hmi1 hp1.2.2.2.2.2.2.1 hsl1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 2⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80007764#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80007760#64) 4 = (0x80007764#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hrd2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp2 := pins_alu hobs2 (by rfl) (pins_drop17_pro hp1)
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1
  have hsl2 : Vsa.Sim.Code.SvfprintfSliceLoaded σ2.mem := by rw [hmem2]; exact hsl1

  -- === 0x80007764: subw s8,s6,a5 = 0 (same value both sides) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80007764_pr σ2 i2 (c.steps + 2) _ vmi2 vfmt vfmt
      hG2 hpc2 hmi2 hp2.2.2.2.2.2.1 hp2.1 hsl2 rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 2⟩ ⟨σ3, i3, c.steps + 3⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80007768#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80007764#64) 4 = (0x80007768#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hrd3 : σ3.regs.get? Register.x24 = some ((0#64)) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [subw_self_pro vfmt] at this
  have hp3 := pins_cons_pro hrd3 (pins_alu hobs3 (by rfl) (pins_drop13_pro hp2))
  have hmE3 : σ3.mem = c.σ.mem := hmem3.trans hmE2
  have hsl3 : Vsa.Sim.Code.SvfprintfSliceLoaded σ3.mem := by rw [hmem3]; exact hsl2

  -- === 0x80007768: bnez s8 NOT taken ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80007768_nottaken_pr σ3 i3 (c.steps + 3) _ vmi3 (0#64)
      hG3 hpc3 hmi3 hp3.1 hsl3 rfl (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 3⟩ ⟨σ4, i4, c.steps + 4⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x8000776c#64) := by
    have := obs_bnottaken_pc hobs4
    rwa [show BitVec.addInt (0x80007768#64) 4 = (0x8000776c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_bnottaken_minstret hobs4
  have hp4 := pins_bnottaken hobs4 (by rfl) hp3
  have hmE4 : σ4.mem = c.σ.mem := hmem4.trans hmE3
  have hsl4 : Vsa.Sim.Code.SvfprintfSliceLoaded σ4.mem := by rw [hmem4]; exact hsl3

  -- === 0x8000776c: addi a5,s6,1 — cursor past the '%' ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_8000776c_pr σ4 i4 (c.steps + 4) _ vmi4 vfmt
      hG4 hpc4 hmi4 hp4.2.2.2.2.2.2.1 hsl4 rfl hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 4⟩ ⟨σ5, i5, c.steps + 5⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80007770#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x8000776c#64) 4 = (0x80007770#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hrd5 : σ5.regs.get? Register.x15 = some (vfmt + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp5 := pins_cons_pro hrd5 (pins_alu hobs5 (by rfl) (pins_drop2_pro hp4))
  have hmE5 : σ5.mem = c.σ.mem := hmem5.trans hmE4
  have hsl5 : Vsa.Sim.Code.SvfprintfSliceLoaded σ5.mem := by rw [hmem5]; exact hsl4

  -- === 0x80007770: lbu s8,1(s6) — format[1] = 'l' ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80007770_pr σ5 i5 (c.steps + 5) _ vmi5 vfmt _
      hG5 hpc5 hmi5 hp5.2.2.2.2.2.2.1 hsl5 rfl (by rw [hofff1]; omega) (by rw [hofff1]; omega) (by rw [hofff1]; exact hfhtif1) (by rw [hofff1, hmE5]; exact hlB) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 5⟩ ⟨σ6, i6, c.steps + 6⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80007774#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80007770#64) 4 = (0x80007774#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hrd6 : σ6.regs.get? Register.x24 = some ((0x6c#64)) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (zero_extend (m := 64) (0x6c#8) : BitVec 64) = (0x6c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp6 := pins_cons_pro hrd6 (pins_alu hobs6 (by rfl) (pins_drop2_pro hp5))
  have hmE6 : σ6.mem = c.σ.mem := hmem6.trans hmE5
  have hsl6 : Vsa.Sim.Code.SvfprintfSliceLoaded σ6.mem := by rw [hmem6]; exact hsl5

  -- === 0x80007774: sb zero,167(sp) — the sign-byte slot ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80007774_pr σ6 i6 (c.steps + 6) _ vmi6 vsp
      hG6 hpc6 hmi6 hp6.2.2.1 hsl6 rfl (by rw [hoff167]; omega) (by rw [hoff167]; omega) (by rw [hoff167, htoh]; omega) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 7⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80007778#64) := by
    have := obs_store_pc hobs7
    rwa [show BitVec.addInt (0x80007774#64) 4 = (0x80007778#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret hobs7
  have hp7 := pins_store hobs7 (by rfl) hp6
  have hmE7 : σ7.mem = (c.σ.mem).insert (vsp.toNat + 167) (stData 1 (0#64)) := by
    rw [hmem7, mem_afterNextPC, hmE6, hoff167]
  have hsl7 : Vsa.Sim.Code.SvfprintfSliceLoaded σ7.mem := by
    rw [hmem7, mem_afterNextPC]
    exact svfprintfSlice_insert_sn4 _ _ _ (by rw [hoff167]; omega) hsl6

  -- === 0x80007778: sd a5,0(sp) — cursor slot := vfmt+1 ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80007778_pr σ7 i7 (c.steps + 7) _ vmi7 vsp _
      hG7 hpc7 hmi7 hp7.2.2.1 hp7.2.1 hsl7 rfl (by rw [hoff0]; omega) (by rw [hoff0]; omega) (by rw [hoff0, htoh]; omega) (by rw [hoff0]; omega) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 7⟩ ⟨σ8, i8, c.steps + 8⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000777c#64) := by
    have := obs_store_pc hobs8
    rwa [show BitVec.addInt (0x80007778#64) 4 = (0x8000777c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret hobs8
  have hp8 := pins_store hobs8 (by rfl) hp7
  have hmE8 : σ8.mem = writeMap8 ((c.σ.mem).insert (vsp.toNat + 167) (stData 1 (0#64))) (vsp.toNat) (sdData_val (vfmt + sign_extend (m := 64) (0x001#12))) := by
    rw [hmem8, mem_afterNextPC, hmE7, hoff0]
  have hsl8 : Vsa.Sim.Code.SvfprintfSliceLoaded σ8.mem := by
    rw [hmem8, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff0]; omega) hsl7

  -- === 0x8000777c: li s4,-1 — default precision ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_8000777c_pr σ8 i8 (c.steps + 8) _ vmi8
      hG8 hpc8 hmi8 hsl8 rfl hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 8⟩ ⟨σ9, i9, c.steps + 9⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80007780#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x8000777c#64) 4 = (0x80007780#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hrd9 : σ9.regs.get? Register.x20 = some ((0xffffffffffffffff#64)) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) : BitVec 64) + sign_extend (m := 64) (0xfff#12) = (0xffffffffffffffff#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp9 := pins_cons_pro hrd9 (pins_alu hobs9 (by rfl) hp8)
  have hmE9 : σ9.mem = writeMap8 ((c.σ.mem).insert (vsp.toNat + 167) (stData 1 (0#64))) (vsp.toNat) (sdData_val (vfmt + sign_extend (m := 64) (0x001#12))) := hmem9.trans hmE8
  have hsl9 : Vsa.Sim.Code.SvfprintfSliceLoaded σ9.mem := by rw [hmem9]; exact hsl8

  -- === 0x80007780: li t1,0 — the flag word ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80007780_pr σ9 i9 (c.steps + 9) _ vmi9
      hG9 hpc9 hmi9 hsl9 rfl hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 9⟩ ⟨σ10, i10, c.steps + 10⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80007784#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80007780#64) 4 = (0x80007784#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hrd10 : σ10.regs.get? Register.x6 = some ((0#64)) := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro (0#64)] at this
  have hp10 := pins_cons_pro hrd10 (pins_alu hobs10 (by rfl) hp9)
  have hmE10 : σ10.mem = writeMap8 ((c.σ.mem).insert (vsp.toNat + 167) (stData 1 (0#64))) (vsp.toNat) (sdData_val (vfmt + sign_extend (m := 64) (0x001#12))) := hmem10.trans hmE9
  have hsl10 : Vsa.Sim.Code.SvfprintfSliceLoaded σ10.mem := by rw [hmem10]; exact hsl9

  -- === 0x80007784: li s10,90 — dispatch bound ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80007784_pr σ10 i10 (c.steps + 10) _ vmi10
      hG10 hpc10 hmi10 hsl10 rfl hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 10⟩ ⟨σ11, i11, c.steps + 11⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80007788#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x80007784#64) 4 = (0x80007788#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hrd11 : σ11.regs.get? Register.x26 = some ((90#64)) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) : BitVec 64) + sign_extend (m := 64) (0x05a#12) = (90#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp11 := pins_cons_pro hrd11 (pins_alu hobs11 (by rfl) (pins_drop17_pro hp10))
  have hmE11 : σ11.mem = writeMap8 ((c.σ.mem).insert (vsp.toNat + 167) (stData 1 (0#64))) (vsp.toNat) (sdData_val (vfmt + sign_extend (m := 64) (0x001#12))) := hmem11.trans hmE10
  have hsl11 : Vsa.Sim.Code.SvfprintfSliceLoaded σ11.mem := by rw [hmem11]; exact hsl10

  -- === 0x80007788: auipc s6,0x13 ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80007788_pr4 σ11 i11 (c.steps + 11) _ vmi11
      hG11 hpc11 hmi11 hsl11 rfl hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 11⟩ ⟨σ12, i12, c.steps + 12⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x8000778c#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80007788#64) 4 = (0x8000778c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hrd12 : σ12.regs.get? Register.x22 = some ((0x8001a788#64)) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x80007788#64 : BitVec 64) + sign_extend (m := 64) ((0x00013#20) +++ 0x000#12) = (0x8001a788#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp12 := pins_cons_pro hrd12 (pins_alu hobs12 (by rfl) (pins_drop10_pro hp11))
  have hmE12 : σ12.mem = writeMap8 ((c.σ.mem).insert (vsp.toNat + 167) (stData 1 (0#64))) (vsp.toNat) (sdData_val (vfmt + sign_extend (m := 64) (0x001#12))) := hmem12.trans hmE11
  have hsl12 : Vsa.Sim.Code.SvfprintfSliceLoaded σ12.mem := by rw [hmem12]; exact hsl11

  -- === 0x8000778c: addi s6,s6,-1676 — parse jump-table base ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_8000778c_pr σ12 i12 (c.steps + 12) _ vmi12 (0x8001a788#64)
      hG12 hpc12 hmi12 hp12.1 hsl12 rfl hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 12⟩ ⟨σ13, i13, c.steps + 13⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80007790#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x8000778c#64) 4 = (0x80007790#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hrd13 : σ13.regs.get? Register.x22 = some ((0x8001a0fc#64)) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x8001a788#64 : BitVec 64) + sign_extend (m := 64) (0x974#12) = (0x8001a0fc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp13 := pins_cons_pro hrd13 (pins_alu hobs13 (by rfl) hp12.2)
  have hmE13 : σ13.mem = writeMap8 ((c.σ.mem).insert (vsp.toNat + 167) (stData 1 (0#64))) (vsp.toNat) (sdData_val (vfmt + sign_extend (m := 64) (0x001#12))) := hmem13.trans hmE12
  have hsl13 : Vsa.Sim.Code.SvfprintfSliceLoaded σ13.mem := by rw [hmem13]; exact hsl12

  -- === 0x80007790: li s11,0 ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80007790_pr σ13 i13 (c.steps + 13) _ vmi13
      hG13 hpc13 hmi13 hsl13 rfl hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 13⟩ ⟨σ14, i14, c.steps + 14⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x80007794#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x80007790#64) 4 = (0x80007794#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hrd14 : σ14.regs.get? Register.x27 = some ((0#64)) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro (0#64)] at this
  have hp14 := pins_cons_pro hrd14 (pins_alu hobs14 (by rfl) (pins_drop18_pro hp13))
  have hmE14 : σ14.mem = writeMap8 ((c.σ.mem).insert (vsp.toNat + 167) (stData 1 (0#64))) (vsp.toNat) (sdData_val (vfmt + sign_extend (m := 64) (0x001#12))) := hmem14.trans hmE13
  have hsl14 : Vsa.Sim.Code.SvfprintfSliceLoaded σ14.mem := by rw [hmem14]; exact hsl13

  -- === 0x80007794: mv s9,a5 ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80007794_pr σ14 i14 (c.steps + 14) _ vmi14 (vfmt + sign_extend (m := 64) (0x001#12))
      hG14 hpc14 hmi14 hp14.2.2.2.2.2.2.1 hsl14 rfl hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 14⟩ ⟨σ15, i15, c.steps + 15⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80007798#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80007794#64) 4 = (0x80007798#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hrd15 : σ15.regs.get? Register.x25 = some (vfmt + sign_extend (m := 64) (0x001#12)) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro (vfmt + sign_extend (m := 64) (0x001#12))] at this
  have hp15 := pins_cons_pro hrd15 (pins_alu hobs15 (by rfl) (pins_drop18_pro hp14))
  have hmE15 : σ15.mem = writeMap8 ((c.σ.mem).insert (vsp.toNat + 167) (stData 1 (0#64))) (vsp.toNat) (sdData_val (vfmt + sign_extend (m := 64) (0x001#12))) := hmem15.trans hmE14
  have hsl15 : Vsa.Sim.Code.SvfprintfSliceLoaded σ15.mem := by rw [hmem15]; exact hsl14

  have hz167 : σ15.mem[vsp.toNat + 167]? = some (0x00#8) := by
    rw [hmE15, getElem?_writeMap8_out _ (vsp.toNat) _ _ (by omega),
      getElem_insert_self]
    rfl
  have hS000N : SlotHolds vsp 0x000 (vfmt + sign_extend (m := 64) (0x001#12))
      σ15.mem := by
    rw [hmE15]
    exact slot_save vsp 0x000 (vfmt + sign_extend (m := 64) (0x001#12)) _ _ _ hoff0 rfl
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 167 ≤ a ∧ a < vsp.toNat + 168) →
      ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 8) →
      σ15.mem[a]? = c.σ.mem[a]? := by
    intro a hw0 hw1
    rw [hmE15,
      getElem?_writeMap8_out _ (vsp.toNat) _ a (by omega),
      getElem_insert_ne _ a (vsp.toNat + 167) _
        (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]
  refine ⟨⟨σ15, i15, c.steps + 15⟩, ?_,
    hG15,
    hpc15,
    hp15.2.2.2.2.2.2.2.2.1,
    hp15.2.2.2.2.2.2.2.2.2.1,
    hp15.2.2.2.2.2.2.2.2.2.2.1,
    hp15.2.2.2.2.2.2.2.2.2.2.2.1,
    hp15.2.2.1,
    hp15.2.2.2.2.2.2.1,
    hp15.1,
    hp15.2.2.2.1,
    hp15.2.2.2.2.2.1,
    hp15.2.2.2.2.1,
    hp15.2.1,
    hp15.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp15.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp15.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp15.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp15.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp15.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hz167,
    hS000N,
    hagN,
    hsl15,
    hi15,
    ⟨vmi15, hmi15⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans (Steps.single hstep15))))))))))))))

end Vsa.Sim
