import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesRet

/-!
# M3 Layer-3 — `SnprintfSpec31` : svfprintf prologue segment E
## `0x800076f4 → 0x80007728` (the `jal __locale_mb_cur_max`)

Zero inits of the parse-state slots (incl. the TOTAL at `sp+16` — Spec26's
`htotS`), `s1 := &__global_locale`, the `'%'`/`16` constants, the fmt spill
`sd s6,0(sp)` and its immediate reload, and the static `mbtowc` function
pointer load `ld s4,232(s1)` (the parse loop's indirect callee).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec31.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **Segment E of the svfprintf prologue**: `0x800076f4 → 0x80007728`.

The seven zero-initialized parse-state slots (`sp+{40,64,88,104,128,96,16}` —
the last is the TOTAL accumulator, Spec26's `htotS` with `vtot = 0`),
`s1 := &__global_locale` (`0x8001b798`), the `'%'` and `16` constants, the
fmt-cursor spill `sd s6,0(sp)` + reload, and the static
`__global_locale.mbtowc` function-pointer load (`s4 := __ascii_mbtowc =
0x80012268`, Spec26's `hfnslot` data). -/
theorem svfProE_spec
    (vsp va0 vfile vfmt : BitVec 64)
    (vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hms0 : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm0 : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800076f4#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some vfile)
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx21 : c.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx23 : c.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    -- static __global_locale.mbtowc slot bytes at 0x8001b880 (= 0x80012268)
    (hfn0 : c.σ.mem[(0x8001b880 : Nat)]? = some (0x68#8))
    (hfn1 : c.σ.mem[(0x8001b880 : Nat) + 1]? = some (0x22#8))
    (hfn2 : c.σ.mem[(0x8001b880 : Nat) + 2]? = some (0x01#8))
    (hfn3 : c.σ.mem[(0x8001b880 : Nat) + 3]? = some (0x80#8))
    (hfn4 : c.σ.mem[(0x8001b880 : Nat) + 4]? = some (0x00#8))
    (hfn5 : c.σ.mem[(0x8001b880 : Nat) + 5]? = some (0x00#8))
    (hfn6 : c.σ.mem[(0x8001b880 : Nat) + 6]? = some (0x00#8))
    (hfn7 : c.σ.mem[(0x8001b880 : Nat) + 7]? = some (0x00#8))
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80007728#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some (0x8001b798#64) ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x20 = some (0x80012268#64) ∧
      c'.σ.regs.get? Register.x18 = some (16#64) ∧
      c'.σ.regs.get? Register.x19 = some (37#64) ∧
      c'.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      SlotHolds vsp 0x028 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x040 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x058 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x068 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x080 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x060 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x010 (0#64) c'.σ.mem ∧
      SlotHolds vsp 0x000 vfmt c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 40 ≤ a ∧ a < vsp.toNat + 48) →
      ¬(vsp.toNat + 64 ≤ a ∧ a < vsp.toNat + 72) →
      ¬(vsp.toNat + 88 ≤ a ∧ a < vsp.toNat + 96) →
      ¬(vsp.toNat + 104 ≤ a ∧ a < vsp.toNat + 112) →
      ¬(vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 136) →
      ¬(vsp.toNat + 96 ≤ a ∧ a < vsp.toNat + 104) →
      ¬(vsp.toNat + 16 ≤ a ∧ a < vsp.toNat + 24) →
      ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 8) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.MemsetLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff0 : (vsp + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat := by
    rw [sext0_add_pro]
  have hoffloc : ((0x8001b798#64 : BitVec 64) + sign_extend (m := 64) (0x0e8#12)).toNat
      = (0x8001b880 : Nat) := by decide
  have hoff40 : (vsp + sign_extend (m := 64) (0x028#12)).toNat = vsp.toNat + 40 := ptr_addoff vsp _ 40 (by decide) (by omega)
  have hoff64 : (vsp + sign_extend (m := 64) (0x040#12)).toNat = vsp.toNat + 64 := ptr_addoff vsp _ 64 (by decide) (by omega)
  have hoff88 : (vsp + sign_extend (m := 64) (0x058#12)).toNat = vsp.toNat + 88 := ptr_addoff vsp _ 88 (by decide) (by omega)
  have hoff104 : (vsp + sign_extend (m := 64) (0x068#12)).toNat = vsp.toNat + 104 := ptr_addoff vsp _ 104 (by decide) (by omega)
  have hoff128 : (vsp + sign_extend (m := 64) (0x080#12)).toNat = vsp.toNat + 128 := ptr_addoff vsp _ 128 (by decide) (by omega)
  have hoff96 : (vsp + sign_extend (m := 64) (0x060#12)).toNat = vsp.toNat + 96 := ptr_addoff vsp _ 96 (by decide) (by omega)
  have hoff16 : (vsp + sign_extend (m := 64) (0x010#12)).toNat = vsp.toNat + 16 := ptr_addoff vsp _ 16 (by decide) (by omega)
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp⟩, ⟨Register.x3, (0x8001b510#64)⟩, ⟨Register.x8, va0⟩, ⟨Register.x9, vfile⟩, ⟨Register.x22, vfmt⟩, ⟨Register.x21, vsp + sign_extend (m := 64) (0x160#12)⟩, ⟨Register.x23, vsp + sign_extend (m := 64) (0x160#12)⟩, ⟨Register.x24, vS8o⟩, ⟨Register.x25, vS9o⟩, ⟨Register.x26, vS10o⟩, ⟨Register.x27, vS11o⟩] :=
    ⟨hx2, hx3, hx8, hx9, hx22, hx21, hx23, hx24, hx25, hx26, hx27, trivial⟩
  -- === 0x800076f4: sd zero,40(sp) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800076f4_pr c.σ c.tick c.steps _ vmi0 vsp
      hG hpc hmi0 hp0.1 hsl0 rfl (by rw [hoff40]; omega) (by rw [hoff40]; omega) (by rw [hoff40, htoh]; omega) (by rw [hoff40]; omega) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x800076f8#64) := by
    have := obs_store_pc hobs1
    rwa [show BitVec.addInt (0x800076f4#64) 4 = (0x800076f8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_store_minstret hobs1
  have hp1 := pins_store hobs1 (by rfl) hp0
  have hmE1 : σ1.mem = writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64)) := by
    rw [hmem1, mem_afterNextPC, hoff40]
  have hsl1 : Vsa.Sim.Code.SvfprintfSliceLoaded σ1.mem := by
    rw [hmem1, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff40]; omega) hsl0

  -- === 0x800076f8: sd zero,64(sp) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_800076f8_pr σ1 i1 (c.steps + 1) _ vmi1 vsp
      hG1 hpc1 hmi1 hp1.1 hsl1 rfl (by rw [hoff64]; omega) (by rw [hoff64]; omega) (by rw [hoff64, htoh]; omega) (by rw [hoff64]; omega) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 2⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x800076fc#64) := by
    have := obs_store_pc hobs2
    rwa [show BitVec.addInt (0x800076f8#64) 4 = (0x800076fc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret hobs2
  have hp2 := pins_store hobs2 (by rfl) hp1
  have hmE2 : σ2.mem = writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64)) := by
    rw [hmem2, mem_afterNextPC, hmE1, hoff64]
  have hsl2 : Vsa.Sim.Code.SvfprintfSliceLoaded σ2.mem := by
    rw [hmem2, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff64]; omega) hsl1

  -- === 0x800076fc: sd zero,88(sp) ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_800076fc_pr σ2 i2 (c.steps + 2) _ vmi2 vsp
      hG2 hpc2 hmi2 hp2.1 hsl2 rfl (by rw [hoff88]; omega) (by rw [hoff88]; omega) (by rw [hoff88, htoh]; omega) (by rw [hoff88]; omega) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 2⟩ ⟨σ3, i3, c.steps + 3⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80007700#64) := by
    have := obs_store_pc hobs3
    rwa [show BitVec.addInt (0x800076fc#64) 4 = (0x80007700#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret hobs3
  have hp3 := pins_store hobs3 (by rfl) hp2
  have hmE3 : σ3.mem = writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64)) := by
    rw [hmem3, mem_afterNextPC, hmE2, hoff88]
  have hsl3 : Vsa.Sim.Code.SvfprintfSliceLoaded σ3.mem := by
    rw [hmem3, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff88]; omega) hsl2

  -- === 0x80007700: sd zero,104(sp) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80007700_pr σ3 i3 (c.steps + 3) _ vmi3 vsp
      hG3 hpc3 hmi3 hp3.1 hsl3 rfl (by rw [hoff104]; omega) (by rw [hoff104]; omega) (by rw [hoff104, htoh]; omega) (by rw [hoff104]; omega) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 3⟩ ⟨σ4, i4, c.steps + 4⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80007704#64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x80007700#64) 4 = (0x80007704#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret hobs4
  have hp4 := pins_store hobs4 (by rfl) hp3
  have hmE4 : σ4.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64))) (vsp.toNat + 104) (sdData_val (0#64)) := by
    rw [hmem4, mem_afterNextPC, hmE3, hoff104]
  have hsl4 : Vsa.Sim.Code.SvfprintfSliceLoaded σ4.mem := by
    rw [hmem4, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff104]; omega) hsl3

  -- === 0x80007704: sd zero,128(sp) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80007704_pr σ4 i4 (c.steps + 4) _ vmi4 vsp
      hG4 hpc4 hmi4 hp4.1 hsl4 rfl (by rw [hoff128]; omega) (by rw [hoff128]; omega) (by rw [hoff128, htoh]; omega) (by rw [hoff128]; omega) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 4⟩ ⟨σ5, i5, c.steps + 5⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80007708#64) := by
    have := obs_store_pc hobs5
    rwa [show BitVec.addInt (0x80007704#64) 4 = (0x80007708#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret hobs5
  have hp5 := pins_store hobs5 (by rfl) hp4
  have hmE5 : σ5.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64))) (vsp.toNat + 104) (sdData_val (0#64))) (vsp.toNat + 128) (sdData_val (0#64)) := by
    rw [hmem5, mem_afterNextPC, hmE4, hoff128]
  have hsl5 : Vsa.Sim.Code.SvfprintfSliceLoaded σ5.mem := by
    rw [hmem5, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff128]; omega) hsl4

  -- === 0x80007708: sd zero,96(sp) ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80007708_pr σ5 i5 (c.steps + 5) _ vmi5 vsp
      hG5 hpc5 hmi5 hp5.1 hsl5 rfl (by rw [hoff96]; omega) (by rw [hoff96]; omega) (by rw [hoff96, htoh]; omega) (by rw [hoff96]; omega) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 5⟩ ⟨σ6, i6, c.steps + 6⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x8000770c#64) := by
    have := obs_store_pc hobs6
    rwa [show BitVec.addInt (0x80007708#64) 4 = (0x8000770c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_store_minstret hobs6
  have hp6 := pins_store hobs6 (by rfl) hp5
  have hmE6 : σ6.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64))) (vsp.toNat + 104) (sdData_val (0#64))) (vsp.toNat + 128) (sdData_val (0#64))) (vsp.toNat + 96) (sdData_val (0#64)) := by
    rw [hmem6, mem_afterNextPC, hmE5, hoff96]
  have hsl6 : Vsa.Sim.Code.SvfprintfSliceLoaded σ6.mem := by
    rw [hmem6, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff96]; omega) hsl5

  -- === 0x8000770c: sd zero,16(sp) ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_8000770c_pr σ6 i6 (c.steps + 6) _ vmi6 vsp
      hG6 hpc6 hmi6 hp6.1 hsl6 rfl (by rw [hoff16]; omega) (by rw [hoff16]; omega) (by rw [hoff16, htoh]; omega) (by rw [hoff16]; omega) hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 7⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80007710#64) := by
    have := obs_store_pc hobs7
    rwa [show BitVec.addInt (0x8000770c#64) 4 = (0x80007710#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_store_minstret hobs7
  have hp7 := pins_store hobs7 (by rfl) hp6
  have hmE7 : σ7.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64))) (vsp.toNat + 104) (sdData_val (0#64))) (vsp.toNat + 128) (sdData_val (0#64))) (vsp.toNat + 96) (sdData_val (0#64))) (vsp.toNat + 16) (sdData_val (0#64)) := by
    rw [hmem7, mem_afterNextPC, hmE6, hoff16]
  have hsl7 : Vsa.Sim.Code.SvfprintfSliceLoaded σ7.mem := by
    rw [hmem7, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff16]; omega) hsl6

  -- === 0x80007710: addi s1,gp,648 — s1 := &__global_locale ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80007710_pr σ7 i7 (c.steps + 7) _ vmi7 (0x8001b510#64)
      hG7 hpc7 hmi7 hp7.2.1 hsl7 rfl hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 7⟩ ⟨σ8, i8, c.steps + 8⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80007714#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80007710#64) 4 = (0x80007714#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hrd8 : σ8.regs.get? Register.x9 = some ((0x8001b798#64)) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x8001b510#64 : BitVec 64) + sign_extend (m := 64) (0x288#12) = (0x8001b798#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp8 := pins_cons_pro hrd8 (pins_alu hobs8 (by rfl) (pins_drop4_pro hp7))
  have hmE8 : σ8.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64))) (vsp.toNat + 104) (sdData_val (0#64))) (vsp.toNat + 128) (sdData_val (0#64))) (vsp.toNat + 96) (sdData_val (0#64))) (vsp.toNat + 16) (sdData_val (0#64)) := hmem8.trans hmE7
  have hsl8 : Vsa.Sim.Code.SvfprintfSliceLoaded σ8.mem := by rw [hmem8]; exact hsl7

  -- === 0x80007714: li s3,37 — '%' ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80007714_pr σ8 i8 (c.steps + 8) _ vmi8
      hG8 hpc8 hmi8 hsl8 rfl hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 8⟩ ⟨σ9, i9, c.steps + 9⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80007718#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x80007714#64) 4 = (0x80007718#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hrd9 : σ9.regs.get? Register.x19 = some ((37#64)) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) : BitVec 64) + sign_extend (m := 64) (0x025#12) = (37#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp9 := pins_cons_pro hrd9 (pins_alu hobs9 (by rfl) hp8)
  have hmE9 : σ9.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64))) (vsp.toNat + 104) (sdData_val (0#64))) (vsp.toNat + 128) (sdData_val (0#64))) (vsp.toNat + 96) (sdData_val (0#64))) (vsp.toNat + 16) (sdData_val (0#64)) := hmem9.trans hmE8
  have hsl9 : Vsa.Sim.Code.SvfprintfSliceLoaded σ9.mem := by rw [hmem9]; exact hsl8

  -- === 0x80007718: li s2,16 ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80007718_pr σ9 i9 (c.steps + 9) _ vmi9
      hG9 hpc9 hmi9 hsl9 rfl hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 9⟩ ⟨σ10, i10, c.steps + 10⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x8000771c#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80007718#64) 4 = (0x8000771c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hrd10 : σ10.regs.get? Register.x18 = some ((16#64)) := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) : BitVec 64) + sign_extend (m := 64) (0x010#12) = (16#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp10 := pins_cons_pro hrd10 (pins_alu hobs10 (by rfl) hp9)
  have hmE10 : σ10.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64))) (vsp.toNat + 104) (sdData_val (0#64))) (vsp.toNat + 128) (sdData_val (0#64))) (vsp.toNat + 96) (sdData_val (0#64))) (vsp.toNat + 16) (sdData_val (0#64)) := hmem10.trans hmE9
  have hsl10 : Vsa.Sim.Code.SvfprintfSliceLoaded σ10.mem := by rw [hmem10]; exact hsl9

  -- === 0x8000771c: sd s6,0(sp) — the fmt cursor slot ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_8000771c_pr σ10 i10 (c.steps + 10) _ vmi10 vsp _
      hG10 hpc10 hmi10 hp10.2.2.2.1 hp10.2.2.2.2.2.2.1 hsl10 rfl (by rw [hoff0]; omega) (by rw [hoff0]; omega) (by rw [hoff0, htoh]; omega) (by rw [hoff0]; omega) hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 10⟩ ⟨σ11, i11, c.steps + 11⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80007720#64) := by
    have := obs_store_pc hobs11
    rwa [show BitVec.addInt (0x8000771c#64) 4 = (0x80007720#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_store_minstret hobs11
  have hp11 := pins_store hobs11 (by rfl) hp10
  have hmE11 : σ11.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64))) (vsp.toNat + 104) (sdData_val (0#64))) (vsp.toNat + 128) (sdData_val (0#64))) (vsp.toNat + 96) (sdData_val (0#64))) (vsp.toNat + 16) (sdData_val (0#64))) (vsp.toNat) (sdData_val vfmt) := by
    rw [hmem11, mem_afterNextPC, hmE10, hoff0]
  have hsl11 : Vsa.Sim.Code.SvfprintfSliceLoaded σ11.mem := by
    rw [hmem11, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff0]; omega) hsl10

  -- === 0x80007720: ld s6,0(sp) — reload the fmt cursor ===
  have hrb0 : σ11.mem[vsp.toNat]? = some ((sdData_val vfmt).extractLsb' 0 8) := by rw [hmE11]; exact getElem_writeMap8_0 _ _ _
  have hrb1 : σ11.mem[vsp.toNat + 1]? = some ((sdData_val vfmt).extractLsb' 8 8) := by rw [hmE11]; exact getElem_writeMap8_1 _ _ _
  have hrb2 : σ11.mem[vsp.toNat + 2]? = some ((sdData_val vfmt).extractLsb' 16 8) := by rw [hmE11]; exact getElem_writeMap8_2 _ _ _
  have hrb3 : σ11.mem[vsp.toNat + 3]? = some ((sdData_val vfmt).extractLsb' 24 8) := by rw [hmE11]; exact getElem_writeMap8_3 _ _ _
  have hrb4 : σ11.mem[vsp.toNat + 4]? = some ((sdData_val vfmt).extractLsb' 32 8) := by rw [hmE11]; exact getElem_writeMap8_4 _ _ _
  have hrb5 : σ11.mem[vsp.toNat + 5]? = some ((sdData_val vfmt).extractLsb' 40 8) := by rw [hmE11]; exact getElem_writeMap8_5 _ _ _
  have hrb6 : σ11.mem[vsp.toNat + 6]? = some ((sdData_val vfmt).extractLsb' 48 8) := by rw [hmE11]; exact getElem_writeMap8_6 _ _ _
  have hrb7 : σ11.mem[vsp.toNat + 7]? = some ((sdData_val vfmt).extractLsb' 56 8) := by rw [hmE11]; exact getElem_writeMap8_7 _ _ _
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80007720_rt σ11 i11 (c.steps + 11) _ vmi11 vsp _ _ _ _ _ _ _ _
      hG11 hpc11 hmi11 hp11.2.2.2.1 hsl11 rfl (by rw [hoff0]; omega) (by rw [hoff0]; omega) (Or.inr (by rw [hoff0, htoh]; omega)) (by rw [hoff0]; omega) (by rw [hoff0]; exact hrb0) (by rw [hoff0]; exact hrb1) (by rw [hoff0]; exact hrb2) (by rw [hoff0]; exact hrb3) (by rw [hoff0]; exact hrb4) (by rw [hoff0]; exact hrb5) (by rw [hoff0]; exact hrb6) (by rw [hoff0]; exact hrb7) hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 11⟩ ⟨σ12, i12, c.steps + 12⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x80007724#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80007720#64) 4 = (0x80007724#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hrd12 : σ12.regs.get? Register.x22 = some (vfmt) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [slot_reassemble vfmt] at this
  have hp12 := pins_cons_pro hrd12 (pins_alu hobs12 (by rfl) (pins_drop7_pro hp11))
  have hmE12 : σ12.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64))) (vsp.toNat + 104) (sdData_val (0#64))) (vsp.toNat + 128) (sdData_val (0#64))) (vsp.toNat + 96) (sdData_val (0#64))) (vsp.toNat + 16) (sdData_val (0#64))) (vsp.toNat) (sdData_val vfmt) := hmem12.trans hmE11
  have hsl12 : Vsa.Sim.Code.SvfprintfSliceLoaded σ12.mem := by rw [hmem12]; exact hsl11

  -- below-frame agreement at σ12 (all eight writes are in-frame)
  have hagA : ∀ a : Nat, a < vsp.toNat → σ12.mem[a]? = c.σ.mem[a]? := by
    intro a ha
    rw [hmE12,
      getElem?_writeMap8_out _ (vsp.toNat) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 16) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 96) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 128) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 104) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 88) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 64) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 40) _ a (by omega)]

  -- === 0x80007724: ld s4,232(s1) — __global_locale.mbtowc = __ascii_mbtowc ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80007724_rt σ12 i12 (c.steps + 12) _ vmi12 (0x8001b798#64) _ _ _ _ _ _ _ _
      hG12 hpc12 hmi12 hp12.2.2.2.1 hsl12 rfl (by rw [hoffloc]; omega) (by rw [hoffloc]; omega) (Or.inr (by rw [hoffloc, htoh]; omega)) (by rw [hoffloc]) (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn0) (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn1) (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn2) (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn3) (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn4) (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn5) (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn6) (by rw [hoffloc]; exact (hagA _ (by omega)).trans hfn7) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 12⟩ ⟨σ13, i13, c.steps + 13⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80007728#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x80007724#64) 4 = (0x80007728#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hrd13 : σ13.regs.get? Register.x20 = some ((0x80012268#64)) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) (((((((((0x00#8).append (0x00#8)).append (0x00#8)).append (0x00#8)).append (0x80#8)).append (0x01#8)).append (0x22#8)).append (0x68#8)) : BitVec (8 * 8)) : BitVec 64) = (0x80012268#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp13 := pins_cons_pro hrd13 (pins_alu hobs13 (by rfl) hp12)
  have hmE13 : σ13.mem = writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (c.σ.mem) (vsp.toNat + 40) (sdData_val (0#64))) (vsp.toNat + 64) (sdData_val (0#64))) (vsp.toNat + 88) (sdData_val (0#64))) (vsp.toNat + 104) (sdData_val (0#64))) (vsp.toNat + 128) (sdData_val (0#64))) (vsp.toNat + 96) (sdData_val (0#64))) (vsp.toNat + 16) (sdData_val (0#64))) (vsp.toNat) (sdData_val vfmt) := hmem13.trans hmE12
  have hsl13 : Vsa.Sim.Code.SvfprintfSliceLoaded σ13.mem := by rw [hmem13]; exact hsl12

  have hS028 : SlotHolds vsp 0x028 (0#64) σ13.mem := by
    rw [hmE13]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff40]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff40]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff40]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff40]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff40]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff40]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff40]; omega) ?_
    exact slot_save vsp 0x028 (0#64) _ _ _ hoff40 rfl
  have hS040 : SlotHolds vsp 0x040 (0#64) σ13.mem := by
    rw [hmE13]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff64]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff64]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff64]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff64]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff64]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff64]; omega) ?_
    exact slot_save vsp 0x040 (0#64) _ _ _ hoff64 rfl
  have hS058 : SlotHolds vsp 0x058 (0#64) σ13.mem := by
    rw [hmE13]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff88]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff88]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff88]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff88]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff88]; omega) ?_
    exact slot_save vsp 0x058 (0#64) _ _ _ hoff88 rfl
  have hS068 : SlotHolds vsp 0x068 (0#64) σ13.mem := by
    rw [hmE13]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff104]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff104]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff104]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff104]; omega) ?_
    exact slot_save vsp 0x068 (0#64) _ _ _ hoff104 rfl
  have hS080 : SlotHolds vsp 0x080 (0#64) σ13.mem := by
    rw [hmE13]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff128]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff128]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff128]; omega) ?_
    exact slot_save vsp 0x080 (0#64) _ _ _ hoff128 rfl
  have hS060 : SlotHolds vsp 0x060 (0#64) σ13.mem := by
    rw [hmE13]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff96]; omega) ?_
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff96]; omega) ?_
    exact slot_save vsp 0x060 (0#64) _ _ _ hoff96 rfl
  have hS010 : SlotHolds vsp 0x010 (0#64) σ13.mem := by
    rw [hmE13]
    refine slot_survives_writeMap8 _ _ _ _ _ _ (by rw [hoff16]; omega) ?_
    exact slot_save vsp 0x010 (0#64) _ _ _ hoff16 rfl
  have hS000 : SlotHolds vsp 0x000 vfmt σ13.mem := by
    rw [hmE13]
    exact slot_save vsp 0x000 vfmt _ _ _ hoff0 rfl
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 40 ≤ a ∧ a < vsp.toNat + 48) →
      ¬(vsp.toNat + 64 ≤ a ∧ a < vsp.toNat + 72) →
      ¬(vsp.toNat + 88 ≤ a ∧ a < vsp.toNat + 96) →
      ¬(vsp.toNat + 104 ≤ a ∧ a < vsp.toNat + 112) →
      ¬(vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 136) →
      ¬(vsp.toNat + 96 ≤ a ∧ a < vsp.toNat + 104) →
      ¬(vsp.toNat + 16 ≤ a ∧ a < vsp.toNat + 24) →
      ¬(vsp.toNat ≤ a ∧ a < vsp.toNat + 8) →
      σ13.mem[a]? = c.σ.mem[a]? := by
    intro a hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7
    rw [hmE13,
      getElem?_writeMap8_out _ (vsp.toNat) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 16) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 96) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 128) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 104) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 88) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 64) _ a (by omega),
      getElem?_writeMap8_out _ (vsp.toNat + 40) _ a (by omega)]
  have hmsN : Vsa.Sim.Code.MemsetLoaded σ13.mem := by
    rw [hmE13]
    exact memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega)
      (memset_w8_pro _ _ _ (by omega) (memset_w8_pro _ _ _ (by omega) hms0)))))))
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ13.mem := by
    rw [hmE13]
    exact localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega)
      (localemb_w8_pro _ _ _ (by omega) (localemb_w8_pro _ _ _ (by omega) hlm0)))))))
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ13.mem := by
    rw [hmE13]
    exact amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega)
      (amb_w8_pro _ _ _ (by omega) (amb_w8_pro _ _ _ (by omega) hamb0)))))))
  refine ⟨⟨σ13, i13, c.steps + 13⟩, ?_,
    hG13,
    hpc13,
    hp13.2.2.2.2.2.1,
    hp13.2.2.2.2.2.2.1,
    hp13.2.2.2.2.2.2.2.1,
    hp13.2.2.2.2.1,
    hp13.2.1,
    hp13.1,
    hp13.2.2.1,
    hp13.2.2.2.1,
    hp13.2.2.2.2.2.2.2.2.1,
    hp13.2.2.2.2.2.2.2.2.2.1,
    hp13.2.2.2.2.2.2.2.2.2.2.1,
    hp13.2.2.2.2.2.2.2.2.2.2.2.1,
    hp13.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp13.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hS028,
    hS040,
    hS058,
    hS068,
    hS080,
    hS060,
    hS010,
    hS000,
    hagN,
    hsl13,
    hmsN,
    hlmN,
    hambN,
    hi13,
    ⟨vmi13, hmi13⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans (Steps.single hstep13))))))))))))

end Vsa.Sim
