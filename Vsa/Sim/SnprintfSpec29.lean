import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro3
import Vsa.Sim.SnprintfSitesPro4

/-!
# M3 Layer-3 — `SnprintfSpec29` : svfprintf prologue segment C
## `0x800076a0` (the `jal memset`) → `0x800076bc` (second spill block)

`memset(sp+200, 0, 8)` (mbstate init) fully inlined — small-size `bgeu`
dispatch, computed `jr 12(a3)` into the byte-store chain, 8 × `sb`, `ret` —
then the FILE `_flags` `lhu`/`andi 128`/`beqz`-taken check (the `__SCLE`
bit is clear for the `_svsnprintf_r` string sink).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec29.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **Segment C of the svfprintf prologue**: `0x800076a0 → 0x800076bc`.

The `jal memset` with the whole concrete `memset(sp+200, 0, 8)` execution
inlined (small-size dispatch `bgeu 15,8` taken, computed `jr` into the sb
chain, eight byte stores, `ret`), then the FILE `_flags` check: `lhu
a5,16(s1)`, `andi a5,a5,128` (the `__SCLE` bit is clear for the string-sink
FILE, caller fact `hflagB`), `beqz` taken to the second spill block. -/
theorem svfProC_spec
    (vsp va0 vfile vfmt : BitVec 64)
    (vS2o vS3o vS4o vS5o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (fl0 fl1 : BitVec 8)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hms0 : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm0 : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800076a0#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some vfile)
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx10 : c.σ.regs.get? Register.x10 = some (vsp + sign_extend (m := 64) (0x0c8#12)))
    (hx11 : c.σ.regs.get? Register.x11 = some (0#64))
    (hx12 : c.σ.regs.get? Register.x12 = some (8#64))
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    -- the FILE `_flags` halfword (bit 7, `__SCLE`, clear)
    (hfl0B : c.σ.mem[vfile.toNat + 16]? = some fl0)
    (hfl1B : c.σ.mem[vfile.toNat + 17]? = some fl1)
    (hflagB : (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)) : BitVec 64)
        &&& sign_extend (m := 64) (0x080#12) = 0#64)
    (hfilelo : vsp.toNat + 592 ≤ vfile.toNat)
    (hfilehi : vfile.toNat + 24 ≤ 0x100000000)
    (hfileal : vfile.toNat % 8 = 0)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800076bc#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x1 = some (0x800076a4#64) ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some vfile ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some vS5o ∧
      c'.σ.regs.get? Register.x23 = some vS7o ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      c'.σ.mem[vsp.toNat + 200]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 201]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 202]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 203]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 204]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 205]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 206]? = some (0x00#8) ∧
      c'.σ.mem[vsp.toNat + 207]? = some (0x00#8) ∧
      (∀ a : Nat, ¬(vsp.toNat + 200 ≤ a ∧ a < vsp.toNat + 208) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.MemsetLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoffc8 : (vsp + sign_extend (m := 64) (0x0c8#12)).toNat = vsp.toNat + 200 :=
    ptr_addoff vsp _ 200 (by decide) (by omega)
  have hoffsb0 : ((vsp + sign_extend (m := 64) (0x0c8#12)) + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat + 200 := by
    rw [ptr_addoff _ _ 0 (by decide) (by rw [hoffc8]; omega), hoffc8]
  have hoffsb1 : ((vsp + sign_extend (m := 64) (0x0c8#12)) + sign_extend (m := 64) (0x001#12)).toNat = vsp.toNat + 201 := by
    rw [ptr_addoff _ _ 1 (by decide) (by rw [hoffc8]; omega), hoffc8]
  have hoffsb2 : ((vsp + sign_extend (m := 64) (0x0c8#12)) + sign_extend (m := 64) (0x002#12)).toNat = vsp.toNat + 202 := by
    rw [ptr_addoff _ _ 2 (by decide) (by rw [hoffc8]; omega), hoffc8]
  have hoffsb3 : ((vsp + sign_extend (m := 64) (0x0c8#12)) + sign_extend (m := 64) (0x003#12)).toNat = vsp.toNat + 203 := by
    rw [ptr_addoff _ _ 3 (by decide) (by rw [hoffc8]; omega), hoffc8]
  have hoffsb4 : ((vsp + sign_extend (m := 64) (0x0c8#12)) + sign_extend (m := 64) (0x004#12)).toNat = vsp.toNat + 204 := by
    rw [ptr_addoff _ _ 4 (by decide) (by rw [hoffc8]; omega), hoffc8]
  have hoffsb5 : ((vsp + sign_extend (m := 64) (0x0c8#12)) + sign_extend (m := 64) (0x005#12)).toNat = vsp.toNat + 205 := by
    rw [ptr_addoff _ _ 5 (by decide) (by rw [hoffc8]; omega), hoffc8]
  have hoffsb6 : ((vsp + sign_extend (m := 64) (0x0c8#12)) + sign_extend (m := 64) (0x006#12)).toNat = vsp.toNat + 206 := by
    rw [ptr_addoff _ _ 6 (by decide) (by rw [hoffc8]; omega), hoffc8]
  have hoffsb7 : ((vsp + sign_extend (m := 64) (0x0c8#12)) + sign_extend (m := 64) (0x007#12)).toNat = vsp.toNat + 207 := by
    rw [ptr_addoff _ _ 7 (by decide) (by rw [hoffc8]; omega), hoffc8]
  have hoafl : (vfile + sign_extend (m := 64) (0x010#12)).toNat = vfile.toNat + 16 := ptr_addoff vfile _ 16 (by decide) (by omega)
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp⟩, ⟨Register.x3, (0x8001b510#64)⟩, ⟨Register.x8, va0⟩, ⟨Register.x9, vfile⟩, ⟨Register.x22, vfmt⟩, ⟨Register.x10, vsp + sign_extend (m := 64) (0x0c8#12)⟩, ⟨Register.x11, (0#64)⟩, ⟨Register.x12, (8#64)⟩, ⟨Register.x18, vS2o⟩, ⟨Register.x19, vS3o⟩, ⟨Register.x20, vS4o⟩, ⟨Register.x21, vS5o⟩, ⟨Register.x23, vS7o⟩, ⟨Register.x24, vS8o⟩, ⟨Register.x25, vS9o⟩, ⟨Register.x26, vS10o⟩, ⟨Register.x27, vS11o⟩] :=
    ⟨hx2, hx3, hx8, hx9, hx22, hx10, hx11, hx12, hx18, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, trivial⟩
  -- === 0x800076a0: jal memset ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_800076a0_pr c.σ c.tick c.steps _ vmi0
      hG hpc hmi0 hsl0 rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006aec#64) := by
    have := obs_jal_pc hobs1
    rwa [show (0x800076a0#64 : BitVec 64) + sign_extend (m := 64) (0x1ff44c#21) = (0x80006aec#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_jal_minstret hobs1
  have hrd1 : σ1.regs.get? Register.x1 = some ((0x800076a4#64)) := by
    have := obs_jal_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800076a0#64) 4 = (0x800076a4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp1 := pins_cons_pro hrd1 (pins_jal hobs1 (by rfl) hp0)
  have hmE1 : σ1.mem = c.σ.mem := hmem1

  -- === 0x80006aec: li t1,15 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006aec_pm σ1 i1 (c.steps + 1) _ vmi1
      hG1 hpc1 hmi1 (hmE1 ▸ hms0) rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 2⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006af0#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80006aec#64) 4 = (0x80006af0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hrd2 : σ2.regs.get? Register.x6 = some ((15#64)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) : BitVec 64) + sign_extend (m := 64) (0x00f#12) = (15#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp2 := pins_cons_pro hrd2 (pins_alu hobs2 (by rfl) hp1)
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1

  -- === 0x80006af0: mv a4,a0 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006af0_pm σ2 i2 (c.steps + 2) _ vmi2 (vsp + sign_extend (m := 64) (0x0c8#12))
      hG2 hpc2 hmi2 hp2.2.2.2.2.2.2.2.1 (hmE2 ▸ hms0) rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 2⟩ ⟨σ3, i3, c.steps + 3⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006af4#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80006af0#64) 4 = (0x80006af4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hrd3 : σ3.regs.get? Register.x14 = some (vsp + sign_extend (m := 64) (0x0c8#12)) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro (vsp + sign_extend (m := 64) (0x0c8#12))] at this
  have hp3 := pins_cons_pro hrd3 (pins_alu hobs3 (by rfl) hp2)
  have hmE3 : σ3.mem = c.σ.mem := hmem3.trans hmE2

  -- === 0x80006af4: bgeu t1,a2 TAKEN (15 ≥ 8) ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006af4_taken_pm σ3 i3 (c.steps + 3) _ vmi3 (15#64) (8#64)
      hG3 hpc3 hmi3 hp3.2.1 hp3.2.2.2.2.2.2.2.2.2.2.1 (hmE3 ▸ hms0) rfl (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 3⟩ ⟨σ4, i4, c.steps + 4⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006b28#64) := by
    have := obs_btaken_pc hobs4
    rwa [site_80006af4_taken_pm_tgt] at this
  obtain ⟨vmi4, hmi4⟩ := obs_btaken_minstret hobs4
  have hp4 := pins_btaken hobs4 (by rfl) hp3
  have hmE4 : σ4.mem = c.σ.mem := hmem4.trans hmE3

  -- === 0x80006b28: sub a3,t1,a2 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006b28_pm σ4 i4 (c.steps + 4) _ vmi4 (15#64) (8#64)
      hG4 hpc4 hmi4 hp4.2.1 hp4.2.2.2.2.2.2.2.2.2.2.1 (hmE4 ▸ hms0) rfl hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 4⟩ ⟨σ5, i5, c.steps + 5⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006b2c#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80006b28#64) 4 = (0x80006b2c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hrd5 : σ5.regs.get? Register.x13 = some ((7#64)) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (15#64 : BitVec 64) - (8#64) = (7#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp5 := pins_cons_pro hrd5 (pins_alu hobs5 (by rfl) hp4)
  have hmE5 : σ5.mem = c.σ.mem := hmem5.trans hmE4

  -- === 0x80006b2c: slli a3,a3,0x2 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006b2c_pm4 σ5 i5 (c.steps + 5) _ vmi5 (7#64)
      hG5 hpc5 hmi5 hp5.1 (hmE5 ▸ hms0) rfl hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 5⟩ ⟨σ6, i6, c.steps + 6⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006b30#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80006b2c#64) 4 = (0x80006b30#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hrd6 : σ6.regs.get? Register.x13 = some ((28#64)) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show shift_bits_left (7#64 : BitVec 64) (Sail.BitVec.extractLsb (0x02#6) 5 0) = (28#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp6 := pins_cons_pro hrd6 (pins_alu hobs6 (by rfl) hp5.2)
  have hmE6 : σ6.mem = c.σ.mem := hmem6.trans hmE5

  -- === 0x80006b30: auipc t0,0x0 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006b30_pm4 σ6 i6 (c.steps + 6) _ vmi6
      hG6 hpc6 hmi6 (hmE6 ▸ hms0) rfl hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 7⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006b34#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80006b30#64) 4 = (0x80006b34#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hrd7 : σ7.regs.get? Register.x5 = some ((0x80006b30#64)) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x80006b30#64 : BitVec 64) + sign_extend (m := 64) ((0x00000#20) +++ 0x000#12) = (0x80006b30#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp7 := pins_cons_pro hrd7 (pins_alu hobs7 (by rfl) hp6)
  have hmE7 : σ7.mem = c.σ.mem := hmem7.trans hmE6

  -- === 0x80006b34: add a3,a3,t0 ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006b34_pm σ7 i7 (c.steps + 7) _ vmi7 (28#64) (0x80006b30#64)
      hG7 hpc7 hmi7 hp7.2.1 hp7.1 (hmE7 ▸ hms0) rfl hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 7⟩ ⟨σ8, i8, c.steps + 8⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006b38#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80006b34#64) 4 = (0x80006b38#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hrd8 : σ8.regs.get? Register.x13 = some ((0x80006b4c#64)) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (28#64 : BitVec 64) + (0x80006b30#64) = (0x80006b4c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp8 := pins_cons_pro hrd8 (pins_alu hobs8 (by rfl) (pins_drop2_pro hp7))
  have hmE8 : σ8.mem = c.σ.mem := hmem8.trans hmE7

  -- === 0x80006b38: jr 12(a3) → sb chain entry for n = 8 ===
  have hjr : BitVec.update ((0x80006b4c#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12)) 0 0#1 = (0x80006b58#64 : BitVec 64) := by apply BitVec.eq_of_toNat_eq; decide
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80006b38_pm4 σ8 i8 (c.steps + 8) _ vmi8 (0x80006b4c#64)
      hG8 hpc8 hmi8 hp8.1 (hmE8 ▸ hms0) rfl (by rw [hjr]; decide) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 8⟩ ⟨σ9, i9, c.steps + 9⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80006b58#64) := by
    have := obs_jr_pc hobs9
    rwa [hjr] at this
  obtain ⟨vmi9, hmi9⟩ := obs_jr_minstret hobs9
  have hp9 := pins_jr hobs9 (by rfl) hp8
  have hmE9 : σ9.mem = c.σ.mem := hmem9.trans hmE8

  -- === 0x80006b58:  ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80006b58_pm σ9 i9 (c.steps + 9) _ vmi9 (vsp + sign_extend (m := 64) (0x0c8#12)) _
      hG9 hpc9 hmi9 hp9.2.2.1 hp9.2.2.2.2.2.2.2.2.2.2.2.1 (hmE9 ▸ hms0) rfl (by rw [hoffsb7]; omega) (by rw [hoffsb7]; omega) (by rw [hoffsb7, htoh]; omega) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 9⟩ ⟨σ10, i10, c.steps + 10⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80006b5c#64) := by
    have := obs_store_pc hobs10
    rwa [show BitVec.addInt (0x80006b58#64) 4 = (0x80006b5c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_store_minstret hobs10
  have hp10 := pins_store hobs10 (by rfl) hp9
  have hmE10 : σ10.mem = (c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64)) := by
    rw [hmem10, mem_afterNextPC, hmE9, hoffsb7]

  have hmsA10 : Vsa.Sim.Code.MemsetLoaded σ10.mem := by
    rw [hmem10, mem_afterNextPC]
    exact memset_insert_pro _ _ _ (by rw [hoffsb7]; omega) (hmE9 ▸ hms0)

  -- === 0x80006b5c:  ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80006b5c_pm σ10 i10 (c.steps + 10) _ vmi10 (vsp + sign_extend (m := 64) (0x0c8#12)) _
      hG10 hpc10 hmi10 hp10.2.2.1 hp10.2.2.2.2.2.2.2.2.2.2.2.1 hmsA10 rfl (by rw [hoffsb6]; omega) (by rw [hoffsb6]; omega) (by rw [hoffsb6, htoh]; omega) hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 10⟩ ⟨σ11, i11, c.steps + 11⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80006b60#64) := by
    have := obs_store_pc hobs11
    rwa [show BitVec.addInt (0x80006b5c#64) 4 = (0x80006b60#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_store_minstret hobs11
  have hp11 := pins_store hobs11 (by rfl) hp10
  have hmE11 : σ11.mem = ((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64)) := by
    rw [hmem11, mem_afterNextPC, hmE10, hoffsb6]

  have hmsA11 : Vsa.Sim.Code.MemsetLoaded σ11.mem := by
    rw [hmem11, mem_afterNextPC]
    exact memset_insert_pro _ _ _ (by rw [hoffsb6]; omega) hmsA10

  -- === 0x80006b60:  ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80006b60_pm σ11 i11 (c.steps + 11) _ vmi11 (vsp + sign_extend (m := 64) (0x0c8#12)) _
      hG11 hpc11 hmi11 hp11.2.2.1 hp11.2.2.2.2.2.2.2.2.2.2.2.1 hmsA11 rfl (by rw [hoffsb5]; omega) (by rw [hoffsb5]; omega) (by rw [hoffsb5, htoh]; omega) hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 11⟩ ⟨σ12, i12, c.steps + 12⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x80006b64#64) := by
    have := obs_store_pc hobs12
    rwa [show BitVec.addInt (0x80006b60#64) 4 = (0x80006b64#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_store_minstret hobs12
  have hp12 := pins_store hobs12 (by rfl) hp11
  have hmE12 : σ12.mem = (((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64))).insert (vsp.toNat + 205) (stData 1 (0#64)) := by
    rw [hmem12, mem_afterNextPC, hmE11, hoffsb5]

  have hmsA12 : Vsa.Sim.Code.MemsetLoaded σ12.mem := by
    rw [hmem12, mem_afterNextPC]
    exact memset_insert_pro _ _ _ (by rw [hoffsb5]; omega) hmsA11

  -- === 0x80006b64:  ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80006b64_pm σ12 i12 (c.steps + 12) _ vmi12 (vsp + sign_extend (m := 64) (0x0c8#12)) _
      hG12 hpc12 hmi12 hp12.2.2.1 hp12.2.2.2.2.2.2.2.2.2.2.2.1 hmsA12 rfl (by rw [hoffsb4]; omega) (by rw [hoffsb4]; omega) (by rw [hoffsb4, htoh]; omega) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 12⟩ ⟨σ13, i13, c.steps + 13⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80006b68#64) := by
    have := obs_store_pc hobs13
    rwa [show BitVec.addInt (0x80006b64#64) 4 = (0x80006b68#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_store_minstret hobs13
  have hp13 := pins_store hobs13 (by rfl) hp12
  have hmE13 : σ13.mem = ((((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64))).insert (vsp.toNat + 205) (stData 1 (0#64))).insert (vsp.toNat + 204) (stData 1 (0#64)) := by
    rw [hmem13, mem_afterNextPC, hmE12, hoffsb4]

  have hmsA13 : Vsa.Sim.Code.MemsetLoaded σ13.mem := by
    rw [hmem13, mem_afterNextPC]
    exact memset_insert_pro _ _ _ (by rw [hoffsb4]; omega) hmsA12

  -- === 0x80006b68:  ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80006b68_pm σ13 i13 (c.steps + 13) _ vmi13 (vsp + sign_extend (m := 64) (0x0c8#12)) _
      hG13 hpc13 hmi13 hp13.2.2.1 hp13.2.2.2.2.2.2.2.2.2.2.2.1 hmsA13 rfl (by rw [hoffsb3]; omega) (by rw [hoffsb3]; omega) (by rw [hoffsb3, htoh]; omega) hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 13⟩ ⟨σ14, i14, c.steps + 14⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x80006b6c#64) := by
    have := obs_store_pc hobs14
    rwa [show BitVec.addInt (0x80006b68#64) 4 = (0x80006b6c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_store_minstret hobs14
  have hp14 := pins_store hobs14 (by rfl) hp13
  have hmE14 : σ14.mem = (((((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64))).insert (vsp.toNat + 205) (stData 1 (0#64))).insert (vsp.toNat + 204) (stData 1 (0#64))).insert (vsp.toNat + 203) (stData 1 (0#64)) := by
    rw [hmem14, mem_afterNextPC, hmE13, hoffsb3]

  have hmsA14 : Vsa.Sim.Code.MemsetLoaded σ14.mem := by
    rw [hmem14, mem_afterNextPC]
    exact memset_insert_pro _ _ _ (by rw [hoffsb3]; omega) hmsA13

  -- === 0x80006b6c:  ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80006b6c_pm σ14 i14 (c.steps + 14) _ vmi14 (vsp + sign_extend (m := 64) (0x0c8#12)) _
      hG14 hpc14 hmi14 hp14.2.2.1 hp14.2.2.2.2.2.2.2.2.2.2.2.1 hmsA14 rfl (by rw [hoffsb2]; omega) (by rw [hoffsb2]; omega) (by rw [hoffsb2, htoh]; omega) hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 14⟩ ⟨σ15, i15, c.steps + 15⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80006b70#64) := by
    have := obs_store_pc hobs15
    rwa [show BitVec.addInt (0x80006b6c#64) 4 = (0x80006b70#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_store_minstret hobs15
  have hp15 := pins_store hobs15 (by rfl) hp14
  have hmE15 : σ15.mem = ((((((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64))).insert (vsp.toNat + 205) (stData 1 (0#64))).insert (vsp.toNat + 204) (stData 1 (0#64))).insert (vsp.toNat + 203) (stData 1 (0#64))).insert (vsp.toNat + 202) (stData 1 (0#64)) := by
    rw [hmem15, mem_afterNextPC, hmE14, hoffsb2]

  have hmsA15 : Vsa.Sim.Code.MemsetLoaded σ15.mem := by
    rw [hmem15, mem_afterNextPC]
    exact memset_insert_pro _ _ _ (by rw [hoffsb2]; omega) hmsA14

  -- === 0x80006b70:  ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80006b70_pm σ15 i15 (c.steps + 15) _ vmi15 (vsp + sign_extend (m := 64) (0x0c8#12)) _
      hG15 hpc15 hmi15 hp15.2.2.1 hp15.2.2.2.2.2.2.2.2.2.2.2.1 hmsA15 rfl (by rw [hoffsb1]; omega) (by rw [hoffsb1]; omega) (by rw [hoffsb1, htoh]; omega) hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 15⟩ ⟨σ16, i16, c.steps + 16⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x80006b74#64) := by
    have := obs_store_pc hobs16
    rwa [show BitVec.addInt (0x80006b70#64) 4 = (0x80006b74#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_store_minstret hobs16
  have hp16 := pins_store hobs16 (by rfl) hp15
  have hmE16 : σ16.mem = (((((((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64))).insert (vsp.toNat + 205) (stData 1 (0#64))).insert (vsp.toNat + 204) (stData 1 (0#64))).insert (vsp.toNat + 203) (stData 1 (0#64))).insert (vsp.toNat + 202) (stData 1 (0#64))).insert (vsp.toNat + 201) (stData 1 (0#64)) := by
    rw [hmem16, mem_afterNextPC, hmE15, hoffsb1]

  have hmsA16 : Vsa.Sim.Code.MemsetLoaded σ16.mem := by
    rw [hmem16, mem_afterNextPC]
    exact memset_insert_pro _ _ _ (by rw [hoffsb1]; omega) hmsA15

  -- === 0x80006b74:  ===
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_80006b74_pm σ16 i16 (c.steps + 16) _ vmi16 (vsp + sign_extend (m := 64) (0x0c8#12)) _
      hG16 hpc16 hmi16 hp16.2.2.1 hp16.2.2.2.2.2.2.2.2.2.2.2.1 hmsA16 rfl (by rw [hoffsb0]; omega) (by rw [hoffsb0]; omega) (by rw [hoffsb0, htoh]; omega) hi16
  have hstep17 : Step ⟨σ16, i16, c.steps + 16⟩ ⟨σ17, i17, c.steps + 17⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x80006b78#64) := by
    have := obs_store_pc hobs17
    rwa [show BitVec.addInt (0x80006b74#64) 4 = (0x80006b78#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi17, hmi17⟩ := obs_store_minstret hobs17
  have hp17 := pins_store hobs17 (by rfl) hp16
  have hmE17 : σ17.mem = ((((((((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64))).insert (vsp.toNat + 205) (stData 1 (0#64))).insert (vsp.toNat + 204) (stData 1 (0#64))).insert (vsp.toNat + 203) (stData 1 (0#64))).insert (vsp.toNat + 202) (stData 1 (0#64))).insert (vsp.toNat + 201) (stData 1 (0#64))).insert (vsp.toNat + 200) (stData 1 (0#64)) := by
    rw [hmem17, mem_afterNextPC, hmE16, hoffsb0]

  have hmsA17 : Vsa.Sim.Code.MemsetLoaded σ17.mem := by
    rw [hmem17, mem_afterNextPC]
    exact memset_insert_pro _ _ _ (by rw [hoffsb0]; omega) hmsA16

  -- === 0x80006b78: ret (memset done) ===
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_80006b78_pm σ17 i17 (c.steps + 17) _ vmi17 (0x800076a4#64)
      hG17 hpc17 hmi17 hp17.2.2.2.2.1 hmsA17 rfl (by rw [ret_tgt _ (by decide)]; decide) hi17
  have hstep18 : Step ⟨σ17, i17, c.steps + 17⟩ ⟨σ18, i18, c.steps + 18⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x800076a4#64) := by
    have := obs_jr_pc hobs18
    rwa [ret_tgt _ (by decide)] at this
  obtain ⟨vmi18, hmi18⟩ := obs_jr_minstret hobs18
  have hp18 := pins_jr hobs18 (by rfl) hp17
  have hmE18 : σ18.mem = ((((((((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64))).insert (vsp.toNat + 205) (stData 1 (0#64))).insert (vsp.toNat + 204) (stData 1 (0#64))).insert (vsp.toNat + 203) (stData 1 (0#64))).insert (vsp.toNat + 202) (stData 1 (0#64))).insert (vsp.toNat + 201) (stData 1 (0#64))).insert (vsp.toNat + 200) (stData 1 (0#64)) := hmem18.trans hmE17

  have hslA : Vsa.Sim.Code.SvfprintfSliceLoaded σ18.mem := by
    rw [hmE18]
    exact svfprintfSlice_insert_sn4 _ _ _ (by omega) (svfprintfSlice_insert_sn4 _ _ _
      (by omega) (svfprintfSlice_insert_sn4 _ _ _ (by omega)
      (svfprintfSlice_insert_sn4 _ _ _ (by omega) (svfprintfSlice_insert_sn4 _ _ _
      (by omega) (svfprintfSlice_insert_sn4 _ _ _ (by omega)
      (svfprintfSlice_insert_sn4 _ _ _ (by omega) (svfprintfSlice_insert_sn4 _ _ _
      (by omega) hsl0)))))))
  have hagA : ∀ a : Nat, vsp.toNat + 592 ≤ a → σ18.mem[a]? = c.σ.mem[a]? := by
    intro a ha
    rw [hmE18,
      getElem_insert_ne _ a (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 201) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 202) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 203) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 204) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 205) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 206) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 207) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

  -- === 0x800076a4: lhu a5,16(s1) — FILE _flags ===
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_800076a4_pr4 σ18 i18 (c.steps + 18) _ vmi18 vfile _ _
      hG18 hpc18 hmi18 hp18.2.2.2.2.2.2.2.2.1 hslA rfl (by rw [hoafl]; omega) (by rw [hoafl]; omega) (by rw [hoafl, htoh]; omega) (by rw [hoafl]; omega) (by rw [hoafl]; exact (hagA _ (by omega)).trans hfl0B) (by rw [hoafl]; exact (hagA _ (by omega)).trans hfl1B) hi18
  have hstep19 : Step ⟨σ18, i18, c.steps + 18⟩ ⟨σ19, i19, c.steps + 19⟩ := hs19
  have hpc19 : σ19.regs.get? Register.PC = some (0x800076a8#64) := by
    have := obs_alu_pc hobs19
    rwa [show BitVec.addInt (0x800076a4#64) 4 = (0x800076a8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi19, hmi19⟩ := obs_alu_minstret hobs19
  have hrd19 : σ19.regs.get? Register.x15 = some (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2))) :=
    obs_alu_rd hobs19 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp19 := pins_cons_pro hrd19 (pins_alu hobs19 (by rfl) hp18)
  have hmE19 : σ19.mem = ((((((((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64))).insert (vsp.toNat + 205) (stData 1 (0#64))).insert (vsp.toNat + 204) (stData 1 (0#64))).insert (vsp.toNat + 203) (stData 1 (0#64))).insert (vsp.toNat + 202) (stData 1 (0#64))).insert (vsp.toNat + 201) (stData 1 (0#64))).insert (vsp.toNat + 200) (stData 1 (0#64)) := hmem19.trans hmE18

  -- === 0x800076a8: andi a5,a5,128 — __SCLE clear ===
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_800076a8_pr4 σ19 i19 (c.steps + 19) _ vmi19 (zero_extend (m := 64) ((fl1.append fl0) : BitVec (8 * 2)))
      hG19 hpc19 hmi19 hp19.1 (hmem19 ▸ hslA) rfl hi19
  have hstep20 : Step ⟨σ19, i19, c.steps + 19⟩ ⟨σ20, i20, c.steps + 20⟩ := hs20
  have hpc20 : σ20.regs.get? Register.PC = some (0x800076ac#64) := by
    have := obs_alu_pc hobs20
    rwa [show BitVec.addInt (0x800076a8#64) 4 = (0x800076ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi20, hmi20⟩ := obs_alu_minstret hobs20
  have hrd20 : σ20.regs.get? Register.x15 = some ((0#64)) := by
    have := obs_alu_rd hobs20 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hflagB] at this
  have hp20 := pins_cons_pro hrd20 (pins_alu hobs20 (by rfl) hp19.2)
  have hmE20 : σ20.mem = ((((((((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64))).insert (vsp.toNat + 205) (stData 1 (0#64))).insert (vsp.toNat + 204) (stData 1 (0#64))).insert (vsp.toNat + 203) (stData 1 (0#64))).insert (vsp.toNat + 202) (stData 1 (0#64))).insert (vsp.toNat + 201) (stData 1 (0#64))).insert (vsp.toNat + 200) (stData 1 (0#64)) := hmem20.trans hmE19

  -- === 0x800076ac: beqz a5 TAKEN → 0x800076bc ===
  obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
    site_800076ac_taken_pr σ20 i20 (c.steps + 20) _ vmi20 (0#64)
      hG20 hpc20 hmi20 hp20.1 ((hmem20.trans hmem19) ▸ hslA) rfl (by decide) hi20
  have hstep21 : Step ⟨σ20, i20, c.steps + 20⟩ ⟨σ21, i21, c.steps + 21⟩ := hs21
  have hpc21 : σ21.regs.get? Register.PC = some (0x800076bc#64) := by
    have := obs_btaken_pc hobs21
    rwa [site_800076ac_taken_pr_tgt] at this
  obtain ⟨vmi21, hmi21⟩ := obs_btaken_minstret hobs21
  have hp21 := pins_btaken hobs21 (by rfl) hp20
  have hmE21 : σ21.mem = ((((((((c.σ.mem).insert (vsp.toNat + 207) (stData 1 (0#64))).insert (vsp.toNat + 206) (stData 1 (0#64))).insert (vsp.toNat + 205) (stData 1 (0#64))).insert (vsp.toNat + 204) (stData 1 (0#64))).insert (vsp.toNat + 203) (stData 1 (0#64))).insert (vsp.toNat + 202) (stData 1 (0#64))).insert (vsp.toNat + 201) (stData 1 (0#64))).insert (vsp.toNat + 200) (stData 1 (0#64)) := hmem21.trans hmE20

  have hslN : Vsa.Sim.Code.SvfprintfSliceLoaded σ21.mem :=
    (hmem21.trans (hmem20.trans hmem19)) ▸ hslA
  have hmsN : Vsa.Sim.Code.MemsetLoaded σ21.mem := by
    rw [hmem21, hmem20, hmem19, hmem18]; exact hmsA17
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ21.mem := by
    rw [hmE21]
    exact localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
      (localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
      (localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
      (localemb_insert_pro _ _ _ (by omega) (localemb_insert_pro _ _ _ (by omega)
        hlm0)))))))
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ21.mem := by
    rw [hmE21]
    exact amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
      (amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
      (amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
      (amb_insert_pro _ _ _ (by omega) (amb_insert_pro _ _ _ (by omega)
        hamb0)))))))
  have hz200 : σ21.mem[vsp.toNat + 200]? = some (0x00#8) := by
    rw [hmE21, getElem_insert_self]
    rfl
  have hz201 : σ21.mem[vsp.toNat + 201]? = some (0x00#8) := by
    rw [hmE21,
      getElem_insert_ne _ (vsp.toNat + 201) (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self]
    rfl
  have hz202 : σ21.mem[vsp.toNat + 202]? = some (0x00#8) := by
    rw [hmE21,
      getElem_insert_ne _ (vsp.toNat + 202) (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 202) (vsp.toNat + 201) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self]
    rfl
  have hz203 : σ21.mem[vsp.toNat + 203]? = some (0x00#8) := by
    rw [hmE21,
      getElem_insert_ne _ (vsp.toNat + 203) (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 203) (vsp.toNat + 201) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 203) (vsp.toNat + 202) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self]
    rfl
  have hz204 : σ21.mem[vsp.toNat + 204]? = some (0x00#8) := by
    rw [hmE21,
      getElem_insert_ne _ (vsp.toNat + 204) (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 204) (vsp.toNat + 201) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 204) (vsp.toNat + 202) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 204) (vsp.toNat + 203) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self]
    rfl
  have hz205 : σ21.mem[vsp.toNat + 205]? = some (0x00#8) := by
    rw [hmE21,
      getElem_insert_ne _ (vsp.toNat + 205) (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 205) (vsp.toNat + 201) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 205) (vsp.toNat + 202) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 205) (vsp.toNat + 203) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 205) (vsp.toNat + 204) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self]
    rfl
  have hz206 : σ21.mem[vsp.toNat + 206]? = some (0x00#8) := by
    rw [hmE21,
      getElem_insert_ne _ (vsp.toNat + 206) (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 206) (vsp.toNat + 201) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 206) (vsp.toNat + 202) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 206) (vsp.toNat + 203) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 206) (vsp.toNat + 204) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 206) (vsp.toNat + 205) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self]
    rfl
  have hz207 : σ21.mem[vsp.toNat + 207]? = some (0x00#8) := by
    rw [hmE21,
      getElem_insert_ne _ (vsp.toNat + 207) (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 207) (vsp.toNat + 201) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 207) (vsp.toNat + 202) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 207) (vsp.toNat + 203) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 207) (vsp.toNat + 204) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 207) (vsp.toNat + 205) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ (vsp.toNat + 207) (vsp.toNat + 206) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_self]
    rfl
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 200 ≤ a ∧ a < vsp.toNat + 208) →
      σ21.mem[a]? = c.σ.mem[a]? := by
    intro a hw0
    rw [hmE21,
      getElem_insert_ne _ a (vsp.toNat + 200) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 201) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 202) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 203) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 204) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 205) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 206) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
      getElem_insert_ne _ a (vsp.toNat + 207) _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]
  refine ⟨⟨σ21, i21, c.steps + 21⟩, ?_,
    hG21,
    hpc21,
    hp21.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hz200,
    hz201,
    hz202,
    hz203,
    hz204,
    hz205,
    hz206,
    hz207,
    hagN,
    hslN,
    hmsN,
    hlmN,
    hambN,
    hi21,
    ⟨vmi21, hmi21⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans ((Steps.single hstep19).trans ((Steps.single hstep20).trans (Steps.single hstep21))))))))))))))))))))

end Vsa.Sim
