import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.StrlenSites
import Vsa.Sim.StrlenSpec

/-!
# M3 Layer-3 — `SnprintfSpec28` : svfprintf prologue segment B
## `0x8000768c` (the `jal strlen`) → `0x800076a0` (the `jal memset`)

`strlen(decimal_point)` for the concrete static string `"."` at `0x80019770`
(from `_localeconv_r`), fully inlined (22 `StrlenSites` steps: aligned entry,
one magic word probe, byte tail, exit `a0 = 1`), the result spill to `sp+72`,
and the `memset(sp+200, 0, 8)` argument setup.
Generated in the SnprintfSpec22 house style by /tmp/gen_spec28.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **Segment B of the svfprintf prologue**: `0x8000768c → 0x800076a0`.

The `jal strlen` with the whole concrete `strlen(".")` execution inlined
(aligned word probe of the static decimal-point string at `0x80019770`,
magic-constant NUL detection, byte-tail exit at `0x80006d94`, result `1`),
the spill of the result to `sp+72`, and the `memset` argument setup
(`a2 := 8`, `a0 := sp+200`, `a1 := 0`); stops poised at the `jal memset`. -/
theorem svfProB_spec
    (vsp va0 vfile vfmt : BitVec 64)
    (vS2o vS3o vS4o vS5o vS7o vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hstr0 : Vsa.Sim.Code.StrlenLoaded c.σ.mem)
    (hms0 : Vsa.Sim.Code.MemsetLoaded c.σ.mem)
    (hlm0 : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x8000768c#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some vfile)
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx10 : c.σ.regs.get? Register.x10 = some (0x80019770#64))
    (hx18 : c.σ.regs.get? Register.x18 = some vS2o)
    (hx19 : c.σ.regs.get? Register.x19 = some vS3o)
    (hx20 : c.σ.regs.get? Register.x20 = some vS4o)
    (hx21 : c.σ.regs.get? Register.x21 = some vS5o)
    (hx23 : c.σ.regs.get? Register.x23 = some vS7o)
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    -- the static "." decimal-point string bytes at 0x80019770
    (hdb0 : c.σ.mem[(0x80019770 : Nat)]? = some (0x2e#8))
    (hdb1 : c.σ.mem[(0x80019770 : Nat) + 1]? = some (0x00#8))
    (hdb2 : c.σ.mem[(0x80019770 : Nat) + 2]? = some (0x00#8))
    (hdb3 : c.σ.mem[(0x80019770 : Nat) + 3]? = some (0x00#8))
    (hdb4 : c.σ.mem[(0x80019770 : Nat) + 4]? = some (0x00#8))
    (hdb5 : c.σ.mem[(0x80019770 : Nat) + 5]? = some (0x00#8))
    (hdb6 : c.σ.mem[(0x80019770 : Nat) + 6]? = some (0x00#8))
    (hdb7 : c.σ.mem[(0x80019770 : Nat) + 7]? = some (0x00#8))
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x800076a0#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x1 = some (0x80007690#64) ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some vfile ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x10 = some (vsp + sign_extend (m := 64) (0x0c8#12)) ∧
      c'.σ.regs.get? Register.x11 = some (0#64) ∧
      c'.σ.regs.get? Register.x12 = some (8#64) ∧
      c'.σ.regs.get? Register.x18 = some vS2o ∧
      c'.σ.regs.get? Register.x19 = some vS3o ∧
      c'.σ.regs.get? Register.x20 = some vS4o ∧
      c'.σ.regs.get? Register.x21 = some vS5o ∧
      c'.σ.regs.get? Register.x23 = some vS7o ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      SlotHolds vsp 0x048 (1#64) c'.σ.mem ∧
      (∀ a : Nat, ¬(vsp.toNat + 72 ≤ a ∧ a < vsp.toNat + 80) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.MemsetLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoff72 : (vsp + sign_extend (m := 64) (0x048#12)).toNat = vsp.toNat + 72 :=
    ptr_addoff vsp _ 72 (by decide) (by omega)
  have hoffdb : ((0x80019770#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat
      = (0x80019770 : Nat) := by decide
  have hoffm8 : ((0x80019778#64 : BitVec 64) + sign_extend (m := 64) (0xff8#12)).toNat
      = (0x80019770 : Nat) := by decide
  have hoffm7 : ((0x80019778#64 : BitVec 64) + sign_extend (m := 64) (0xff9#12)).toNat
      = (0x80019770 : Nat) + 1 := by decide
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp⟩, ⟨Register.x3, (0x8001b510#64)⟩, ⟨Register.x8, va0⟩, ⟨Register.x9, vfile⟩, ⟨Register.x22, vfmt⟩, ⟨Register.x10, (0x80019770#64)⟩, ⟨Register.x18, vS2o⟩, ⟨Register.x19, vS3o⟩, ⟨Register.x20, vS4o⟩, ⟨Register.x21, vS5o⟩, ⟨Register.x23, vS7o⟩, ⟨Register.x24, vS8o⟩, ⟨Register.x25, vS9o⟩, ⟨Register.x26, vS10o⟩, ⟨Register.x27, vS11o⟩] :=
    ⟨hx2, hx3, hx8, hx9, hx22, hx10, hx18, hx19, hx20, hx21, hx23, hx24, hx25, hx26, hx27, trivial⟩
  -- === 0x8000768c: jal strlen ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_8000768c_pr c.σ c.tick c.steps _ vmi0
      hG hpc hmi0 hsl0 rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006cf0#64) := by
    have := obs_jal_pc hobs1
    rwa [show (0x8000768c#64 : BitVec 64) + sign_extend (m := 64) (0x1ff664#21) = (0x80006cf0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_jal_minstret hobs1
  have hrd1 : σ1.regs.get? Register.x1 = some ((0x80007690#64)) := by
    have := obs_jal_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x8000768c#64) 4 = (0x80007690#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp1 := pins_cons_pro hrd1 (pins_jal hobs1 (by rfl) hp0)
  have hmE1 : σ1.mem = c.σ.mem := hmem1

  -- === 0x80006cf0: andi a5,a0,7 (aligned) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006cf0 σ1 i1 (c.steps + 1) _ vmi1 (0x80019770#64)
      hG1 hpc1 hmi1 hp1.2.2.2.2.2.2.1 (hmE1 ▸ hstr0) rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 2⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006cf4#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80006cf0#64) 4 = (0x80006cf4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hrd2 : σ2.regs.get? Register.x15 = some ((0#64)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x80019770#64 : BitVec 64) &&& sign_extend (m := 64) (0x007#12) = (0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp2 := pins_cons_pro hrd2 (pins_alu hobs2 (by rfl) hp1)
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1

  -- === 0x80006cf4: mv a4,a0 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006cf4 σ2 i2 (c.steps + 2) _ vmi2 (0x80019770#64)
      hG2 hpc2 hmi2 hp2.2.2.2.2.2.2.2.1 (hmE2 ▸ hstr0) rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 2⟩ ⟨σ3, i3, c.steps + 3⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006cf8#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80006cf4#64) 4 = (0x80006cf8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hrd3 : σ3.regs.get? Register.x14 = some ((0x80019770#64)) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro (0x80019770#64)] at this
  have hp3 := pins_cons_pro hrd3 (pins_alu hobs3 (by rfl) hp2)
  have hmE3 : σ3.mem = c.σ.mem := hmem3.trans hmE2

  -- === 0x80006cf8: bnez a5 NOT taken ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006cf8_nottaken σ3 i3 (c.steps + 3) _ vmi3 (0#64)
      hG3 hpc3 hmi3 hp3.2.1 (hmE3 ▸ hstr0) rfl (by decide) hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 3⟩ ⟨σ4, i4, c.steps + 4⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006cfc#64) := by
    have := obs_bnottaken_pc hobs4
    rwa [show BitVec.addInt (0x80006cf8#64) 4 = (0x80006cfc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_bnottaken_minstret hobs4
  have hp4 := pins_bnottaken hobs4 (by rfl) hp3
  have hmE4 : σ4.mem = c.σ.mem := hmem4.trans hmE3

  -- === 0x80006cfc: lui a5,0x7f7f8 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006cfc σ4 i4 (c.steps + 4) _ vmi4
      hG4 hpc4 hmi4 (hmE4 ▸ hstr0) rfl hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 4⟩ ⟨σ5, i5, c.steps + 5⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006d00#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80006cfc#64) 4 = (0x80006d00#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hrd5 : σ5.regs.get? Register.x15 = some ((0x7f7f8000#64)) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12) : BitVec 64) = (0x7f7f8000#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp5 := pins_cons_pro hrd5 (pins_alu hobs5 (by rfl) (pins_drop2_pro hp4))
  have hmE5 : σ5.mem = c.σ.mem := hmem5.trans hmE4

  -- === 0x80006d00: addi a5,a5,-129 (magic lo) ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006d00 σ5 i5 (c.steps + 5) _ vmi5 (0x7f7f8000#64)
      hG5 hpc5 hmi5 hp5.1 (hmE5 ▸ hstr0) rfl hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 5⟩ ⟨σ6, i6, c.steps + 6⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006d04#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80006d00#64) 4 = (0x80006d04#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hrd6 : σ6.regs.get? Register.x15 = some ((0x7f7f7f7f#64)) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x7f7f8000#64 : BitVec 64) + sign_extend (m := 64) (0xf7f#12) = (0x7f7f7f7f#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp6 := pins_cons_pro hrd6 (pins_alu hobs6 (by rfl) hp5.2)
  have hmE6 : σ6.mem = c.σ.mem := hmem6.trans hmE5

  -- === 0x80006d04: slli a3,a5,0x20 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006d04 σ6 i6 (c.steps + 6) _ vmi6 (0x7f7f7f7f#64)
      hG6 hpc6 hmi6 hp6.1 (hmE6 ▸ hstr0) rfl hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 7⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006d08#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80006d04#64) 4 = (0x80006d08#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hrd7 : σ7.regs.get? Register.x13 = some ((0x7f7f7f7f00000000#64)) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show shift_bits_left (0x7f7f7f7f#64 : BitVec 64) (Sail.BitVec.extractLsb (0x20#6) 5 0) = (0x7f7f7f7f00000000#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp7 := pins_cons_pro hrd7 (pins_alu hobs7 (by rfl) hp6)
  have hmE7 : σ7.mem = c.σ.mem := hmem7.trans hmE6

  -- === 0x80006d08: add a3,a3,a5 (magic) ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006d08 σ7 i7 (c.steps + 7) _ vmi7 (0x7f7f7f7f00000000#64) (0x7f7f7f7f#64)
      hG7 hpc7 hmi7 hp7.1 hp7.2.1 (hmE7 ▸ hstr0) rfl hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 7⟩ ⟨σ8, i8, c.steps + 8⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006d0c#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80006d08#64) 4 = (0x80006d0c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hrd8 : σ8.regs.get? Register.x13 = some ((0x7f7f7f7f7f7f7f7f#64)) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x7f7f7f7f00000000#64 : BitVec 64) + (0x7f7f7f7f#64) = (0x7f7f7f7f7f7f7f7f#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp8 := pins_cons_pro hrd8 (pins_alu hobs8 (by rfl) hp7.2)
  have hmE8 : σ8.mem = c.σ.mem := hmem8.trans hmE7

  -- === 0x80006d0c: li a1,-1 ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80006d0c σ8 i8 (c.steps + 8) _ vmi8
      hG8 hpc8 hmi8 (hmE8 ▸ hstr0) rfl hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 8⟩ ⟨σ9, i9, c.steps + 9⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80006d10#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x80006d0c#64) 4 = (0x80006d10#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hrd9 : σ9.regs.get? Register.x11 = some ((0xffffffffffffffff#64)) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) : BitVec 64) + sign_extend (m := 64) (0xfff#12) = (0xffffffffffffffff#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp9 := pins_cons_pro hrd9 (pins_alu hobs9 (by rfl) hp8)
  have hmE9 : σ9.mem = c.σ.mem := hmem9.trans hmE8

  -- === 0x80006d10: ld a2,0(a4) — total word load of ". \0…" ===
  have hldval : (sign_extend (m := 64) (ldBytesT (afterNextPC (afterPrelude σ9) (0x80006d10#64)) ((0x80019770#64) + sign_extend (m := 64) (0x000#12))) : BitVec 64) = (0x2e#64) := by
    rw [ldBytesT_wordAt, mem_afterNextPC, hoffdb]
    unfold strlenWordAt
    rw [hmE9, hdb0, hdb1, hdb2, hdb3, hdb4, hdb5, hdb6, hdb7]
    simp only [Option.getD_some]
    apply BitVec.eq_of_toNat_eq; decide
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80006d10 σ9 i9 (c.steps + 9) _ vmi9 (0x80019770#64)
      hG9 hpc9 hmi9 hp9.2.2.2.1 (hmE9 ▸ hstr0) rfl (by rw [hoffdb]; omega) (by rw [hoffdb]; omega) (by rw [hoffdb, htoh]; omega) (by rw [hoffdb]) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 9⟩ ⟨σ10, i10, c.steps + 10⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80006d14#64) := by
    have := obs_alu_pc hobs10
    rwa [show BitVec.addInt (0x80006d10#64) 4 = (0x80006d14#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_alu_minstret hobs10
  have hrd10 : σ10.regs.get? Register.x12 = some ((0x2e#64)) := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hldval] at this
  have hp10 := pins_cons_pro hrd10 (pins_alu hobs10 (by rfl) hp9)
  have hmE10 : σ10.mem = c.σ.mem := hmem10.trans hmE9

  -- === 0x80006d14: addi a4,a4,8 ===
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80006d14 σ10 i10 (c.steps + 10) _ vmi10 (0x80019770#64)
      hG10 hpc10 hmi10 hp10.2.2.2.2.1 (hmE10 ▸ hstr0) rfl hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 10⟩ ⟨σ11, i11, c.steps + 11⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80006d18#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x80006d14#64) 4 = (0x80006d18#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hrd11 : σ11.regs.get? Register.x14 = some ((0x80019778#64)) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x80019770#64 : BitVec 64) + sign_extend (m := 64) (0x008#12) = (0x80019778#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp11 := pins_cons_pro hrd11 (pins_alu hobs11 (by rfl) (pins_drop5_pro hp10))
  have hmE11 : σ11.mem = c.σ.mem := hmem11.trans hmE10

  -- === 0x80006d18: and a5,a2,a3 ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80006d18 σ11 i11 (c.steps + 11) _ vmi11 (0x2e#64) (0x7f7f7f7f7f7f7f7f#64)
      hG11 hpc11 hmi11 hp11.2.1 hp11.2.2.2.1 (hmE11 ▸ hstr0) rfl hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 11⟩ ⟨σ12, i12, c.steps + 12⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x80006d1c#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80006d18#64) 4 = (0x80006d1c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hrd12 : σ12.regs.get? Register.x15 = some ((0x2e#64)) := by
    have := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x2e#64 : BitVec 64) &&& (0x7f7f7f7f7f7f7f7f#64) = (0x2e#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp12 := pins_cons_pro hrd12 (pins_alu hobs12 (by rfl) (pins_drop5_pro hp11))
  have hmE12 : σ12.mem = c.σ.mem := hmem12.trans hmE11

  -- === 0x80006d1c: add a5,a5,a3 ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80006d1c σ12 i12 (c.steps + 12) _ vmi12 (0x2e#64) (0x7f7f7f7f7f7f7f7f#64)
      hG12 hpc12 hmi12 hp12.1 hp12.2.2.2.2.1 (hmE12 ▸ hstr0) rfl hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 12⟩ ⟨σ13, i13, c.steps + 13⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80006d20#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x80006d1c#64) 4 = (0x80006d20#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hrd13 : σ13.regs.get? Register.x15 = some ((0x7f7f7f7f7f7f7fad#64)) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x2e#64 : BitVec 64) + (0x7f7f7f7f7f7f7f7f#64) = (0x7f7f7f7f7f7f7fad#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp13 := pins_cons_pro hrd13 (pins_alu hobs13 (by rfl) hp12.2)
  have hmE13 : σ13.mem = c.σ.mem := hmem13.trans hmE12

  -- === 0x80006d20: or a5,a5,a2 ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80006d20 σ13 i13 (c.steps + 13) _ vmi13 (0x7f7f7f7f7f7f7fad#64) (0x2e#64)
      hG13 hpc13 hmi13 hp13.1 hp13.2.2.1 (hmE13 ▸ hstr0) rfl hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 13⟩ ⟨σ14, i14, c.steps + 14⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x80006d24#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x80006d20#64) 4 = (0x80006d24#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hrd14 : σ14.regs.get? Register.x15 = some ((0x7f7f7f7f7f7f7faf#64)) := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x7f7f7f7f7f7f7fad#64 : BitVec 64) ||| (0x2e#64) = (0x7f7f7f7f7f7f7faf#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp14 := pins_cons_pro hrd14 (pins_alu hobs14 (by rfl) hp13.2)
  have hmE14 : σ14.mem = c.σ.mem := hmem14.trans hmE13

  -- === 0x80006d24: or a5,a5,a3 ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_80006d24 σ14 i14 (c.steps + 14) _ vmi14 (0x7f7f7f7f7f7f7faf#64) (0x7f7f7f7f7f7f7f7f#64)
      hG14 hpc14 hmi14 hp14.1 hp14.2.2.2.2.1 (hmE14 ▸ hstr0) rfl hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 14⟩ ⟨σ15, i15, c.steps + 15⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80006d28#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80006d24#64) 4 = (0x80006d28#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hrd15 : σ15.regs.get? Register.x15 = some ((0x7f7f7f7f7f7f7fff#64)) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x7f7f7f7f7f7f7faf#64 : BitVec 64) ||| (0x7f7f7f7f7f7f7f7f#64) = (0x7f7f7f7f7f7f7fff#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp15 := pins_cons_pro hrd15 (pins_alu hobs15 (by rfl) hp14.2)
  have hmE15 : σ15.mem = c.σ.mem := hmem15.trans hmE14

  -- === 0x80006d28: beq a5,a1 NOT taken (NUL present) ===
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80006d28_nottaken σ15 i15 (c.steps + 15) _ vmi15 (0x7f7f7f7f7f7f7fff#64) (0xffffffffffffffff#64)
      hG15 hpc15 hmi15 hp15.1 hp15.2.2.2.1 (hmE15 ▸ hstr0) rfl (by decide) hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 15⟩ ⟨σ16, i16, c.steps + 16⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x80006d2c#64) := by
    have := obs_bnottaken_pc hobs16
    rwa [show BitVec.addInt (0x80006d28#64) 4 = (0x80006d2c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_bnottaken_minstret hobs16
  have hp16 := pins_bnottaken hobs16 (by rfl) hp15
  have hmE16 : σ16.mem = c.σ.mem := hmem16.trans hmE15

  -- === 0x80006d2c: lbu a5,-8(a4) — byte 0 = '.' ===
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_80006d2c σ16 i16 (c.steps + 16) _ vmi16 (0x80019778#64) _
      hG16 hpc16 hmi16 hp16.2.1 (hmE16 ▸ hstr0) rfl (by rw [hoffm8]; omega) (by rw [hoffm8]; omega) (by rw [hoffm8, htoh]; omega) (by rw [hoffm8, hmE16]; exact hdb0) hi16
  have hstep17 : Step ⟨σ16, i16, c.steps + 16⟩ ⟨σ17, i17, c.steps + 17⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x80006d30#64) := by
    have := obs_alu_pc hobs17
    rwa [show BitVec.addInt (0x80006d2c#64) 4 = (0x80006d30#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi17, hmi17⟩ := obs_alu_minstret hobs17
  have hrd17 : σ17.regs.get? Register.x15 = some ((0x2e#64)) := by
    have := obs_alu_rd hobs17 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (zero_extend (m := 64) (0x2e#8) : BitVec 64) = (0x2e#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp17 := pins_cons_pro hrd17 (pins_alu hobs17 (by rfl) hp16.2)
  have hmE17 : σ17.mem = c.σ.mem := hmem17.trans hmE16

  -- === 0x80006d30: sub a3,a4,a0 ===
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_80006d30 σ17 i17 (c.steps + 17) _ vmi17 (0x80019778#64) (0x80019770#64)
      hG17 hpc17 hmi17 hp17.2.1 hp17.2.2.2.2.2.2.2.2.2.2.2.1 (hmE17 ▸ hstr0) rfl hi17
  have hstep18 : Step ⟨σ17, i17, c.steps + 17⟩ ⟨σ18, i18, c.steps + 18⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x80006d34#64) := by
    have := obs_alu_pc hobs18
    rwa [show BitVec.addInt (0x80006d30#64) 4 = (0x80006d34#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi18, hmi18⟩ := obs_alu_minstret hobs18
  have hrd18 : σ18.regs.get? Register.x13 = some ((8#64)) := by
    have := obs_alu_rd hobs18 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0x80019778#64 : BitVec 64) - (0x80019770#64) = (8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp18 := pins_cons_pro hrd18 (pins_alu hobs18 (by rfl) (pins_drop5_pro hp17))
  have hmE18 : σ18.mem = c.σ.mem := hmem18.trans hmE17

  -- === 0x80006d34: beqz a5 NOT taken ('.' ≠ 0) ===
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_80006d34_nottaken σ18 i18 (c.steps + 18) _ vmi18 (0x2e#64)
      hG18 hpc18 hmi18 hp18.2.1 (hmE18 ▸ hstr0) rfl (by decide) hi18
  have hstep19 : Step ⟨σ18, i18, c.steps + 18⟩ ⟨σ19, i19, c.steps + 19⟩ := hs19
  have hpc19 : σ19.regs.get? Register.PC = some (0x80006d38#64) := by
    have := obs_bnottaken_pc hobs19
    rwa [show BitVec.addInt (0x80006d34#64) 4 = (0x80006d38#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi19, hmi19⟩ := obs_bnottaken_minstret hobs19
  have hp19 := pins_bnottaken hobs19 (by rfl) hp18
  have hmE19 : σ19.mem = c.σ.mem := hmem19.trans hmE18

  -- === 0x80006d38: lbu a5,-7(a4) — the NUL ===
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_80006d38 σ19 i19 (c.steps + 19) _ vmi19 (0x80019778#64) _
      hG19 hpc19 hmi19 hp19.2.2.1 (hmE19 ▸ hstr0) rfl (by rw [hoffm7]; omega) (by rw [hoffm7]; omega) (by rw [hoffm7, htoh]; omega) (by rw [hoffm7, hmE19]; exact hdb1) hi19
  have hstep20 : Step ⟨σ19, i19, c.steps + 19⟩ ⟨σ20, i20, c.steps + 20⟩ := hs20
  have hpc20 : σ20.regs.get? Register.PC = some (0x80006d3c#64) := by
    have := obs_alu_pc hobs20
    rwa [show BitVec.addInt (0x80006d38#64) 4 = (0x80006d3c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi20, hmi20⟩ := obs_alu_minstret hobs20
  have hrd20 : σ20.regs.get? Register.x15 = some ((0#64)) := by
    have := obs_alu_rd hobs20 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (zero_extend (m := 64) (0x00#8) : BitVec 64) = (0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp20 := pins_cons_pro hrd20 (pins_alu hobs20 (by rfl) (pins_drop2_pro hp19))
  have hmE20 : σ20.mem = c.σ.mem := hmem20.trans hmE19

  -- === 0x80006d3c: beqz a5 TAKEN → byte-1 exit ===
  obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
    site_80006d3c_taken σ20 i20 (c.steps + 20) _ vmi20 (0#64)
      hG20 hpc20 hmi20 hp20.1 (hmE20 ▸ hstr0) rfl (by decide) hi20
  have hstep21 : Step ⟨σ20, i20, c.steps + 20⟩ ⟨σ21, i21, c.steps + 21⟩ := hs21
  have hpc21 : σ21.regs.get? Register.PC = some (0x80006d94#64) := by
    have := obs_btaken_pc hobs21
    rwa [show (0x80006d3c#64 : BitVec 64) + sign_extend (m := 64) (0x0058#13) = (0x80006d94#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi21, hmi21⟩ := obs_btaken_minstret hobs21
  have hp21 := pins_btaken hobs21 (by rfl) hp20
  have hmE21 : σ21.mem = c.σ.mem := hmem21.trans hmE20

  -- === 0x80006d94: addi a0,a3,-7 — strlen(".") = 1 ===
  obtain ⟨σ22, i22, hs22, hi22, hG22, hmem22, hobs22⟩ :=
    site_80006d94 σ21 i21 (c.steps + 21) _ vmi21 (8#64)
      hG21 hpc21 hmi21 hp21.2.1 (hmE21 ▸ hstr0) rfl hi21
  have hstep22 : Step ⟨σ21, i21, c.steps + 21⟩ ⟨σ22, i22, c.steps + 22⟩ := hs22
  have hpc22 : σ22.regs.get? Register.PC = some (0x80006d98#64) := by
    have := obs_alu_pc hobs22
    rwa [show BitVec.addInt (0x80006d94#64) 4 = (0x80006d98#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi22, hmi22⟩ := obs_alu_minstret hobs22
  have hrd22 : σ22.regs.get? Register.x10 = some ((1#64)) := by
    have := obs_alu_rd hobs22 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (8#64 : BitVec 64) + sign_extend (m := 64) (0xff9#12) = (1#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp22 := pins_cons_pro hrd22 (pins_alu hobs22 (by rfl) (pins_drop12_pro hp21))
  have hmE22 : σ22.mem = c.σ.mem := hmem22.trans hmE21

  -- === 0x80006d98: ret (back to 0x80007690) ===
  obtain ⟨σ23, i23, hs23, hi23, hG23, hmem23, hobs23⟩ :=
    site_80006d98 σ22 i22 (c.steps + 22) _ vmi22 (0x80007690#64)
      hG22 hpc22 hmi22 hp22.2.2.2.2.2.2.1 (hmE22 ▸ hstr0) rfl (by rw [ret_tgt _ (by decide)]; decide) hi22
  have hstep23 : Step ⟨σ22, i22, c.steps + 22⟩ ⟨σ23, i23, c.steps + 23⟩ := hs23
  have hpc23 : σ23.regs.get? Register.PC = some (0x80007690#64) := by
    have := obs_jr_pc hobs23
    rwa [ret_tgt _ (by decide)] at this
  obtain ⟨vmi23, hmi23⟩ := obs_jr_minstret hobs23
  have hp23 := pins_jr hobs23 (by rfl) hp22
  have hmE23 : σ23.mem = c.σ.mem := hmem23.trans hmE22

  -- === 0x80007690: sd a0,72(sp) — strlen result spill ===
  obtain ⟨σ24, i24, hs24, hi24, hG24, hmem24, hobs24⟩ :=
    site_80007690_pr σ23 i23 (c.steps + 23) _ vmi23 vsp _
      hG23 hpc23 hmi23 hp23.2.2.2.2.2.2.2.1 hp23.1 (hmE23 ▸ hsl0) rfl (by rw [hoff72]; omega) (by rw [hoff72]; omega) (by rw [hoff72, htoh]; omega) (by rw [hoff72]; omega) hi23
  have hstep24 : Step ⟨σ23, i23, c.steps + 23⟩ ⟨σ24, i24, c.steps + 24⟩ := hs24
  have hpc24 : σ24.regs.get? Register.PC = some (0x80007694#64) := by
    have := obs_store_pc hobs24
    rwa [show BitVec.addInt (0x80007690#64) 4 = (0x80007694#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi24, hmi24⟩ := obs_store_minstret hobs24
  have hp24 := pins_store hobs24 (by rfl) hp23
  have hmE24 : σ24.mem = writeMap8 (c.σ.mem) (vsp.toNat + 72) (sdData_val (1#64)) := by
    rw [hmem24, mem_afterNextPC, hmE23, hoff72]

  have hslA : Vsa.Sim.Code.SvfprintfSliceLoaded σ24.mem := by
    rw [hmem24, mem_afterNextPC]
    exact svfprintfSlice_writeMap8_sn5 _ _ _ (by rw [hoff72]; omega) (hmE23 ▸ hsl0)

  -- === 0x80007694: li a2,8 ===
  obtain ⟨σ25, i25, hs25, hi25, hG25, hmem25, hobs25⟩ :=
    site_80007694_pr σ24 i24 (c.steps + 24) _ vmi24
      hG24 hpc24 hmi24 hslA rfl hi24
  have hstep25 : Step ⟨σ24, i24, c.steps + 24⟩ ⟨σ25, i25, c.steps + 25⟩ := hs25
  have hpc25 : σ25.regs.get? Register.PC = some (0x80007698#64) := by
    have := obs_alu_pc hobs25
    rwa [show BitVec.addInt (0x80007694#64) 4 = (0x80007698#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi25, hmi25⟩ := obs_alu_minstret hobs25
  have hrd25 : σ25.regs.get? Register.x12 = some ((8#64)) := by
    have := obs_alu_rd hobs25 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64) : BitVec 64) + sign_extend (m := 64) (0x008#12) = (8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp25 := pins_cons_pro hrd25 (pins_alu hobs25 (by rfl) (pins_drop5_pro hp24))
  have hmE25 : σ25.mem = writeMap8 (c.σ.mem) (vsp.toNat + 72) (sdData_val (1#64)) := hmem25.trans hmE24

  have hslB : Vsa.Sim.Code.SvfprintfSliceLoaded σ25.mem := hmem25 ▸ hslA
  -- === 0x80007698: addi a0,sp,200 ===
  obtain ⟨σ26, i26, hs26, hi26, hG26, hmem26, hobs26⟩ :=
    site_80007698_pr σ25 i25 (c.steps + 25) _ vmi25 vsp
      hG25 hpc25 hmi25 hp25.2.2.2.2.2.2.2.1 hslB rfl hi25
  have hstep26 : Step ⟨σ25, i25, c.steps + 25⟩ ⟨σ26, i26, c.steps + 26⟩ := hs26
  have hpc26 : σ26.regs.get? Register.PC = some (0x8000769c#64) := by
    have := obs_alu_pc hobs26
    rwa [show BitVec.addInt (0x80007698#64) 4 = (0x8000769c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi26, hmi26⟩ := obs_alu_minstret hobs26
  have hrd26 : σ26.regs.get? Register.x10 = some (vsp + sign_extend (m := 64) (0x0c8#12)) :=
    obs_alu_rd hobs26 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp26 := pins_cons_pro hrd26 (pins_alu hobs26 (by rfl) (pins_drop2_pro hp25))
  have hmE26 : σ26.mem = writeMap8 (c.σ.mem) (vsp.toNat + 72) (sdData_val (1#64)) := hmem26.trans hmE25

  have hslC : Vsa.Sim.Code.SvfprintfSliceLoaded σ26.mem := hmem26 ▸ hslB
  -- === 0x8000769c: li a1,0 ===
  obtain ⟨σ27, i27, hs27, hi27, hG27, hmem27, hobs27⟩ :=
    site_8000769c_pr σ26 i26 (c.steps + 26) _ vmi26
      hG26 hpc26 hmi26 hslC rfl hi26
  have hstep27 : Step ⟨σ26, i26, c.steps + 26⟩ ⟨σ27, i27, c.steps + 27⟩ := hs27
  have hpc27 : σ27.regs.get? Register.PC = some (0x800076a0#64) := by
    have := obs_alu_pc hobs27
    rwa [show BitVec.addInt (0x8000769c#64) 4 = (0x800076a0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi27, hmi27⟩ := obs_alu_minstret hobs27
  have hrd27 : σ27.regs.get? Register.x11 = some ((0#64)) := by
    have := obs_alu_rd hobs27 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro (0#64)] at this
  have hp27 := pins_cons_pro hrd27 (pins_alu hobs27 (by rfl) (pins_drop6_pro hp26))
  have hmE27 : σ27.mem = writeMap8 (c.σ.mem) (vsp.toNat + 72) (sdData_val (1#64)) := hmem27.trans hmE26

  have hslN : Vsa.Sim.Code.SvfprintfSliceLoaded σ27.mem := hmem27 ▸ hslC
  have hmsN : Vsa.Sim.Code.MemsetLoaded σ27.mem := by
    rw [hmE27]
    exact memset_w8_pro _ _ _ (by omega) hms0
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ27.mem := by
    rw [hmE27]
    exact localemb_w8_pro _ _ _ (by omega) hlm0
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ27.mem := by
    rw [hmE27]
    exact amb_w8_pro _ _ _ (by omega) hamb0
  have hS048 : SlotHolds vsp 0x048 (1#64) σ27.mem := by
    rw [hmE27]
    exact slot_save vsp 0x048 (1#64) _ _ _ hoff72 rfl
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 72 ≤ a ∧ a < vsp.toNat + 80) →
      σ27.mem[a]? = c.σ.mem[a]? := by
    intro a hw0
    rw [hmE27, getElem?_writeMap8_out _ (vsp.toNat + 72) _ a (by omega)]
  refine ⟨⟨σ27, i27, c.steps + 27⟩, ?_,
    hG27,
    hpc27,
    hp27.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.2.1,
    hp27.2.1,
    hp27.1,
    hp27.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp27.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hS048,
    hagN,
    hslN,
    hmsN,
    hlmN,
    hambN,
    hi27,
    ⟨vmi27, hmi27⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans ((Steps.single hstep19).trans ((Steps.single hstep20).trans ((Steps.single hstep21).trans ((Steps.single hstep22).trans ((Steps.single hstep23).trans ((Steps.single hstep24).trans ((Steps.single hstep25).trans ((Steps.single hstep26).trans (Steps.single hstep27))))))))))))))))))))))))))

end Vsa.Sim
