import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesPro4
import Vsa.Sim.SnprintfSites2

/-!
# M3 Layer-3 — `SnprintfSpec34` : svfprintf prologue segment H
## `0x80007798 → 0x80008534` — the first `%lld` dispatch, wide post

A self-contained twin of `SnprintfSpec14.parseDispatch_l_full_spec` whose
post carries **all** the registers `SnprintfSpec16.parseToPrintEntry_spec`
and `SnprintfSpec26`'s `hmidregs` need at the `'l'` handler entry
(`x2/x3/x6/x8/x9/x10/x12/x18/x19/x20/x21/x22/x23/x25/x26/x27`) plus
`c'.σ.mem = c.σ.mem`.  The table slot bytes are caller pins (`ParseSlotPinned
0x6c` unpacked; `parseSlot_l` in SnprintfSpec13 proves the same data).
Generated in the SnprintfSpec22 house style by /tmp/gen_spec34.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (SvfprintfSliceLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **Segment H of the svfprintf prologue chain**: `0x80007798 → 0x80008534`.

The `%lld` first dispatch, with a FULL post (unlike
`SnprintfSpec14.parseDispatch_l_full_spec`, which surfaces only
`x2/x6/x20/x25/x27`): cursor bump (`s9 := vs9+1`), `sext.w`/`addiw` index
arithmetic (`'l' − 32 = 76`), `bltu` bound check not taken, `slli`/`srli`/
`add` slot address `0x8001a22c`, the `.rodata` table `lw` (bytes
`38 e4 fe ff`, caller pins), `add` → `0x80008534`, and the indirect `jr a5`.
Memory is preserved verbatim (`c'.σ.mem = c.σ.mem`). -/
theorem svfProH_spec
    (vsp va0 vfmt vs9 : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007798#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some (0x8001b798#64))
    (hx22 : c.σ.regs.get? Register.x22 = some (0x8001a0fc#64))
    (hx24 : c.σ.regs.get? Register.x24 = some (0x6c#64))
    (hx25 : c.σ.regs.get? Register.x25 = some vs9)
    (hx26 : c.σ.regs.get? Register.x26 = some (90#64))
    (hx20 : c.σ.regs.get? Register.x20 = some (0xffffffffffffffff#64))
    (hx6 : c.σ.regs.get? Register.x6 = some (0#64))
    (hx27 : c.σ.regs.get? Register.x27 = some (0#64))
    (hx10 : c.σ.regs.get? Register.x10 = some (1#64))
    (hx12 : c.σ.regs.get? Register.x12 = some vfmt)
    (hx18 : c.σ.regs.get? Register.x18 = some (16#64))
    (hx19 : c.σ.regs.get? Register.x19 = some (37#64))
    (hx21 : c.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx23 : c.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)))
    -- the .rodata parse-table 'l' slot bytes at 0x8001a22c (offset -0x11bc8)
    (htb0 : c.σ.mem[(0x8001a22c : Nat)]? = some (0x38#8))
    (htb1 : c.σ.mem[(0x8001a22c : Nat) + 1]? = some (0xe4#8))
    (htb2 : c.σ.mem[(0x8001a22c : Nat) + 2]? = some (0xfe#8))
    (htb3 : c.σ.mem[(0x8001a22c : Nat) + 3]? = some (0xff#8))
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x80008534#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some (0x8001b798#64) ∧
      c'.σ.regs.get? Register.x6 = some (0#64) ∧
      c'.σ.regs.get? Register.x20 = some (0xffffffffffffffff#64) ∧
      c'.σ.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) ∧
      c'.σ.regs.get? Register.x26 = some (90#64) ∧
      c'.σ.regs.get? Register.x22 = some (0x8001a0fc#64) ∧
      c'.σ.regs.get? Register.x27 = some (0#64) ∧
      c'.σ.regs.get? Register.x10 = some (1#64) ∧
      c'.σ.regs.get? Register.x12 = some vfmt ∧
      c'.σ.regs.get? Register.x18 = some (16#64) ∧
      c'.σ.regs.get? Register.x19 = some (37#64) ∧
      c'.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.mem = c.σ.mem ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hofftb : ((0x8001a22c#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)).toNat
      = (0x8001a22c : Nat) := by decide
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp⟩, ⟨Register.x3, (0x8001b510#64)⟩, ⟨Register.x8, va0⟩, ⟨Register.x9, (0x8001b798#64)⟩, ⟨Register.x22, (0x8001a0fc#64)⟩, ⟨Register.x24, (0x6c#64)⟩, ⟨Register.x25, vs9⟩, ⟨Register.x26, (90#64)⟩, ⟨Register.x20, (0xffffffffffffffff#64)⟩, ⟨Register.x6, (0#64)⟩, ⟨Register.x27, (0#64)⟩, ⟨Register.x10, (1#64)⟩, ⟨Register.x12, vfmt⟩, ⟨Register.x18, (16#64)⟩, ⟨Register.x19, (37#64)⟩, ⟨Register.x21, vsp + sign_extend (m := 64) (0x160#12)⟩, ⟨Register.x23, vsp + sign_extend (m := 64) (0x160#12)⟩] :=
    ⟨hx2, hx3, hx8, hx9, hx22, hx24, hx25, hx26, hx20, hx6, hx27, hx10, hx12, hx18, hx19, hx21, hx23, trivial⟩
  -- === 0x80007798: addi s9,s9,1 — cursor to format[2] ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80007798_pr c.σ c.tick c.steps _ vmi0 vs9
      hG hpc hmi0 hp0.2.2.2.2.2.2.1 hsl0 rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000779c#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80007798#64) 4 = (0x8000779c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hrd1 : σ1.regs.get? Register.x25 = some (vs9 + sign_extend (m := 64) (0x001#12)) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp1 := pins_cons_pro hrd1 (pins_alu hobs1 (by rfl) (pins_drop7_pro hp0))
  have hmE1 : σ1.mem = c.σ.mem := hmem1

  -- === 0x8000779c: sext.w s8,s8 — still 'l' ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_8000779c_pr σ1 i1 (c.steps + 1) _ vmi1 (0x6c#64)
      hG1 hpc1 hmi1 hp1.2.2.2.2.2.2.1 (hmE1 ▸ hsl0) rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 2⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x800077a0#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x8000779c#64) 4 = (0x800077a0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hrd2 : σ2.regs.get? Register.x24 = some ((0x6c#64)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) (Sail.BitVec.extractLsb ((0x6c#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 31 0) : BitVec 64) = (0x6c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp2 := pins_cons_pro hrd2 (pins_alu hobs2 (by rfl) (pins_drop7_pro hp1))
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1

  -- === 0x800077a0: addiw a5,s8,-32 — dispatch index 76 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_800077a0_pr σ2 i2 (c.steps + 2) _ vmi2 (0x6c#64)
      hG2 hpc2 hmi2 hp2.1 (hmE2 ▸ hsl0) rfl hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 2⟩ ⟨σ3, i3, c.steps + 3⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x800077a4#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800077a0#64) 4 = (0x800077a4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hrd3 : σ3.regs.get? Register.x15 = some ((76#64)) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) (Sail.BitVec.extractLsb ((0x6c#64 : BitVec 64) + sign_extend (m := 64) (0xfe0#12)) 31 0) : BitVec 64) = (76#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp3 := pins_cons_pro hrd3 (pins_alu hobs3 (by rfl) hp2)
  have hmE3 : σ3.mem = c.σ.mem := hmem3.trans hmE2

  -- === 0x800077a4: bltu s10,a5 NOT taken (76 ≤ 90) ===
  have hbltu : zopz0zI_u (90#64) (76#64) = false := by simp only [zopz0zI_u, Sail.BitVec.toNatInt]; decide
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_800077a4_nottaken_pr σ3 i3 (c.steps + 3) _ vmi3 (90#64) (76#64)
      hG3 hpc3 hmi3 hp3.2.2.2.2.2.2.2.2.1 hp3.1 (hmE3 ▸ hsl0) rfl hbltu hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 3⟩ ⟨σ4, i4, c.steps + 4⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x800077a8#64) := by
    have := obs_bnottaken_pc hobs4
    rwa [show BitVec.addInt (0x800077a4#64) 4 = (0x800077a8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_bnottaken_minstret hobs4
  have hp4 := pins_bnottaken hobs4 (by rfl) hp3
  have hmE4 : σ4.mem = c.σ.mem := hmem4.trans hmE3

  -- === 0x800077a8: slli a4,a5,0x20 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_800077a8_pr4 σ4 i4 (c.steps + 4) _ vmi4 (76#64)
      hG4 hpc4 hmi4 hp4.1 (hmE4 ▸ hsl0) rfl hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 4⟩ ⟨σ5, i5, c.steps + 5⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x800077ac#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x800077a8#64) 4 = (0x800077ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hrd5 : σ5.regs.get? Register.x14 = some ((0x4c00000000#64)) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show shift_bits_left (76#64 : BitVec 64) (Sail.BitVec.extractLsb (0x20#6) 5 0) = (0x4c00000000#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp5 := pins_cons_pro hrd5 (pins_alu hobs5 (by rfl) hp4)
  have hmE5 : σ5.mem = c.σ.mem := hmem5.trans hmE4

  -- === 0x800077ac: srli a5,a4,0x1e — 4*76 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_800077ac_pr4 σ5 i5 (c.steps + 5) _ vmi5 (0x4c00000000#64)
      hG5 hpc5 hmi5 hp5.1 (hmE5 ▸ hsl0) rfl hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 5⟩ ⟨σ6, i6, c.steps + 6⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x800077b0#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x800077ac#64) 4 = (0x800077b0#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hrd6 : σ6.regs.get? Register.x15 = some ((304#64)) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show shift_bits_right (0x4c00000000#64 : BitVec 64) (Sail.BitVec.extractLsb (0x1e#6) 5 0) = (304#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp6 := pins_cons_pro hrd6 (pins_alu hobs6 (by rfl) (pins_drop2_pro hp5))
  have hmE6 : σ6.mem = c.σ.mem := hmem6.trans hmE5

  -- === 0x800077b0: add a5,a5,s6 — the 'l' slot address ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_800077b0_pr σ6 i6 (c.steps + 6) _ vmi6 (304#64) (0x8001a0fc#64)
      hG6 hpc6 hmi6 hp6.1 hp6.2.2.2.2.2.2.2.2.1 (hmE6 ▸ hsl0) rfl hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 7⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x800077b4#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x800077b0#64) 4 = (0x800077b4#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hrd7 : σ7.regs.get? Register.x15 = some ((0x8001a22c#64)) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (304#64 : BitVec 64) + (0x8001a0fc#64) = (0x8001a22c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp7 := pins_cons_pro hrd7 (pins_alu hobs7 (by rfl) hp6.2)
  have hmE7 : σ7.mem = c.σ.mem := hmem7.trans hmE6

  -- === 0x800077b4: lw a5,0(a5) — table offset -0x11bc8 ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_800077b4_pr σ7 i7 (c.steps + 7) _ vmi7 (0x8001a22c#64) _ _ _ _
      hG7 hpc7 hmi7 hp7.1 (hmE7 ▸ hsl0) rfl (by rw [hofftb]; omega) (by rw [hofftb]; omega) (by rw [hofftb, htoh]; omega) (by rw [hofftb]) (by rw [hofftb, hmE7]; exact htb0) (by rw [hofftb, hmE7]; exact htb1) (by rw [hofftb, hmE7]; exact htb2) (by rw [hofftb, hmE7]; exact htb3) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 7⟩ ⟨σ8, i8, c.steps + 8⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x800077b8#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x800077b4#64) 4 = (0x800077b8#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hrd8 : σ8.regs.get? Register.x15 = some ((0xfffffffffffee438#64)) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) (((((0xff#8).append (0xfe#8)).append (0xe4#8)).append (0x38#8)) : BitVec (8 * 4)) : BitVec 64) = (0xfffffffffffee438#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp8 := pins_cons_pro hrd8 (pins_alu hobs8 (by rfl) hp7.2)
  have hmE8 : σ8.mem = c.σ.mem := hmem8.trans hmE7

  -- === 0x800077b8: add a5,a5,s6 — the 'l' handler address ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_800077b8_pr σ8 i8 (c.steps + 8) _ vmi8 (0xfffffffffffee438#64) (0x8001a0fc#64)
      hG8 hpc8 hmi8 hp8.1 hp8.2.2.2.2.2.2.2.2.1 (hmE8 ▸ hsl0) rfl hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 8⟩ ⟨σ9, i9, c.steps + 9⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x800077bc#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x800077b8#64) 4 = (0x800077bc#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hrd9 : σ9.regs.get? Register.x15 = some ((0x80008534#64)) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (0xfffffffffffee438#64 : BitVec 64) + (0x8001a0fc#64) = (0x80008534#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp9 := pins_cons_pro hrd9 (pins_alu hobs9 (by rfl) hp8.2)
  have hmE9 : σ9.mem = c.σ.mem := hmem9.trans hmE8

  -- === 0x800077bc: jr a5 → the 'l' length-modifier handler ===
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_800077bc_jr_sn4 σ9 i9 (c.steps + 9) _ vmi9 (0x80008534#64)
      hG9 hpc9 hmi9 hp9.1 (hmE9 ▸ hsl0) rfl (by rw [ret_tgt _ (by decide)]; decide) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 9⟩ ⟨σ10, i10, c.steps + 10⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x80008534#64) := by
    have := obs_jr_pc hobs10
    rwa [ret_tgt _ (by decide)] at this
  obtain ⟨vmi10, hmi10⟩ := obs_jr_minstret hobs10
  have hp10 := pins_jr hobs10 (by rfl) hp9
  have hmE10 : σ10.mem = c.σ.mem := hmem10.trans hmE9

  have hmemN : σ10.mem = c.σ.mem := hmE10
  have hslN : Vsa.Sim.Code.SvfprintfSliceLoaded σ10.mem := hmemN ▸ hsl0
  refine ⟨⟨σ10, i10, c.steps + 10⟩, ?_,
    hG10,
    hpc10,
    hp10.2.2.2.2.1,
    hp10.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hmemN,
    hslN,
    hi10,
    ⟨vmi10, hmi10⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans (Steps.single hstep10)))))))))

end Vsa.Sim
