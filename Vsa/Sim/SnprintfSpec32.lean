import Vsa.Sim.SnprintfProCommon
import Vsa.Sim.SnprintfSitesPro
import Vsa.Sim.SnprintfSitesRet
import Vsa.Sim.SnprintfSitesRet3
import Vsa.Sim.SnprintfSitesRet4
import Vsa.Sim.SnprintfSitesRet5

/-!
# M3 Layer-3 — `SnprintfSpec32` : svfprintf prologue segment F
## `0x80007728 → 0x8000775c` — parse pass 1, the `'%'` recognition

Reuses the `SnprintfSitesRet*` batteries (the same instructions run on the
NUL exit path verified in `SnprintfSpec22`); here the mbtowc reads the
concrete `'%'` (`0x25`) — the first byte of the static `"%lld"` template —
returns 1, and the `beq a5,s3` dispatches into the `%`-directive block.
Generated in the SnprintfSpec22 house style by /tmp/gen_spec32.py.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- **Segment F of the svfprintf prologue**: `0x80007728 → 0x8000775c`.

The parse loop's first pass over `"%lld"`: `jal __locale_mb_cur_max` (callee
inlined, `a0 := 1`), the mbtowc argument setup, the **indirect `jalr s4` →
`__ascii_mbtowc`** reading the concrete `'%'` (`0x25`) at `vfmt` and storing
it as a wide char at `sp+180`, return `a0 = 1`, then `beqz`/`bltz` not taken,
`lw a5,180(sp)` reading the `'%'` back, and `beq a5,s3` **taken** into the
`%`-directive block at `0x8000775c`. -/
theorem svfProF_spec
    (vsp va0 vfmt : BitVec 64)
    (vS8o vS9o vS10o vS11o : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hsl0 : Vsa.Sim.Code.SvfprintfSliceLoaded c.σ.mem)
    (hlm0 : Vsa.Sim.Code.__locale_mb_cur_maxLoaded c.σ.mem)
    (hamb0 : Vsa.Sim.Code.__ascii_mbtowcLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x80007728#64))
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx3 : c.σ.regs.get? Register.x3 = some (0x8001b510#64))
    (hx8 : c.σ.regs.get? Register.x8 = some va0)
    (hx9 : c.σ.regs.get? Register.x9 = some (0x8001b798#64))
    (hx22 : c.σ.regs.get? Register.x22 = some vfmt)
    (hx20 : c.σ.regs.get? Register.x20 = some (0x80012268#64))
    (hx18 : c.σ.regs.get? Register.x18 = some (16#64))
    (hx19 : c.σ.regs.get? Register.x19 = some (37#64))
    (hx21 : c.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx23 : c.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)))
    (hx24 : c.σ.regs.get? Register.x24 = some vS8o)
    (hx25 : c.σ.regs.get? Register.x25 = some vS9o)
    (hx26 : c.σ.regs.get? Register.x26 = some vS10o)
    (hx27 : c.σ.regs.get? Register.x27 = some vS11o)
    -- static locale data: __mb_cur_max byte
    (hmbB : c.σ.mem[(0x8001b8f8 : Nat)]? = some (0x01#8))
    -- the format string's first byte: '%'
    (hpctB : c.σ.mem[vfmt.toNat]? = some (0x25#8))
    (hflo : 0x80000000 ≤ vfmt.toNat)
    (hfhi : vfmt.toNat + 8 ≤ 0x100000000)
    (hfhtif : vfmt.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ vfmt.toNat)
    (hfstk : vfmt.toNat + 8 ≤ vsp.toNat ∨ vsp.toNat + 592 ≤ vfmt.toNat)
    (hsplo : 0x8001c000 ≤ vsp.toNat)
    (hsphi : vsp.toNat + 592 ≤ 0x100000000)
    (hspal : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000775c#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x1 = some (0x80007744#64) ∧
      c'.σ.regs.get? Register.x3 = some (0x8001b510#64) ∧
      c'.σ.regs.get? Register.x8 = some va0 ∧
      c'.σ.regs.get? Register.x9 = some (0x8001b798#64) ∧
      c'.σ.regs.get? Register.x22 = some vfmt ∧
      c'.σ.regs.get? Register.x20 = some (0x80012268#64) ∧
      c'.σ.regs.get? Register.x10 = some (1#64) ∧
      c'.σ.regs.get? Register.x11 = some (vsp + sign_extend (m := 64) (0x0b4#12)) ∧
      c'.σ.regs.get? Register.x12 = some vfmt ∧
      c'.σ.regs.get? Register.x13 = some (1#64) ∧
      c'.σ.regs.get? Register.x18 = some (16#64) ∧
      c'.σ.regs.get? Register.x19 = some (37#64) ∧
      c'.σ.regs.get? Register.x21 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x23 = some (vsp + sign_extend (m := 64) (0x160#12)) ∧
      c'.σ.regs.get? Register.x24 = some vS8o ∧
      c'.σ.regs.get? Register.x25 = some vS9o ∧
      c'.σ.regs.get? Register.x26 = some vS10o ∧
      c'.σ.regs.get? Register.x27 = some vS11o ∧
      Pin4 c'.σ.mem (vsp.toNat + 180) (swData (0x25#64)) ∧
      (∀ a : Nat, ¬(vsp.toNat + 180 ≤ a ∧ a < vsp.toNat + 184) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      Vsa.Sim.Code.SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__locale_mb_cur_maxLoaded c'.σ.mem ∧
      Vsa.Sim.Code.__ascii_mbtowcLoaded c'.σ.mem ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨vmi0, hmi0⟩ := hG.minstret
  have hoffgp : ((0x8001b510#64 : BitVec 64) + sign_extend (m := 64) (0x3e8#12)).toNat
      = (0x8001b8f8 : Nat) := by decide
  have hoffcur : (vfmt + sign_extend (m := 64) (0x000#12)).toNat = vfmt.toNat := by
    rw [sext0_add_pro]
  have hoffb4 : (vsp + sign_extend (m := 64) (0x0b4#12)).toNat = vsp.toNat + 180 :=
    ptr_addoff vsp _ 180 (by decide) (by omega)
  have hoff180 : ((vsp + sign_extend (m := 64) (0x0b4#12))
      + sign_extend (m := 64) (0x000#12)).toNat = vsp.toNat + 180 := by
    rw [sext0_add_pro, hoffb4]
  have hsigned : zopz0zI_s (1#64) (0#64) = false := by
    simp only [zopz0zI_s]; decide
  have hp0 : PinsHold c.σ [⟨Register.x2, vsp⟩, ⟨Register.x3, (0x8001b510#64)⟩, ⟨Register.x8, va0⟩, ⟨Register.x9, (0x8001b798#64)⟩, ⟨Register.x22, vfmt⟩, ⟨Register.x20, (0x80012268#64)⟩, ⟨Register.x18, (16#64)⟩, ⟨Register.x19, (37#64)⟩, ⟨Register.x21, vsp + sign_extend (m := 64) (0x160#12)⟩, ⟨Register.x23, vsp + sign_extend (m := 64) (0x160#12)⟩, ⟨Register.x24, vS8o⟩, ⟨Register.x25, vS9o⟩, ⟨Register.x26, vS10o⟩, ⟨Register.x27, vS11o⟩] :=
    ⟨hx2, hx3, hx8, hx9, hx22, hx20, hx18, hx19, hx21, hx23, hx24, hx25, hx26, hx27, trivial⟩
  -- === 0x80007728: jal __locale_mb_cur_max ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80007728_rt c.σ c.tick c.steps _ vmi0
      hG hpc hmi0 hsl0 rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80010234#64) := by
    have := obs_jal_pc hobs1
    rwa [show (0x80007728#64 : BitVec 64) + sign_extend (m := 64) (0x008b0c#21) = (0x80010234#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi1, hmi1⟩ := obs_jal_minstret hobs1
  have hrd1 : σ1.regs.get? Register.x1 = some ((0x8000772c#64)) := by
    have := obs_jal_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80007728#64) 4 = (0x8000772c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp1 := pins_cons_pro hrd1 (pins_jal hobs1 (by rfl) hp0)
  have hmE1 : σ1.mem = c.σ.mem := hmem1

  -- === 0x80010234: lbu a0,1000(gp) — __mb_cur_max = 1 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80010234_rt3 σ1 i1 (c.steps + 1) _ vmi1 (0x8001b510#64) (0x01#8)
      hG1 hpc1 hmi1 hp1.2.2.1 (hmE1 ▸ hlm0) rfl (by rw [hoffgp]; omega) (by rw [hoffgp]; omega) (Or.inr (by rw [hoffgp, htoh]; omega)) (by rw [hoffgp, hmE1]; exact hmbB) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 2⟩ := hs2
  have hpc2 : σ2.regs.get? Register.PC = some (0x80010238#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80010234#64) 4 = (0x80010238#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hrd2 : σ2.regs.get? Register.x10 = some ((1#64)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (zero_extend (m := 64) (0x01#8) : BitVec 64) = (1#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp2 := pins_cons_pro hrd2 (pins_alu hobs2 (by rfl) hp1)
  have hmE2 : σ2.mem = c.σ.mem := hmem2.trans hmE1

  -- === 0x80010238: ret ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80010238_rt3 σ2 i2 (c.steps + 2) _ vmi2 (0x8000772c#64)
      hG2 hpc2 hmi2 hp2.2.1 (hmE2 ▸ hlm0) rfl (by rw [ret_tgt _ (by decide)]; decide) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 2⟩ ⟨σ3, i3, c.steps + 3⟩ := hs3
  have hpc3 : σ3.regs.get? Register.PC = some (0x8000772c#64) := by
    have := obs_jr_pc hobs3
    rwa [ret_tgt _ (by decide)] at this
  obtain ⟨vmi3, hmi3⟩ := obs_jr_minstret hobs3
  have hp3 := pins_jr hobs3 (by rfl) hp2
  have hmE3 : σ3.mem = c.σ.mem := hmem3.trans hmE2

  -- === 0x8000772c: mv a3,a0 — n := 1 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_8000772c_rt σ3 i3 (c.steps + 3) _ vmi3 (1#64)
      hG3 hpc3 hmi3 hp3.1 (hmE3 ▸ hsl0) rfl hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 3⟩ ⟨σ4, i4, c.steps + 4⟩ := hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80007730#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x8000772c#64) 4 = (0x80007730#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hrd4 : σ4.regs.get? Register.x13 = some ((1#64)) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro (1#64)] at this
  have hp4 := pins_cons_pro hrd4 (pins_alu hobs4 (by rfl) hp3)
  have hmE4 : σ4.mem = c.σ.mem := hmem4.trans hmE3

  -- === 0x80007730: addi a4,sp,200 (mbstate; value untracked) ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80007730_rt σ4 i4 (c.steps + 4) _ vmi4 vsp
      hG4 hpc4 hmi4 hp4.2.2.2.1 (hmE4 ▸ hsl0) rfl hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 4⟩ ⟨σ5, i5, c.steps + 5⟩ := hs5
  have hpc5 : σ5.regs.get? Register.PC = some (0x80007734#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80007730#64) 4 = (0x80007734#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hp5 := pins_alu hobs5 (by rfl) hp4
  have hmE5 : σ5.mem = c.σ.mem := hmem5.trans hmE4

  -- === 0x80007734: mv a2,s6 — the fmt cursor ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80007734_rt σ5 i5 (c.steps + 5) _ vmi5 vfmt
      hG5 hpc5 hmi5 hp5.2.2.2.2.2.2.2.1 (hmE5 ▸ hsl0) rfl hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 5⟩ ⟨σ6, i6, c.steps + 6⟩ := hs6
  have hpc6 : σ6.regs.get? Register.PC = some (0x80007738#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80007734#64) 4 = (0x80007738#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hrd6 : σ6.regs.get? Register.x12 = some (vfmt) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro vfmt] at this
  have hp6 := pins_cons_pro hrd6 (pins_alu hobs6 (by rfl) hp5)
  have hmE6 : σ6.mem = c.σ.mem := hmem6.trans hmE5

  -- === 0x80007738: addi a1,sp,180 — pwc ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80007738_rt σ6 i6 (c.steps + 6) _ vmi6 vsp
      hG6 hpc6 hmi6 hp6.2.2.2.2.1 (hmE6 ▸ hsl0) rfl hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 6⟩ ⟨σ7, i7, c.steps + 7⟩ := hs7
  have hpc7 : σ7.regs.get? Register.PC = some (0x8000773c#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80007738#64) 4 = (0x8000773c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hrd7 : σ7.regs.get? Register.x11 = some (vsp + sign_extend (m := 64) (0x0b4#12)) :=
    obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp7 := pins_cons_pro hrd7 (pins_alu hobs7 (by rfl) hp6)
  have hmE7 : σ7.mem = c.σ.mem := hmem7.trans hmE6

  -- === 0x8000773c: mv a0,s0 — reent ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_8000773c_rt σ7 i7 (c.steps + 7) _ vmi7 va0
      hG7 hpc7 hmi7 hp7.2.2.2.2.2.2.2.1 (hmE7 ▸ hsl0) rfl hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 7⟩ ⟨σ8, i8, c.steps + 8⟩ := hs8
  have hpc8 : σ8.regs.get? Register.PC = some (0x80007740#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x8000773c#64) 4 = (0x80007740#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hrd8 : σ8.regs.get? Register.x10 = some (va0) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add_pro va0] at this
  have hp8 := pins_cons_pro hrd8 (pins_alu hobs8 (by rfl) (pins_drop4_pro hp7))
  have hmE8 : σ8.mem = c.σ.mem := hmem8.trans hmE7

  -- === 0x80007740: jalr s4 — indirect call to __ascii_mbtowc ===
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80007740_rt5 σ8 i8 (c.steps + 8) _ vmi8 (0x80012268#64)
      hG8 hpc8 hmi8 hp8.2.2.2.2.2.2.2.2.2.2.1 (hmE8 ▸ hsl0) rfl (by rw [ret_tgt _ (by decide)]; decide) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 8⟩ ⟨σ9, i9, c.steps + 9⟩ := hs9
  have hpc9 : σ9.regs.get? Register.PC = some (0x80012268#64) := by
    have := obs_jalr_pc hobs9
    rwa [ret_tgt _ (by decide)] at this
  obtain ⟨vmi9, hmi9⟩ := obs_jalr_minstret hobs9
  have hrd9 : σ9.regs.get? Register.x1 = some ((0x80007744#64)) := by
    have := obs_jalr_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80007740#64) 4 = (0x80007744#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp9 := pins_cons_pro hrd9 (pins_jalr hobs9 (by rfl) (pins_drop5_pro hp8))
  have hmE9 : σ9.mem = c.σ.mem := hmem9.trans hmE8

  -- === 0x80012268: beqz a1 NOT taken (pwc = sp+180) ===
  have hgv9 : ((vsp + sign_extend (m := 64) (0x0b4#12)) == (0#64 : BitVec 64)) = false := beq64_false_pro _ _ (by rw [ptr_addoff vsp _ 180 (by decide) (by omega)]; simp only [BitVec.toNat_ofNat]; omega)
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80012268_nottaken_rt4 σ9 i9 (c.steps + 9) _ vmi9 _
      hG9 hpc9 hmi9 hp9.2.2.1 (hmE9 ▸ hamb0) rfl hgv9 hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 9⟩ ⟨σ10, i10, c.steps + 10⟩ := hs10
  have hpc10 : σ10.regs.get? Register.PC = some (0x8001226c#64) := by
    have := obs_bnottaken_pc hobs10
    rwa [show BitVec.addInt (0x80012268#64) 4 = (0x8001226c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi10, hmi10⟩ := obs_bnottaken_minstret hobs10
  have hp10 := pins_bnottaken hobs10 (by rfl) hp9
  have hmE10 : σ10.mem = c.σ.mem := hmem10.trans hmE9

  -- === 0x8001226c: beqz a2 NOT taken (fmt ≠ 0) ===
  have hgv10 : (vfmt == (0#64 : BitVec 64)) = false := beq64_false_pro _ _ (by simp only [BitVec.toNat_ofNat]; omega)
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_8001226c_nottaken_rt4 σ10 i10 (c.steps + 10) _ vmi10 vfmt
      hG10 hpc10 hmi10 hp10.2.2.2.1 (hmE10 ▸ hamb0) rfl hgv10 hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 10⟩ ⟨σ11, i11, c.steps + 11⟩ := hs11
  have hpc11 : σ11.regs.get? Register.PC = some (0x80012270#64) := by
    have := obs_bnottaken_pc hobs11
    rwa [show BitVec.addInt (0x8001226c#64) 4 = (0x80012270#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi11, hmi11⟩ := obs_bnottaken_minstret hobs11
  have hp11 := pins_bnottaken hobs11 (by rfl) hp10
  have hmE11 : σ11.mem = c.σ.mem := hmem11.trans hmE10

  -- === 0x80012270: beqz a3 NOT taken (n = 1) ===
  obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
    site_80012270_nottaken_rt4 σ11 i11 (c.steps + 11) _ vmi11 (1#64)
      hG11 hpc11 hmi11 hp11.2.2.2.2.1 (hmE11 ▸ hamb0) rfl (by decide) hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 11⟩ ⟨σ12, i12, c.steps + 12⟩ := hs12
  have hpc12 : σ12.regs.get? Register.PC = some (0x80012274#64) := by
    have := obs_bnottaken_pc hobs12
    rwa [show BitVec.addInt (0x80012270#64) 4 = (0x80012274#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi12, hmi12⟩ := obs_bnottaken_minstret hobs12
  have hp12 := pins_bnottaken hobs12 (by rfl) hp11
  have hmE12 : σ12.mem = c.σ.mem := hmem12.trans hmE11

  -- === 0x80012274: lbu a5,0(a2) — the '%' ===
  obtain ⟨σ13, i13, hs13, hi13, hG13, hmem13, hobs13⟩ :=
    site_80012274_rt4 σ12 i12 (c.steps + 12) _ vmi12 vfmt (0x25#8)
      hG12 hpc12 hmi12 hp12.2.2.2.1 (hmE12 ▸ hamb0) rfl (by rw [hoffcur]; omega) (by rw [hoffcur]; omega) (by rw [hoffcur]; exact hfhtif) (by rw [hoffcur, hmE12]; exact hpctB) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 12⟩ ⟨σ13, i13, c.steps + 13⟩ := hs13
  have hpc13 : σ13.regs.get? Register.PC = some (0x80012278#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x80012274#64) 4 = (0x80012278#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hrd13 : σ13.regs.get? Register.x15 = some ((0x25#64)) := by
    have := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (zero_extend (m := 64) (0x25#8) : BitVec 64) = (0x25#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp13 := pins_cons_pro hrd13 (pins_alu hobs13 (by rfl) hp12)
  have hmE13 : σ13.mem = c.σ.mem := hmem13.trans hmE12

  -- === 0x80012278: sw a5,0(a1) — *pwc := '%' ===
  obtain ⟨σ14, i14, hs14, hi14, hG14, hmem14, hobs14⟩ :=
    site_80012278_rt4 σ13 i13 (c.steps + 13) _ vmi13 _ (0x25#64)
      hG13 hpc13 hmi13 hp13.2.2.2.1 hp13.1 (hmE13 ▸ hamb0) rfl (by rw [hoff180]; omega) (by rw [hoff180]; omega) (by rw [hoff180, htoh]; omega) (by rw [hoff180]; omega) hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 13⟩ ⟨σ14, i14, c.steps + 14⟩ := hs14
  have hpc14 : σ14.regs.get? Register.PC = some (0x8001227c#64) := by
    have := obs_store_pc hobs14
    rwa [show BitVec.addInt (0x80012278#64) 4 = (0x8001227c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi14, hmi14⟩ := obs_store_minstret hobs14
  have hp14 := pins_store hobs14 (by rfl) hp13
  have hmE14 : σ14.mem = writeMap4 (c.σ.mem) (vsp.toNat + 180) (swData (0x25#64)) := by
    rw [hmem14, mem_afterNextPC, hmE13, hoff180]

  have hambA : Vsa.Sim.Code.__ascii_mbtowcLoaded σ14.mem := by
    rw [hmem14, mem_afterNextPC]
    exact amb_w4_pro _ _ _ (by rw [hoff180]; omega) (hmE13 ▸ hamb0)

  -- === 0x8001227c: lbu a0,0(a2) — '%' again ===
  obtain ⟨σ15, i15, hs15, hi15, hG15, hmem15, hobs15⟩ :=
    site_8001227c_rt4 σ14 i14 (c.steps + 14) _ vmi14 vfmt (0x25#8)
      hG14 hpc14 hmi14 hp14.2.2.2.2.1 hambA rfl (by rw [hoffcur]; omega) (by rw [hoffcur]; omega) (by rw [hoffcur]; exact hfhtif) (by rw [hoffcur, hmE14]; exact (getElem?_writeMap4_out_pro _ (vsp.toNat + 180) _ vfmt.toNat (by omega)).trans hpctB) hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 14⟩ ⟨σ15, i15, c.steps + 15⟩ := hs15
  have hpc15 : σ15.regs.get? Register.PC = some (0x80012280#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x8001227c#64) 4 = (0x80012280#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hrd15 : σ15.regs.get? Register.x10 = some ((0x25#64)) := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (zero_extend (m := 64) (0x25#8) : BitVec 64) = (0x25#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp15 := pins_cons_pro hrd15 (pins_alu hobs15 (by rfl) (pins_drop3_pro hp14))
  have hmE15 : σ15.mem = writeMap4 (c.σ.mem) (vsp.toNat + 180) (swData (0x25#64)) := hmem15.trans hmE14

  -- === 0x80012280: snez a0,a0 → 1 (one byte consumed) ===
  have hsnez : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (0x25#64))) : BitVec 64) = 1#64 := by rw [show zopz0zI_u (0#64) (0x25#64) = true from by simp only [zopz0zI_u, Sail.BitVec.toNatInt, BitVec.toNat_ofNat]; decide] ; apply BitVec.eq_of_toNat_eq; decide
  obtain ⟨σ16, i16, hs16, hi16, hG16, hmem16, hobs16⟩ :=
    site_80012280_rt5 σ15 i15 (c.steps + 15) _ vmi15 (0x25#64)
      hG15 hpc15 hmi15 hp15.1 (hmem15 ▸ hambA) rfl hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 15⟩ ⟨σ16, i16, c.steps + 16⟩ := hs16
  have hpc16 : σ16.regs.get? Register.PC = some (0x80012284#64) := by
    have := obs_alu_pc hobs16
    rwa [show BitVec.addInt (0x80012280#64) 4 = (0x80012284#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi16, hmi16⟩ := obs_alu_minstret hobs16
  have hrd16 : σ16.regs.get? Register.x10 = some ((1#64)) := by
    have := obs_alu_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hsnez] at this
  have hp16 := pins_cons_pro hrd16 (pins_alu hobs16 (by rfl) hp15.2)
  have hmE16 : σ16.mem = writeMap4 (c.σ.mem) (vsp.toNat + 180) (swData (0x25#64)) := hmem16.trans hmE15

  -- === 0x80012284: ret (back to svfprintf) ===
  obtain ⟨σ17, i17, hs17, hi17, hG17, hmem17, hobs17⟩ :=
    site_80012284_rt4 σ16 i16 (c.steps + 16) _ vmi16 (0x80007744#64)
      hG16 hpc16 hmi16 hp16.2.2.1 ((hmem16.trans hmem15) ▸ hambA) rfl (by rw [ret_tgt _ (by decide)]; decide) hi16
  have hstep17 : Step ⟨σ16, i16, c.steps + 16⟩ ⟨σ17, i17, c.steps + 17⟩ := hs17
  have hpc17 : σ17.regs.get? Register.PC = some (0x80007744#64) := by
    have := obs_jr_pc hobs17
    rwa [ret_tgt _ (by decide)] at this
  obtain ⟨vmi17, hmi17⟩ := obs_jr_minstret hobs17
  have hp17 := pins_jr hobs17 (by rfl) hp16
  have hmE17 : σ17.mem = writeMap4 (c.σ.mem) (vsp.toNat + 180) (swData (0x25#64)) := hmem17.trans hmE16

  have hslB : Vsa.Sim.Code.SvfprintfSliceLoaded σ17.mem := by
    rw [hmE17]
    exact svf_w4_pro _ _ _ (by omega) hsl0

  -- === 0x80007744: beqz a0 NOT taken (a0 = 1) ===
  obtain ⟨σ18, i18, hs18, hi18, hG18, hmem18, hobs18⟩ :=
    site_80007744_nottaken_pr σ17 i17 (c.steps + 17) _ vmi17 (1#64)
      hG17 hpc17 hmi17 hp17.1 hslB rfl (by decide) hi17
  have hstep18 : Step ⟨σ17, i17, c.steps + 17⟩ ⟨σ18, i18, c.steps + 18⟩ := hs18
  have hpc18 : σ18.regs.get? Register.PC = some (0x80007748#64) := by
    have := obs_bnottaken_pc hobs18
    rwa [show BitVec.addInt (0x80007744#64) 4 = (0x80007748#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi18, hmi18⟩ := obs_bnottaken_minstret hobs18
  have hp18 := pins_bnottaken hobs18 (by rfl) hp17
  have hmE18 : σ18.mem = writeMap4 (c.σ.mem) (vsp.toNat + 180) (swData (0x25#64)) := hmem18.trans hmE17

  -- === 0x80007748: bltz a0 NOT taken ===
  obtain ⟨σ19, i19, hs19, hi19, hG19, hmem19, hobs19⟩ :=
    site_80007748_nottaken_pr σ18 i18 (c.steps + 18) _ vmi18 (1#64)
      hG18 hpc18 hmi18 hp18.1 (hmem18 ▸ hslB) rfl hsigned hi18
  have hstep19 : Step ⟨σ18, i18, c.steps + 18⟩ ⟨σ19, i19, c.steps + 19⟩ := hs19
  have hpc19 : σ19.regs.get? Register.PC = some (0x8000774c#64) := by
    have := obs_bnottaken_pc hobs19
    rwa [show BitVec.addInt (0x80007748#64) 4 = (0x8000774c#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi19, hmi19⟩ := obs_bnottaken_minstret hobs19
  have hp19 := pins_bnottaken hobs19 (by rfl) hp18
  have hmE19 : σ19.mem = writeMap4 (c.σ.mem) (vsp.toNat + 180) (swData (0x25#64)) := hmem19.trans hmE18

  -- === 0x8000774c: lw a5,180(sp) — the wide char = '%' ===
  have hpinw := Pin4_writeMap4 (c.σ.mem) (vsp.toNat + 180) (swData (0x25#64))
  obtain ⟨σ20, i20, hs20, hi20, hG20, hmem20, hobs20⟩ :=
    site_8000774c_pr σ19 i19 (c.steps + 19) _ vmi19 vsp _ _ _ _
      hG19 hpc19 hmi19 hp19.2.2.2.2.2.2.1 ((hmem19.trans hmem18) ▸ hslB) rfl (by rw [hoffb4]; omega) (by rw [hoffb4]; omega) (by rw [hoffb4, htoh]; omega) (by rw [hoffb4]; omega) (by rw [hoffb4, hmE19]; exact hpinw.1) (by rw [hoffb4, hmE19]; exact hpinw.2.1) (by rw [hoffb4, hmE19]; exact hpinw.2.2.1) (by rw [hoffb4, hmE19]; exact hpinw.2.2.2) hi19
  have hstep20 : Step ⟨σ19, i19, c.steps + 19⟩ ⟨σ20, i20, c.steps + 20⟩ := hs20
  have hpc20 : σ20.regs.get? Register.PC = some (0x80007750#64) := by
    have := obs_alu_pc hobs20
    rwa [show BitVec.addInt (0x8000774c#64) 4 = (0x80007750#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  obtain ⟨vmi20, hmi20⟩ := obs_alu_minstret hobs20
  have hrd20 : σ20.regs.get? Register.x15 = some ((0x25#64)) := by
    have := obs_alu_rd hobs20 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sign_extend (m := 64) (((((swData (0x25#64)).extractLsb' 24 8).append ((swData (0x25#64)).extractLsb' 16 8)).append ((swData (0x25#64)).extractLsb' 8 8)).append ((swData (0x25#64)).extractLsb' 0 8) : BitVec (8 * 4)) : BitVec 64) = (0x25#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hp20 := pins_cons_pro hrd20 (pins_alu hobs20 (by rfl) (pins_drop2_pro hp19))
  have hmE20 : σ20.mem = writeMap4 (c.σ.mem) (vsp.toNat + 180) (swData (0x25#64)) := hmem20.trans hmE19

  -- === 0x80007750: beq a5,s3 TAKEN ('%' seen) ===
  obtain ⟨σ21, i21, hs21, hi21, hG21, hmem21, hobs21⟩ :=
    site_80007750_taken_pr σ20 i20 (c.steps + 20) _ vmi20 (0x25#64) (37#64)
      hG20 hpc20 hmi20 hp20.1 hp20.2.2.2.2.2.2.2.2.2.2.2.2.2.1 ((hmem20.trans (hmem19.trans hmem18)) ▸ hslB) rfl (by decide) hi20
  have hstep21 : Step ⟨σ20, i20, c.steps + 20⟩ ⟨σ21, i21, c.steps + 21⟩ := hs21
  have hpc21 : σ21.regs.get? Register.PC = some (0x8000775c#64) := by
    have := obs_btaken_pc hobs21
    rwa [site_80007750_taken_pr_tgt] at this
  obtain ⟨vmi21, hmi21⟩ := obs_btaken_minstret hobs21
  have hp21 := pins_btaken hobs21 (by rfl) hp20
  have hmE21 : σ21.mem = writeMap4 (c.σ.mem) (vsp.toNat + 180) (swData (0x25#64)) := hmem21.trans hmE20

  have hslN : Vsa.Sim.Code.SvfprintfSliceLoaded σ21.mem :=
    (hmem21.trans (hmem20.trans (hmem19.trans hmem18))) ▸ hslB
  have hambN : Vsa.Sim.Code.__ascii_mbtowcLoaded σ21.mem := by
    rw [hmE21]
    exact amb_w4_pro _ _ _ (by omega) hamb0
  have hlmN : Vsa.Sim.Code.__locale_mb_cur_maxLoaded σ21.mem := by
    rw [hmE21]
    exact localemb_w4_pro _ _ _ (by omega) hlm0
  have hP180 : Pin4 σ21.mem (vsp.toNat + 180) (swData (0x25#64)) := by
    rw [hmE21]
    exact Pin4_writeMap4 _ _ _
  have hagN : ∀ a : Nat, ¬(vsp.toNat + 180 ≤ a ∧ a < vsp.toNat + 184) →
      σ21.mem[a]? = c.σ.mem[a]? := by
    intro a hw0
    rw [hmE21, getElem?_writeMap4_out_pro _ (vsp.toNat + 180) _ a (by omega)]
  refine ⟨⟨σ21, i21, c.steps + 21⟩, ?_,
    hG21,
    hpc21,
    hp21.2.2.2.2.2.2.1,
    hp21.2.2.1,
    hp21.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.1,
    hp21.2.2.2.1,
    hp21.2.2.2.2.1,
    hp21.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hp21.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hP180,
    hagN,
    hslN,
    hlmN,
    hambN,
    hi21,
    ⟨vmi21, hmi21⟩⟩
  exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans ((Steps.single hstep10).trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans ((Steps.single hstep16).trans ((Steps.single hstep17).trans ((Steps.single hstep18).trans ((Steps.single hstep19).trans ((Steps.single hstep20).trans (Steps.single hstep21))))))))))))))))))))

end Vsa.Sim
