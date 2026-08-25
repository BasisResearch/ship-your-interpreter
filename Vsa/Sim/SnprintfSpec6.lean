import Vsa.Sim.SnprintfSpec5

/-!
# M3 Layer-3 — `SnprintfSpec6` : sign block → digit buffer, composed (`_sn6`)

Glues the three verified segments end-to-end for the negative arm:

* `splitToEntry_spec` — the flag-guard hop `0x800080f8 bltz s4` (both arms) and
  the optional flag mask `0x800080fc andi t1,t1,-129`, joining at the fast/multi
  split `0x80008100`.  Memory untouched; the grouping bit of `t1` stays clear
  (`flagmask_sn6`).
* `signToDigits_neg_spec` — the composed theorem: from the sign-block entry
  `0x800080e4` with the loaded argument `v` negative and magnitude `> 9`, the
  machine emits `'-'` into `sp+167`, negates, threads the flag guard, runs the
  loop entry and the whole decimal loop, and exits at `0x80008358` with the
  complete decimal digit string of the magnitude in the descending buffer.
  The value bridge `((0#64) - v).toNat = (-v.toInt).toNat` (INT64_MIN-safe)
  ties the buffer content to `intToString v.toInt`'s magnitude digits
  (`intToString_signblock_sn4`, `SnprintfSpec4`).

The sign byte's survival across the loop's stores (it sits at `sp+167`,
disjoint from the spill area `sp+[32,128)` and the digit window
`sp+[328,348)`) is a memory-frame fact the flush segment will need; stating it
requires a frame conjunct on `decimalLoop_spec`'s postcondition and is the
next piece of plumbing, together with the single-digit fast path and the
flush itself.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded SvfprintfSliceLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Masking `t1` with `~128` (= `sext 0xf7f`) keeps the grouping bit (1024) clear. -/
theorem flagmask_sn6 (a : BitVec 64)
    (h : a &&& sign_extend (m := 64) (0x400#12) = 0#64) :
    (a &&& sign_extend (m := 64) (0xf7f#12)) &&& sign_extend (m := 64) (0x400#12) = 0#64 := by
  rw [BitVec.and_assoc,
    show (sign_extend (m := 64) (0xf7f#12) : BitVec 64) &&& sign_extend (m := 64) (0x400#12)
      = sign_extend (m := 64) (0x400#12) from by decide, h]

/-! ## `splitToEntry_spec` — `0x800080f8` → `0x80008100`, both `bltz` arms -/

/-- The registers `splitToEntry_spec` preserves (post-widening): the five
mid-registers plus the untracked entry registers the caller needs *named*. -/
abbrev keepSplit_sn6 : List Register :=
  [Register.x3, Register.x9, Register.x18, Register.x19, Register.x21,
   Register.x8, Register.x12, Register.x13, Register.x23, Register.x28]

theorem splitToEntry_spec (w vsp vt1 v20 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800080f8#64))
    (hx14 : c.σ.regs.get? Register.x14 = some w)
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hflag : vt1 &&& sign_extend (m := 64) (0x400#12) = 0#64)
    (hx8e : ∃ v, c.σ.regs.get? Register.x8 = some v)
    (hx23e : ∃ v, c.σ.regs.get? Register.x23 = some v)
    (hx28e : ∃ v, c.σ.regs.get? Register.x28 = some v)
    (hx12e : ∃ v, c.σ.regs.get? Register.x12 = some v)
    (hx13e : ∃ v, c.σ.regs.get? Register.x13 = some v)
    (hmi : ∃ u, c.σ.regs.get? Register.minstret = some u)
    (htick : c.tick < 2) :
    ∃ (c' : Config) (vt1' : BitVec 64), Steps c c' ∧ GoodState c'.σ ∧ c'.σ.mem = c.σ.mem ∧
      c'.σ.regs.get? Register.PC = some (0x80008100#64) ∧
      c'.σ.regs.get? Register.x14 = some w ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      c'.σ.regs.get? Register.x6 = some vt1' ∧
      (vt1' &&& sign_extend (m := 64) (0x400#12) = 0#64) ∧
      (∃ v, c'.σ.regs.get? Register.x8 = some v) ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      (∃ v, c'.σ.regs.get? Register.x23 = some v) ∧
      (∃ v, c'.σ.regs.get? Register.x28 = some v) ∧
      (∃ v, c'.σ.regs.get? Register.x12 = some v) ∧
      (∃ v, c'.σ.regs.get? Register.x13 = some v) ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧
      -- post-widening: the exit flag word is one of the two arms' values, and
      -- the ten `keepSplit_sn6` registers are preserved
      (vt1' = vt1 ∨ vt1' = vt1 &&& sign_extend (m := 64) (0xf7f#12)) ∧
      KeepRegs keepSplit_sn6 c.σ c'.σ := by
  obtain ⟨vmi, hvmi⟩ := hmi
  obtain ⟨v8₀, hx8₀⟩ := hx8e
  obtain ⟨v23₀, hx23₀⟩ := hx23e
  obtain ⟨v28₀, hx28₀⟩ := hx28e
  obtain ⟨v12₀, hx12₀⟩ := hx12e
  obtain ⟨v13₀, hx13₀⟩ := hx13e
  rcases Bool.eq_false_or_eq_true (zopz0zI_s v20 (0#64)) with hs4 | hs4
  · -- s4 < 0: branch taken straight to 8100, t1 untouched
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_800080f8_taken_sn5 c.σ c.tick c.steps (0x800080f8#64) vmi v20
        hG hpc hvmi hx20 hload rfl hs4 htick
    have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
    have hpc1 : σ1.regs.get? Register.PC = some (0x80008100#64) := by
      have := obs_btaken_pc hobs1
      rwa [show (0x800080f8#64 : BitVec 64) + sign_extend (m := 64) (0x0008#13)
        = (0x80008100#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
    have hx14_1 : σ1.regs.get? Register.x14 = some w :=
      obs_btaken_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14
    have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
      obs_btaken_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
    have hx6_1 : σ1.regs.get? Register.x6 = some vt1 :=
      obs_btaken_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
    have hx8_1 : σ1.regs.get? Register.x8 = some v8₀ :=
      obs_btaken_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8₀
    have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
      obs_btaken_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20
    have hx23_1 : σ1.regs.get? Register.x23 = some v23₀ :=
      obs_btaken_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23₀
    have hx28_1 : σ1.regs.get? Register.x28 = some v28₀ :=
      obs_btaken_other hobs1 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28₀
    have hx12_1 : σ1.regs.get? Register.x12 = some v12₀ :=
      obs_btaken_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12₀
    have hx13_1 : σ1.regs.get? Register.x13 = some v13₀ :=
      obs_btaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13₀
    obtain ⟨vmi1, hvmi1⟩ := obs_btaken_minstret hobs1
    exact ⟨⟨σ1, i1, c.steps + 1⟩, vt1, Steps.single hstep1, hG1, hmem1, hpc1,
      hx14_1, hx2_1, hx6_1, hflag, ⟨v8₀, hx8_1⟩, hx20_1,
      ⟨v23₀, hx23_1⟩, ⟨v28₀, hx28_1⟩, ⟨v12₀, hx12_1⟩, ⟨v13₀, hx13_1⟩, hi1, ⟨vmi1, hvmi1⟩,
      Or.inl rfl, keep_btaken hobs1 (by decide) (keep_rfl keepSplit_sn6 c.σ)⟩
  · -- s4 ≥ 0: fall through to the andi at 80fc, then 8100
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_800080f8_nottaken_sn5 c.σ c.tick c.steps (0x800080f8#64) vmi v20
        hG hpc hvmi hx20 hload rfl hs4 htick
    have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
    have hpc1 : σ1.regs.get? Register.PC = some (0x800080fc#64) := by
      have := obs_bnottaken_pc hobs1
      rwa [show BitVec.addInt (0x800080f8#64 : BitVec 64) 4 = (0x800080fc#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hx14_1 : σ1.regs.get? Register.x14 = some w :=
      obs_bnottaken_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14
    have hx2_1 : σ1.regs.get? Register.x2 = some vsp :=
      obs_bnottaken_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2
    have hx6_1 : σ1.regs.get? Register.x6 = some vt1 :=
      obs_bnottaken_other hobs1 Register.x6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx6
    have hx8_1 : σ1.regs.get? Register.x8 = some v8₀ :=
      obs_bnottaken_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8₀
    have hx20_1 : σ1.regs.get? Register.x20 = some v20 :=
      obs_bnottaken_other hobs1 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20
    have hx23_1 : σ1.regs.get? Register.x23 = some v23₀ :=
      obs_bnottaken_other hobs1 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23₀
    have hx28_1 : σ1.regs.get? Register.x28 = some v28₀ :=
      obs_bnottaken_other hobs1 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28₀
    have hx12_1 : σ1.regs.get? Register.x12 = some v12₀ :=
      obs_bnottaken_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12₀
    have hx13_1 : σ1.regs.get? Register.x13 = some v13₀ :=
      obs_bnottaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13₀
    obtain ⟨vmi1, hvmi1⟩ := obs_bnottaken_minstret hobs1
    have hload1 : SvfprintfSliceLoaded σ1.mem := hmem1 ▸ hload
    -- 80fc: andi t1,t1,-129
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site_800080fc_sn5 σ1 i1 (c.steps + 1) (0x800080fc#64) vmi1 vt1
        hG1 hpc1 hvmi1 hx6_1 hload1 rfl hi1
    have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
    have hpc2 : σ2.regs.get? Register.PC = some (0x80008100#64) := by
      have := obs_alu_pc hobs2
      rwa [show BitVec.addInt (0x800080fc#64 : BitVec 64) 4 = (0x80008100#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hx6_2 : σ2.regs.get? Register.x6 = some (vt1 &&& sign_extend (m := 64) (0xf7f#12)) :=
      obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hx14_2 : σ2.regs.get? Register.x14 = some w :=
      obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_1
    have hx2_2 : σ2.regs.get? Register.x2 = some vsp :=
      obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx2_1
    have hx8_2 : σ2.regs.get? Register.x8 = some v8₀ :=
      obs_alu_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
    have hx20_2 : σ2.regs.get? Register.x20 = some v20 :=
      obs_alu_other hobs2 Register.x20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx20_1
    have hx23_2 : σ2.regs.get? Register.x23 = some v23₀ :=
      obs_alu_other hobs2 Register.x23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx23_1
    have hx28_2 : σ2.regs.get? Register.x28 = some v28₀ :=
      obs_alu_other hobs2 Register.x28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx28_1
    have hx12_2 : σ2.regs.get? Register.x12 = some v12₀ :=
      obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
    have hx13_2 : σ2.regs.get? Register.x13 = some v13₀ :=
      obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
    obtain ⟨vmi2, hvmi2⟩ := obs_alu_minstret hobs2
    refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, vt1 &&& sign_extend (m := 64) (0xf7f#12),
      (Steps.single hstep1).trans (Steps.single hstep2), hG2, by rw [hmem2, hmem1], hpc2,
      hx14_2, hx2_2, hx6_2, flagmask_sn6 vt1 hflag, ⟨v8₀, hx8_2⟩, hx20_2,
      ⟨v23₀, hx23_2⟩, ⟨v28₀, hx28_2⟩, ⟨v12₀, hx12_2⟩, ⟨v13₀, hx13_2⟩, hi2, ⟨vmi2, hvmi2⟩,
      Or.inr rfl,
      keep_alu hobs2 (by decide)
        (keep_bnottaken hobs1 (by decide) (keep_rfl keepSplit_sn6 c.σ))⟩

/-! ## The composed negative arm: sign block entry → complete digit buffer -/

theorem signToDigits_neg_spec (v vsp vt1 v8 v20 v23 v28 v12 : BitVec 64) (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (hfp : Vsa.Sim.Code.FlushPinsLoaded c.σ.mem)
    (huload : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hcuload : __hidden___udivdi3Loaded c.σ.mem)
    (hpc : c.σ.regs.get? Register.PC = some (0x800080e4#64))
    (hx13 : c.σ.regs.get? Register.x13 = some v)
    (hx2 : c.σ.regs.get? Register.x2 = some vsp)
    (hx6 : c.σ.regs.get? Register.x6 = some vt1)
    (hx8 : c.σ.regs.get? Register.x8 = some v8)
    (hx20 : c.σ.regs.get? Register.x20 = some v20)
    (hx23 : c.σ.regs.get? Register.x23 = some v23)
    (hx28 : c.σ.regs.get? Register.x28 = some v28)
    (hx12 : c.σ.regs.get? Register.x12 = some v12)
    (hflag : vt1 &&& sign_extend (m := 64) (0x400#12) = 0#64)
    (hneg : zopz0zKzJ_s v (0#64) = false)
    (hmag : 9 < ((0#64) - v).toNat)
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ ∃ p, ((0#64) - v).toNat / 10 ^ p ≤ 9 ∧ p + 1 ≤ 20 ∧
      (p = 0 ∨ 9 < ((0#64) - v).toNat / 10 ^ (p - 1)) ∧
      c'.σ.regs.get? Register.PC = some (0x80008358#64) ∧
      c'.σ.regs.get? Register.x23 = some (BitVec.ofNat 64 (p + 1)) ∧
      BufInv (entryTop vsp) ((0#64) - v).toNat (p + 1) c'.σ.mem ∧
      GoodState c'.σ ∧ c'.tick < 2 ∧
      (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧
      ((0#64) - v).toNat = (- v.toInt).toNat ∧
      c'.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]?
        = some (stData 1 ((0#64) + sign_extend (m := 64) (0x02d#12))) ∧
      -- the loop-carried spill/cursor/register facts the flush restore block
      -- (`exitToPrint_spec`) consumes.  The width slot 56 now carries the *named*
      -- entry `x20` value `v20` — the field width the `%`-parse produced (upstream
      -- of `0x800080e4`); the width comparison `hwlt` reduces to a fact about `v20`:
      SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.FlushPinsLoaded c'.σ.mem ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      (∃ vs4j, c'.σ.regs.get? Register.x20 = some vs4j) ∧
      c'.σ.regs.get? Register.x26 = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) ∧
      SlotHolds vsp 0x038 v20 c'.σ.mem ∧
      ∃ vwid vflg vt3 vs7 vs0,
        SlotHolds vsp 0x070 (entryTop vsp) c'.σ.mem ∧
        SlotHolds vsp 0x038 vwid c'.σ.mem ∧
        SlotHolds vsp 0x028 vflg c'.σ.mem ∧
        SlotHolds vsp 0x020 vt3 c'.σ.mem ∧
        SlotHolds vsp 0x030 vs7 c'.σ.mem ∧
        SlotHolds vsp 0x078 vs0 c'.σ.mem ∧
        -- post-widening: *named* spare-slot contents (t3/s7/s0 = the entry
        -- x28/x23/x8), the flags-slot provenance, mid-register preservation,
        -- and the pointwise memory frame outside the written windows
        SlotHolds vsp 0x020 v28 c'.σ.mem ∧
        SlotHolds vsp 0x030 v23 c'.σ.mem ∧
        SlotHolds vsp 0x078 v8 c'.σ.mem ∧
        (vflg = vt1 ∨ vflg = vt1 &&& sign_extend (m := 64) (0xf7f#12)) ∧
        KeepRegs midRegs5 c.σ c'.σ ∧
        (∀ a : Nat, a ≠ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat →
          (a < vsp.toNat + 32 ∨ (vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 328) ∨
            vsp.toNat + 348 ≤ a) →
          c'.σ.mem[a]? = c.σ.mem[a]?) := by
  have htohv : tohostAddr = 0x8001ad00 := rfl
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  have h167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    addoff_toNat_sn5 vsp (0x0a7#12) 167 (by omega) (by decide) hnw
  -- 1. the sign block: emit '-', negate
  obtain ⟨c1, hs1, hG1, hpc1, hx14_1, hsign1, htick1, hmi1,
    hx13_1, hx2_1, hx6_1, hx8_1, hx20_1, hx23_1, hx28_1, hx12_1, hload1, huload1, hcuload1, hfp1,
    hkeepSB, hsbframe⟩ :=
    signBlock_neg_spec v vsp vt1 v8 v20 v23 v28 v12 c hG hload hfp huload hcuload
      hpc hx13 hx2 hx6 hx8 hx20 hx23 hx28 hx12 hneg
      hG.minstret htick
      (by rw [h167]; omega) (by rw [h167]; omega) (by rw [h167]; omega)
  -- 2. the flag-guard hop to the split point
  obtain ⟨c2, vt1', hs2, hG2, hmem2, hpc2, hx14_2, hx2_2, hx6_2, hflag2,
    hx8e2, hx20_2c, hx23e2, hx28e2, hx12e2, hx13e2, htick2, hmi2, hvt1'or, hkeepSplit⟩ :=
    splitToEntry_spec ((0#64) - v) vsp vt1 v20 c1 hG1 hload1 hpc1 hx14_1 hx2_1 hx6_1 hx20_1
      hflag ⟨v8, hx8_1⟩ ⟨v23, hx23_1⟩ ⟨v28, hx28_1⟩ ⟨v12, hx12_1⟩ ⟨v, hx13_1⟩ hmi1 htick1
  have hload2 : SvfprintfSliceLoaded c2.σ.mem := hmem2 ▸ hload1
  have huload2 : Vsa.Sim.Code.__umoddi3Loaded c2.σ.mem := hmem2 ▸ huload1
  have hcuload2 : __hidden___udivdi3Loaded c2.σ.mem := hmem2 ▸ hcuload1
  have hfp2 : Vsa.Sim.Code.FlushPinsLoaded c2.σ.mem := hmem2 ▸ hfp1
  -- 3. loop entry + the whole decimal loop, with its memory frame + surfaced facts
  obtain ⟨c3, hs3, p, hexit, hpb, hmin, hpc3, hx23_3, hbuf3, hG3, htick3, hmi3, hEF3,
    hload3, hx2_3, hx20_3, hx26_3, hslot56v20, vwid, vt3, vs7, vs0,
    hslot112, hslot56, hslot40, hslot32, hslot48, hslot120,
    hs32named, hs48named, hs120named, hkeepED⟩ :=
    entryToDigits_spec ((0#64) - v) vsp vt1' v20 c2 hG2 hload2 huload2 hcuload2
      hpc2 hx14_2 hx2_2 hx6_2 hflag2 hx8e2 hx20_2c hx23e2 hx28e2 hx12e2 hx13e2
      hmag htlo hhi halign htick2
  -- 4. the magnitude bridge (INT64_MIN-safe)
  have hbridge : ((0#64) - v).toNat = (- v.toInt).toNat :=
    neg_out_toNat_sn4 v (bgez_false' v hneg)
  -- 5. the sign byte survives the entry spills and the digit loop (sp+167 is in
  -- the frame domain, between the spill area and the digit window)
  have hsign3 : c3.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]?
      = some (stData 1 ((0#64) + sign_extend (m := 64) (0x02d#12))) := by
    rw [hEF3 (vsp + sign_extend (m := 64) (0x0a7#12)).toNat (by rw [h167]; omega), hmem2]
    exact hsign1
  -- 6. FlushPins survive the digit path: every pin lives < 0x8000b000, and the
  -- entry/loop writes are all to the stack (≥ vsp > 0x8000b000).  `EntryFrame`
  -- fixes all low addresses (`a < vsp+32`), so the pins carry over from c2.
  have hfp3 : Vsa.Sim.Code.FlushPinsLoaded c3.σ.mem := by
    refine Vsa.Sim.Code.flushPins_of_agree (fun a ha => ?_) hfp2
    exact hEF3 a (Or.inl (by omega))
  -- post-widening: the named spare-slot contents (entry x28/x23/x8 values)
  have hslot32v28 : SlotHolds vsp 0x020 v28 c3.σ.mem :=
    hs32named v28 (hkeepSplit Register.x28 (by decide) v28 hx28_1)
  have hslot48v23 : SlotHolds vsp 0x030 v23 c3.σ.mem :=
    hs48named v23 (hkeepSplit Register.x23 (by decide) v23 hx23_1)
  have hslot120v8 : SlotHolds vsp 0x078 v8 c3.σ.mem :=
    hs120named v8 (hkeepSplit Register.x8 (by decide) v8 hx8_1)
  -- post-widening: mid-register preservation, whole block
  have hkeepAll : KeepRegs midRegs5 c.σ c3.σ :=
    keep_trans (keep_trans hkeepSB (keep_sub (by decide) hkeepSplit)) hkeepED
  -- post-widening: the pointwise frame (sign byte + spill/digit windows excluded)
  have hframeAll : ∀ a : Nat, a ≠ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat →
      (a < vsp.toNat + 32 ∨ (vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 328) ∨
        vsp.toNat + 348 ≤ a) →
      c3.σ.mem[a]? = c.σ.mem[a]? := by
    intro a hne hdom
    rw [hEF3 a hdom, hmem2]
    exact hsbframe a hne
  exact ⟨c3, hs1.trans (hs2.trans hs3), p, hexit, hpb, hmin, hpc3, hx23_3, hbuf3, hG3, htick3, hmi3,
    hbridge, hsign3, hload3, hfp3, hx2_3, hx20_3, hx26_3, hslot56v20,
    vwid, vt1', vt3, vs7, vs0, hslot112, hslot56, hslot40, hslot32, hslot48, hslot120,
    hslot32v28, hslot48v23, hslot120v8, hvt1'or, hkeepAll, hframeAll⟩

end Vsa.Sim
