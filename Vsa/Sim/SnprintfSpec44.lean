import Vsa.Sim.SnprintfSpec8
import Vsa.Sim.SnprintfSpec43

/-!
# M3 Layer-3 — `SnprintfSpec44` : `entryToPrint_neg_any_spec` — ALL negative magnitudes

`entryToPrint_neg_spec` (SnprintfSpec8) covers the negative arm for magnitudes
`> 9` (the decimal loop).  `fastToPrint_neg_spec` (SnprintfSpec43) covers the
single-digit fast path (`≤ 9`).  This module removes the magnitude hypothesis:
the SAME statement as `entryToPrint_neg_spec` (postcondition verbatim, `p = 0`
in the fast case), for **every** negative `v` — the case split on
`9 < ((0#64) - v).toNat` happens here, not in the caller.

The only new hypothesis vs Spec8 is `ArmPinsLoaded` (the `0x80008ea4` tail
block + nonneg-hop byte pins, `Code/ArmPins.lean`), which the fast path
executes through.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded SvfprintfSliceLoaded FlushPinsLoaded ArmPinsLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- `ArmPinsLoaded` transports across any memory that agrees below `0x80009000`
(the pin ranges end at `0x80008ebc`). -/
theorem armPins_of_agree_43 {m0 mem : Std.ExtHashMap Nat (BitVec 8)}
    (hag : ∀ a, a < 0x80009000 → mem[a]? = m0[a]?) (h : ArmPinsLoaded m0) :
    ArmPinsLoaded mem := by
  unfold Vsa.Sim.Code.ArmPinsLoaded Vsa.Sim.Code.armPinsChunk0 at h ⊢
  simp (disch := omega) only [hag]
  exact h

/-- **Composed sign-block → PRINT-entry `Steps` chain for the negative case, ANY
magnitude** — `entryToPrint_neg_spec`'s statement with the `9 < mag` hypothesis
removed (and `ArmPinsLoaded` added for the fast path's tail block). -/
theorem entryToPrint_neg_any_spec
    (v vsp vt1 v8 v20 v23 v28 v12 : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (huload : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hcuload : __hidden___udivdi3Loaded c.σ.mem)
    (hfp : Vsa.Sim.Code.FlushPinsLoaded c.σ.mem)
    (hap : ArmPinsLoaded c.σ.mem)
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
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2)
    (hwidth : ∀ (p : Nat), ((0#64) - v).toNat / 10 ^ p ≤ 9 → p + 1 ≤ 20 →
        v20.toInt < (p + 1 : Int)) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000782c#64) ∧
      c'.σ.regs.get? Register.x30 = some (zero_extend (m := 64) signByte) ∧
      c'.σ.regs.get? Register.x31 = some (0#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      ((0#64) - v).toNat = (- v.toInt).toNat ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧
      SvfprintfSliceLoaded c'.σ.mem ∧
      Vsa.Sim.Code.FlushPinsLoaded c'.σ.mem ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x23 = some v23 ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x28 = some v28 ∧
      (∃ vflg, c'.σ.regs.get? Register.x6 = some vflg ∧
        (vflg = vt1 ∨ vflg = vt1 &&& sign_extend (m := 64) (0xf7f#12))) ∧
      SlotHolds vsp 0x020 (0#64) c'.σ.mem ∧
      KeepRegs midRegs5 c.σ c'.σ ∧
      (∃ p, ((0#64) - v).toNat / 10 ^ p ≤ 9 ∧ p + 1 ≤ 20 ∧
        (p = 0 ∨ 9 < ((0#64) - v).toNat / 10 ^ (p - 1)) ∧
        c'.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 (p + 1)) ∧
        c'.σ.regs.get? Register.x16 = some (BitVec.ofNat 64 (p + 2)) ∧
        c'.σ.regs.get? Register.x26
          = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) ∧
        BufInv (entryTop vsp) ((0#64) - v).toNat (p + 1) c'.σ.mem) ∧
      (∀ a : Nat, a ≠ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat →
        (a < vsp.toNat + 32 ∨ (vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 328) ∨
          vsp.toNat + 348 ≤ a) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      c'.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some signByte := by
  have htohv : tohostAddr = 0x8001ad00 := rfl
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  have h167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    addoff_toNat_sn5 vsp (0x0a7#12) 167 (by omega) (by decide) hnw
  rcases Nat.lt_or_ge 9 ((0#64) - v).toNat with hmag | hmag9
  · -- === multi-digit magnitude: exactly `entryToPrint_neg_spec` (Spec8) ===
    obtain ⟨c', hs, hG', hpc', hx30', hx31', hx2', hbridge, htick', hmi', hload', hfp',
      hx20', hx23', hx8', hx28', hvflg', hs32z', hkeep', hpblock', hframe', hsign'⟩ :=
      entryToPrint_neg_spec v vsp vt1 v8 v20 v23 v28 v12 c
        hG hload huload hcuload hfp hpc hx13 hx2 hx6 hx8 hx20 hx23 hx28 hx12
        hflag hneg hmag htlo hhi halign htick hwidth
    exact ⟨c', hs, hG', hpc', hx30', hx31', hx2', hbridge, htick', hmi', hload', hfp',
      hx20', hx23', hx8', hx28', hvflg', hs32z', hkeep', hpblock', hframe', hsign'⟩
  · -- === single-digit magnitude: sign block ≫ split ≫ fast path (Spec43) ===
    -- 1. the sign block: emit '-', negate
    obtain ⟨c1, hs1, hG1, hpc1, hx14_1, hsign1, htick1, hmi1,
      hx13_1, hx2_1, hx6_1, hx8_1, hx20_1, hx23_1, hx28_1, hx12_1,
      hload1, huload1, hcuload1, hfp1, hkeepSB, hsbframe⟩ :=
      signBlock_neg_spec v vsp vt1 v8 v20 v23 v28 v12 c hG hload hfp huload hcuload
        hpc hx13 hx2 hx6 hx8 hx20 hx23 hx28 hx12 hneg hG.minstret htick
        (by rw [h167]; omega) (by rw [h167]; omega) (by rw [h167]; omega)
    -- ArmPins survives the single sign-byte store (sp+167 is far above the pins)
    have hap1 : ArmPinsLoaded c1.σ.mem :=
      armPins_of_agree_43 (fun a ha => hsbframe a (by rw [h167]; omega)) hap
    -- 2. the flag-guard hop to the split point
    obtain ⟨c2, vt1', hs2, hG2, hmem2, hpc2, hx14_2, hx2_2, hx6_2, hflag2,
      hx8e2, hx20_2, hx23e2, hx28e2, hx12e2, hx13e2, htick2, hmi2, hvt1'or, hkeepSplit⟩ :=
      splitToEntry_spec ((0#64) - v) vsp vt1 v20 c1 hG1 hload1 hpc1 hx14_1 hx2_1 hx6_1 hx20_1
        hflag ⟨v8, hx8_1⟩ ⟨v23, hx23_1⟩ ⟨v28, hx28_1⟩ ⟨v12, hx12_1⟩ ⟨v, hx13_1⟩ hmi1 htick1
    -- named x8/x23/x28 at the split point via the widened KeepRegs
    have hx8_2 : c2.σ.regs.get? Register.x8 = some v8 :=
      hkeepSplit Register.x8 (by decide) _ hx8_1
    have hx23_2 : c2.σ.regs.get? Register.x23 = some v23 :=
      hkeepSplit Register.x23 (by decide) _ hx23_1
    have hx28_2 : c2.σ.regs.get? Register.x28 = some v28 :=
      hkeepSplit Register.x28 (by decide) _ hx28_1
    -- code pins + the sign byte at the split point (memory unchanged)
    have hload2 : SvfprintfSliceLoaded c2.σ.mem := hmem2 ▸ hload1
    have hfp2 : FlushPinsLoaded c2.σ.mem := hmem2 ▸ hfp1
    have hap2 : ArmPinsLoaded c2.σ.mem := hmem2 ▸ hap1
    have hsign2 : c2.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]?
        = some signByte := hmem2 ▸ hsign1
    -- the default width is below the (single-digit) length: `v20.toInt < 1`
    have hwneg : v20.toInt < 1 := by
      have := hwidth 0 (by simpa only [Nat.pow_zero, Nat.div_one] using hmag9) (by omega)
      omega
    -- 3. the fast path: 0x80008100 → 0x8000782c
    obtain ⟨c3, hs3, hG3, hpc3, hx22_3, hx16_3, hx30_3, hx31_3, hx20_3, hx6_3,
      hx28_3, hx23_3, hx8_3, hx2_3, hx26_3, htick3, hmi3, hs32z3, hbuf3, hkeepF,
      hframeF, hsign3, hload3, hfp3, hap3⟩ :=
      fastToPrint_neg_spec ((0#64) - v) vsp vt1' v8 v20 v23 v28 signByte c2
        hG2 hload2 hfp2 hap2 hpc2 hx14_2 hx2_2 hx6_2 hx8_2 hx20_2 hx23_2 hx28_2
        hmag9 hwneg hsign2 signByte_ne_zero htlo hhi halign htick2
    -- the magnitude bridge (INT64_MIN-safe)
    have hbridge : ((0#64) - v).toNat = (- v.toInt).toNat :=
      neg_out_toNat_sn4 v (bgez_false' v hneg)
    -- mid-register preservation across all three segments
    have hkeepAll : KeepRegs midRegs5 c.σ c3.σ :=
      keep_trans hkeepSB (keep_trans (keep_sub (by decide) hkeepSplit) hkeepF)
    -- the whole-span pointwise frame (Spec8's domain avoids every fast-path write)
    have hframeAll : ∀ a : Nat, a ≠ (vsp + sign_extend (m := 64) (0x0a7#12)).toNat →
        (a < vsp.toNat + 32 ∨ (vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 328) ∨
          vsp.toNat + 348 ≤ a) →
        c3.σ.mem[a]? = c.σ.mem[a]? := by
      intro a hne hdom
      rw [hframeF a (by omega) (by omega) (by omega), hmem2]
      exact hsbframe a (by rw [h167]; omega)
    exact ⟨c3, (hs1.trans hs2).trans hs3, hG3, hpc3, hx30_3, hx31_3, hx2_3,
      hbridge, htick3, hmi3, hload3, hfp3, hx20_3, hx23_3, hx8_3, hx28_3,
      ⟨vt1', hx6_3, hvt1'or⟩, hs32z3, hkeepAll,
      ⟨0, by simpa only [Nat.pow_zero, Nat.div_one] using hmag9, by omega, Or.inl rfl,
        hx22_3, hx16_3, hx26_3, hbuf3⟩,
      hframeAll, hsign3⟩
end Vsa.Sim
