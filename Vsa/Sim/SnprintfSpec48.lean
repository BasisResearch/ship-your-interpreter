import Vsa.Sim.SnprintfSpec45
import Vsa.Sim.SnprintfSpec46
import Vsa.Sim.SnprintfSpec47
import Vsa.Sim.SnprintfSpec44

/-!
# M3 Layer-3 — `SnprintfSpec48` : `entryToPrintNN_any_spec` — ALL nonneg values

The nonneg analog of `entryToPrint_neg_any_spec` (Spec44): from the value-arm
entry `0x800080e4` with `v` NON-NEGATIVE (any magnitude) to the PRINT entry
`0x8000782c`, with the complete digit buffer (`∃ p`, `BufInv`), `x22 = x16 =
len = p+1` (**no sign bump** — `t5 = 0`), the sign slot still `0x00`, and the
flag word `vt1` carried UNMASKED (the nonneg path executes no `andi -129`).

* magnitude > 9 : `armEntryNN_spec` (Spec47) ≫ `entryToDigits_spec` (Spec5,
  reused VERBATIM — the loop never cared about the sign) ≫ `exitToPrintNN_spec`
  (Spec46, `beqz t5` taken).
* magnitude ≤ 9 : `entryToPrintNN_fast_spec` (Spec45), `p = 0`.

Downstream (next sessions): the 1-iovec PRINT segment `0x8000782c → 0x8000e908`
(count 1, no sign iovec), `ssprint_iov1_spec`, and the nonneg svfprintf/wrapper
capstones.
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

/-- **Composed nonneg arm → PRINT-entry `Steps` chain, ANY magnitude.** -/
theorem entryToPrintNN_any_spec
    (v vsp vt1 v8 v20 v23 v28 v12 : BitVec 64)
    (c : Config)
    (hG : GoodState c.σ)
    (hload : SvfprintfSliceLoaded c.σ.mem)
    (huload : Vsa.Sim.Code.__umoddi3Loaded c.σ.mem)
    (hcuload : __hidden___udivdi3Loaded c.σ.mem)
    (hfp : FlushPinsLoaded c.σ.mem)
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
    (hnn : zopz0zKzJ_s v (0#64) = true)
    (hwneg : v20.toInt < 0)
    (hwidth : ∀ (p : Nat), v.toNat / 10 ^ p ≤ 9 → p + 1 ≤ 20 →
        v20.toInt < (p + 1 : Int))
    (hz167 : c.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8))
    (htlo : tohostAddr + 16 + 64 ≤ vsp.toNat)
    (hhi : vsp.toNat + 356 ≤ 0x100000000)
    (halign : vsp.toNat % 8 = 0)
    (htick : c.tick < 2) :
    ∃ c' : Config, Steps c c' ∧ GoodState c'.σ ∧
      c'.σ.regs.get? Register.PC = some (0x8000782c#64) ∧
      c'.σ.regs.get? Register.x30 = some (0#64) ∧
      c'.σ.regs.get? Register.x31 = some (0#64) ∧
      c'.σ.regs.get? Register.x2 = some vsp ∧
      v.toNat = v.toInt.toNat ∧
      c'.tick < 2 ∧ (∃ u, c'.σ.regs.get? Register.minstret = some u) ∧
      SvfprintfSliceLoaded c'.σ.mem ∧
      FlushPinsLoaded c'.σ.mem ∧
      ArmPinsLoaded c'.σ.mem ∧
      c'.σ.regs.get? Register.x20 = some v20 ∧
      c'.σ.regs.get? Register.x23 = some v23 ∧
      c'.σ.regs.get? Register.x8 = some v8 ∧
      c'.σ.regs.get? Register.x28 = some v28 ∧
      c'.σ.regs.get? Register.x6 = some vt1 ∧
      SlotHolds vsp 0x020 (0#64) c'.σ.mem ∧
      KeepRegs midRegs5 c.σ c'.σ ∧
      (∃ p, v.toNat / 10 ^ p ≤ 9 ∧ p + 1 ≤ 20 ∧
        (p = 0 ∨ 9 < v.toNat / 10 ^ (p - 1)) ∧
        c'.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 (p + 1)) ∧
        c'.σ.regs.get? Register.x16 = some (BitVec.ofNat 64 (p + 1)) ∧
        c'.σ.regs.get? Register.x26
          = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) ∧
        BufInv (entryTop vsp) v.toNat (p + 1) c'.σ.mem) ∧
      (∀ a : Nat,
        (a < vsp.toNat + 32 ∨ (vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 328) ∨
          vsp.toNat + 348 ≤ a) →
        c'.σ.mem[a]? = c.σ.mem[a]?) ∧
      c'.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]? = some (0x00#8) := by
  have htohv : tohostAddr = 0x8001ad00 := rfl
  have hnw : vsp.toNat + 348 < 2 ^ 64 := by omega
  have h167 : (vsp + sign_extend (m := 64) (0x0a7#12)).toNat = vsp.toNat + 167 :=
    addoff_toNat_sn5 vsp (0x0a7#12) 167 (by omega) (by decide) hnw
  have htop_toNat : (entryTop vsp).toNat = vsp.toNat + 348 :=
    addoff_toNat_sn5 vsp (0x15c#12) 348 (by omega) (by decide) hnw
  -- the value bridge: nonneg toInt round-trips
  have hbridge : v.toNat = v.toInt.toNat := by
    rw [toInt_of_notop v (bgez_true' v hnn)]
    omega
  rcases Nat.lt_or_ge 9 v.toNat with hmag | hmag9
  · -- === multi-digit: armEntryNN ≫ entryToDigits (Spec5) ≫ exitToPrintNN ===
    obtain ⟨c1, hs1, hG1, hmem1, hpc1, hx14_1, hx2_1, hx6_1, hx8_1, hx20_1, hx23_1,
      hx28_1, hx12_1, hx13_1, htick1, hmi1, hkeep1⟩ :=
      armEntryNN_spec v vsp vt1 v8 v20 v23 v28 v12 c hG hload hpc hx13 hx2 hx6 hx8
        hx20 hx23 hx28 hx12 hnn hwneg htick
    have hload1 : SvfprintfSliceLoaded c1.σ.mem := hmem1 ▸ hload
    have hum1 : Vsa.Sim.Code.__umoddi3Loaded c1.σ.mem := hmem1 ▸ huload
    have hud1 : __hidden___udivdi3Loaded c1.σ.mem := hmem1 ▸ hcuload
    -- the entry block + decimal loop (Spec5, verbatim)
    obtain ⟨c2, hs2, p, hexit, hpb, hmin, hpc2, hx23c_2, hbuf2, hG2, htick2, hmi2,
      hEF, hload2, hx2_2, ⟨vs4j, hx20_2⟩, hx26_2, hs56v20,
      vwid, vt3, vs7, vs0, hs112, hs56, hs40, hs32, hs48, hs120,
      hs32n, hs48n, hs120n, hkeep5⟩ :=
      entryToDigits_spec v vsp vt1 v20 c1 hG1 hload1 hum1 hud1 hpc1 hx14_1 hx2_1 hx6_1
        hflag ⟨v8, hx8_1⟩ hx20_1 ⟨v23, hx23_1⟩ ⟨v28, hx28_1⟩ ⟨v12, hx12_1⟩ ⟨v, hx13_1⟩
        hmag htlo hhi halign htick1
    -- FlushPins/ArmPins + the cleared sign slot transported across the loop frame
    have hfp2 : FlushPinsLoaded c2.σ.mem :=
      Vsa.Sim.Code.flushPins_of_agree
        (fun a ha => (hEF a (by omega)).trans (by rw [hmem1])) hfp
    have hap2 : ArmPinsLoaded c2.σ.mem :=
      armPins_of_agree_43
        (fun a ha => (hEF a (by omega)).trans (by rw [hmem1])) hap
    have hz167_2 : c2.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]?
        = some (0x00#8) := by
      rw [hEF _ (by rw [h167]; omega), hmem1]
      exact hz167
    -- the width comparison (`bge s4,s6` not taken): `v20 < len = p+1`
    have hlen : (sign_extend (m := 64)
        ((Sail.BitVec.extractLsb (entryTop vsp) 31 0)
          - (Sail.BitVec.extractLsb (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) 31 0)))
        = BitVec.ofNat 64 (p + 1) := len_eq_p1 vsp p hhi hpb
    have hp1_toInt : (BitVec.ofNat 64 (p + 1)).toInt = (p + 1 : Int) := by
      have hlt : 2 * (BitVec.ofNat 64 (p + 1)).toNat < 2 ^ 64 := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
      rw [BitVec.toInt_eq_toNat_of_lt hlt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp
    have hwlt : zopz0zKzJ_s v20 (sign_extend (m := 64)
        ((Sail.BitVec.extractLsb (entryTop vsp) 31 0)
          - (Sail.BitVec.extractLsb (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) 31 0)))
        = false := by
      have hlt := hwidth p hexit hpb
      unfold zopz0zKzJ_s
      rw [hlen, hp1_toInt]
      exact decide_eq_false (by omega)
    -- === the exit restore + hops, `beqz t5` TAKEN ===
    obtain ⟨c3, hs3, hG3, hpc3, hx22_3, hx16_3, hx30_3, hx31_3, hx20_3, hx6_3,
      hx28_3, hx23_3, hx8_3, hx2_3, htick3, hmi3, hs32z3, hkeep7, hmfr3, hload3, hfp3⟩ :=
      exitToPrintNN_spec vsp (entryTop vsp) v20 vt1 v28 v23 v8
        (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) vs4j (BitVec.ofNat 64 (p + 1))
        (0x00#8) c2
        hG2 hload2 hfp2 hpc2 hx2_2 hx26_2 hx20_2 hx23c_2
        hs112 hs56v20 hs40 (hs32n v28 hx28_1) (hs48n v23 hx23_1) (hs120n v8 hx8_1)
        hz167_2 (by decide) hwlt htlo hhi halign htick2
    -- fold the exit values
    rw [hlen] at hx22_3 hx16_3
    rw [show (zero_extend (m := 64) (0x00#8) : BitVec 64) = (0#64) from by decide] at hx30_3
    have hx26_3 : c3.σ.regs.get? Register.x26
        = some (BitVec.ofNat 64 ((entryTop vsp).toNat - 1 - p)) :=
      hkeep7 Register.x26 (by decide) _ hx26_2
    -- the digit buffer + the cleared sign slot survive the restore writes
    have hbuf3 : BufInv (entryTop vsp) v.toNat (p + 1) c3.σ.mem := by
      intro j hj
      rw [hmfr3 _ (by rw [htop_toNat]; omega) (by rw [htop_toNat]; omega)]
      exact hbuf2 j hj
    have hz167_3 : c3.σ.mem[(vsp + sign_extend (m := 64) (0x0a7#12)).toNat]?
        = some (0x00#8) := by
      rw [hmfr3 _ (by rw [h167]; omega) (by rw [h167]; omega)]
      exact hz167_2
    have hap3 : ArmPinsLoaded c3.σ.mem :=
      armPins_of_agree_43
        (fun a ha => (hmfr3 a (by omega) (by omega)).trans
          ((hEF a (by omega)).trans (by rw [hmem1]))) hap
    -- whole-span frame + register keeps
    have hframeAll : ∀ a : Nat,
        (a < vsp.toNat + 32 ∨ (vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 328) ∨
          vsp.toNat + 348 ≤ a) →
        c3.σ.mem[a]? = c.σ.mem[a]? := by
      intro a hdom
      rw [hmfr3 a (by omega) (by omega), hEF a (by omega), hmem1]
    have hkeepAll : KeepRegs midRegs5 c.σ c3.σ :=
      keep_trans hkeep1 (keep_trans hkeep5 (keep_sub (by decide) hkeep7))
    exact ⟨c3, (hs1.trans hs2).trans hs3, hG3, hpc3, hx30_3, hx31_3, hx2_3,
      hbridge, htick3, hmi3, hload3, hfp3, hap3, hx20_3, hx23_3, hx8_3, hx28_3, hx6_3,
      hs32z3, hkeepAll,
      ⟨p, hexit, hpb, hmin, hx22_3, hx16_3, hx26_3, hbuf3⟩,
      hframeAll, hz167_3⟩
  · -- === single-digit: the fast path (Spec45) ===
    obtain ⟨c3, hs3, hG3, hpc3, hx22_3, hx16_3, hx30_3, hx31_3, hx20_3, hx6_3,
      hx28_3, hx23_3, hx8_3, hx2_3, hx26_3, htick3, hmi3, hs32z3, hbuf3, hkeepF,
      hframeF, hz167_3, hload3, hfp3, hap3⟩ :=
      entryToPrintNN_fast_spec v vsp vt1 v8 v20 v23 v28 c
        hG hload hfp hap hpc hx13 hx2 hx6 hx8 hx20 hx23 hx28
        hnn hmag9 hwneg hz167 htlo hhi halign htick
    have hframeAll : ∀ a : Nat,
        (a < vsp.toNat + 32 ∨ (vsp.toNat + 128 ≤ a ∧ a < vsp.toNat + 328) ∨
          vsp.toNat + 348 ≤ a) →
        c3.σ.mem[a]? = c.σ.mem[a]? := by
      intro a hdom
      exact hframeF a (by omega) (by omega) (by omega)
    exact ⟨c3, hs3, hG3, hpc3, hx30_3, hx31_3, hx2_3, hbridge, htick3, hmi3,
      hload3, hfp3, hap3, hx20_3, hx23_3, hx8_3, hx28_3, hx6_3, hs32z3, hkeepF,
      ⟨0, by simpa only [Nat.pow_zero, Nat.div_one] using hmag9, by omega, Or.inl rfl,
        hx22_3, hx16_3, hx26_3, hbuf3⟩,
      hframeAll, hz167_3⟩

end Vsa.Sim
