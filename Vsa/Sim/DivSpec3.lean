import Vsa.Sim.DivSpec2
import Vsa.Sim.DivSites3

/-!
# Layer 3 — total-correctness specs for the signed division wrappers `__moddi3` / `__divdi3`

Config-level composition of the wrapper site steps (`Vsa/Sim/DivSites3.lean`,
`DivSites2.lean`) around the shared unsigned core `udivdi3_spec`
(`Vsa/Sim/DivLoops.lean`) into total-correctness triples for the two remaining
libgcc signed-division wrapper entries:

* `moddi3_spec` (`__moddi3`, entry `0x80004728`): signed remainder,
  `result.toInt = n.toInt.tmod d.toInt` under `d ≠ 0`.
* `divdi3_spec` (`__divdi3`, entry `0x800046a4`): signed quotient,
  `result.toInt = n.toInt.tdiv d.toInt` under `d ≠ 0` excluding the `INT64_MIN / -1`
  overflow input (`¬(n = intMin ∧ d = -1)`).

## Why these two need distinct Q forms

`Int.tmod` has the sign of the **dividend** and magnitude `|n| % |d|`; the
`INT64_MIN` remainder never overflows (`INT64_MIN tmod (-1) = 0`, and the binary
computes exactly that), so `moddi3` needs no overflow side-condition. `Int.tdiv`
truncates toward zero; `INT64_MIN / -1 = 2^63` is not representable, and the
`__divdi3` entry (`0x46a4`) does **not** route through the `__divsi3` overflow
guard at `0x4758` (reached only from `0x46a0`, before `__divdi3`), so we exclude
that single input with a documented `P` side-condition.

## Sign quadrants (dividend `n = a0`, divisor `d = a1`)

`__moddi3` branches on `bltz a1` (d<0) then `bltz a0` (n<0), re-checking `bgez a0`
in the `d<0` arm. The core is always called with `|n|`, `|d|`; the remainder is
negated (`neg a0,a1` at `0x4750`) exactly when `n < 0`. `__divdi3` negates each
negative operand, calls the core on `|n|`, `|d|`, and negates the quotient exactly
when the signs of `n`, `d` differ (mixed-sign path via `jal` at `0x471c`); the
same-sign paths reuse the caller's return slot (`ret`/`x1`) directly.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Signed-value ↔ `toNat` / `natAbs` bridges (kernel-safe, group-algebra discipline) -/

/-- `x` negative (top bit set): `x.toInt = x.toNat - 2^64`. -/
theorem toInt_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    x.toInt = (x.toNat : Int) - 2^64 := by
  rw [BitVec.toInt_eq_toNat_cond]; have hx := x.isLt; rw [if_neg (by omega)]; simp

/-- `x` nonnegative (top bit clear): `x.toInt = x.toNat`. -/
theorem toInt_of_notop (x : BitVec 64) (h : x.toNat < 2^63) :
    x.toInt = (x.toNat : Int) := by
  rw [BitVec.toInt_eq_toNat_cond]; rw [if_pos (by omega)]

/-- Negation `toNat` for a top-bit-set value: `(0 - x).toNat = 2^64 - x.toNat`. -/
theorem neg_toNat_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    ((0#64) - x).toNat = 2^64 - x.toNat := by
  rw [BitVec.toNat_sub]; have hx := x.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega

/-- `natAbs` of a top-bit-set value: `= 2^64 - x.toNat`. -/
theorem natAbs_of_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) :
    x.toInt.natAbs = 2^64 - x.toNat := by
  rw [toInt_of_top x h]; have hx := x.isLt
  rw [Int.natAbs_eq_iff]; right; push_cast; omega

/-- `natAbs` of a top-bit-clear value: `= x.toNat`. -/
theorem natAbs_of_notop (x : BitVec 64) (h : x.toNat < 2^63) :
    x.toInt.natAbs = x.toNat := by
  rw [toInt_of_notop x h]; simp

/-! ## Signed branch-guard bridges (`bltz`/`bgez` ⇒ top-bit facts) -/

theorem bltz_true' (x : BitVec 64) (h : zopz0zI_s x (0#64) = true) : 2^63 ≤ x.toNat := by
  unfold zopz0zI_s at h; simp only [BitVec.toInt_zero] at h
  have hlt : x.toInt < 0 := by have := of_decide_eq_true h; simpa using this
  rw [BitVec.toInt_eq_toNat_cond] at hlt
  by_cases hb : 2 * x.toNat < 2^64
  · rw [if_pos hb] at hlt; omega
  · omega

theorem bltz_false' (x : BitVec 64) (h : zopz0zI_s x (0#64) = false) : x.toNat < 2^63 := by
  unfold zopz0zI_s at h; simp only [BitVec.toInt_zero] at h
  have hge : 0 ≤ x.toInt := by
    have := of_decide_eq_false h; simp only [Int.not_lt] at this; exact this
  rw [BitVec.toInt_eq_toNat_cond] at hge
  by_cases hb : 2 * x.toNat < 2^64
  · omega
  · rw [if_neg hb] at hge; have := x.isLt; omega

theorem bgez_true' (x : BitVec 64) (h : zopz0zKzJ_s x (0#64) = true) : x.toNat < 2^63 := by
  unfold zopz0zKzJ_s at h; simp only [BitVec.toInt_zero] at h
  have hge : 0 ≤ x.toInt := by have := of_decide_eq_true h; simpa using this
  rw [BitVec.toInt_eq_toNat_cond] at hge
  by_cases hb : 2 * x.toNat < 2^64
  · omega
  · rw [if_neg hb] at hge; have := x.isLt; omega

theorem bgez_false' (x : BitVec 64) (h : zopz0zKzJ_s x (0#64) = false) : 2^63 ≤ x.toNat := by
  unfold zopz0zKzJ_s at h; simp only [BitVec.toInt_zero] at h
  have hlt : x.toInt < 0 := by
    have := of_decide_eq_false h; simp only [Int.not_le] at this; exact this
  rw [BitVec.toInt_eq_toNat_cond] at hlt
  by_cases hb : 2 * x.toNat < 2^64
  · rw [if_pos hb] at hlt; omega
  · omega

theorem bltz_cases' (x : BitVec 64) : zopz0zI_s x (0#64) = true ∨ zopz0zI_s x (0#64) = false :=
  Bool.eq_false_or_eq_true _
theorem bgez_cases' (x : BitVec 64) : zopz0zKzJ_s x (0#64) = true ∨ zopz0zKzJ_s x (0#64) = false :=
  Bool.eq_false_or_eq_true _

/-- `bgtz x` (`blt x0,x`): `zopz0zI_s 0 x = true` ⟺ `0 < x.toInt`. -/
theorem bgtz_true' (x : BitVec 64) (h : zopz0zI_s (0#64) x = true) : 0 < x.toInt := by
  unfold zopz0zI_s at h; simp only [BitVec.toInt_zero] at h
  have := of_decide_eq_true h; simpa using this
theorem bgtz_false' (x : BitVec 64) (h : zopz0zI_s (0#64) x = false) : x.toInt ≤ 0 := by
  unfold zopz0zI_s at h; simp only [BitVec.toInt_zero] at h
  have := of_decide_eq_false h; simp only [Int.not_lt] at this; exact this
theorem bgtz_cases' (x : BitVec 64) : zopz0zI_s (0#64) x = true ∨ zopz0zI_s (0#64) x = false :=
  Bool.eq_false_or_eq_true _

/-! ## `Int.tmod` / `Int.tdiv` sign+magnitude characterizations -/

theorem tmod_nonpos_of_nonpos (a b : Int) (h : a ≤ 0) : a.tmod b ≤ 0 := by
  have := Int.tmod_nonneg (a := -a) b (by omega)
  rw [Int.neg_tmod] at this; omega

/-- If `|q| = |a| % |b|` and `q` carries `a`'s sign (nonneg with `a`, nonpos with
`a`), then `q = a.tmod b`. -/
theorem tmod_of_natAbs_sign (a b q : Int)
    (hmag : q.natAbs = a.natAbs % b.natAbs)
    (hsign : 0 ≤ a → 0 ≤ q) (hsign2 : a < 0 → q ≤ 0) :
    q = a.tmod b := by
  have hnat : (a.tmod b).natAbs = a.natAbs % b.natAbs := Int.natAbs_tmod a b
  have habs : q.natAbs = (a.tmod b).natAbs := by rw [hmag, hnat]
  have hcases := Int.natAbs_eq_natAbs_iff.mp habs
  rcases Int.lt_trichotomy a 0 with ha | ha | ha
  · have hq0 := hsign2 (by omega)
    have htm := tmod_nonpos_of_nonpos a b (by omega)
    rcases hcases with h | h
    · exact h
    · omega
  · subst ha; simp only [Int.zero_tmod]
    have : q.natAbs = 0 := by rw [hmag]; simp
    exact Int.natAbs_eq_zero.mp this
  · have hq0 := hsign (by omega)
    have htm := Int.tmod_nonneg b (by omega : (0:Int) ≤ a)
    rcases hcases with h | h
    · exact h
    · omega

/-- If `|q| = |a| / |b|` and `q`'s sign is the product of `a`, `b`'s signs
(nonneg when signs agree, nonpos when they differ), then `q = a.tdiv b`,
provided `q` and `a.tdiv b` don't both have magnitude `0` with opposite chosen
signs — captured by the sign hypotheses. -/
theorem tdiv_of_natAbs_sign (a b q : Int) (hb : b ≠ 0)
    (hmag : q.natAbs = a.natAbs / b.natAbs)
    (hsign : (0 ≤ a ↔ 0 ≤ b) → 0 ≤ q)
    (hsign2 : ¬(0 ≤ a ↔ 0 ≤ b) → q ≤ 0) :
    q = a.tdiv b := by
  have hnat : (a.tdiv b).natAbs = a.natAbs / b.natAbs := Int.natAbs_tdiv a b
  have habs : q.natAbs = (a.tdiv b).natAbs := by rw [hmag, hnat]
  have hcases := Int.natAbs_eq_natAbs_iff.mp habs
  -- sign of tdiv: nonneg iff (0≤a ↔ 0≤b) OR magnitude 0
  by_cases hz : a.natAbs / b.natAbs = 0
  · -- both magnitudes 0
    have hq0 : q = 0 := Int.natAbs_eq_zero.mp (by rw [hmag]; exact hz)
    have ht0 : a.tdiv b = 0 := Int.natAbs_eq_zero.mp (by rw [hnat]; exact hz)
    rw [hq0, ht0]
  · -- magnitude positive: tdiv sign is strict
    rcases hcases with h | h
    · exact h
    · exfalso
      -- q = -(a.tdiv b), both nonzero ⇒ opposite strict signs ⇒ contradiction with sign hyps
      have htdne : a.tdiv b ≠ 0 := fun hc => hz (by rw [← hnat, hc]; simp)
      -- pin the sign of `a.tdiv b` by the four quadrants of (0≤a, 0≤b)
      by_cases ha : 0 ≤ a <;> by_cases hb2 : 0 ≤ b
      · have hs : (0 ≤ a ↔ 0 ≤ b) := ⟨fun _ => hb2, fun _ => ha⟩
        have hq0 := hsign hs
        have htpos : 0 ≤ a.tdiv b := Int.tdiv_nonneg ha hb2
        omega
      · have hbneg : b < 0 := by omega
        have hs : ¬(0 ≤ a ↔ 0 ≤ b) := fun hi => absurd (hi.mp ha) (by omega)
        have hq0 := hsign2 hs
        have htneg : a.tdiv b ≤ 0 := by
          have := Int.tdiv_nonneg (a := a) (b := -b) ha (by omega); rw [Int.tdiv_neg] at this; omega
        omega
      · have haneg : a < 0 := by omega
        have hs : ¬(0 ≤ a ↔ 0 ≤ b) := fun hi => absurd (hi.mpr hb2) (by omega)
        have hq0 := hsign2 hs
        have htneg : a.tdiv b ≤ 0 := by
          have := Int.tdiv_nonneg (a := -a) (b := b) (by omega) hb2; rw [Int.neg_tdiv] at this; omega
        omega
      · have hs : (0 ≤ a ↔ 0 ≤ b) := ⟨fun hi => absurd hi ha, fun hi => absurd hi hb2⟩
        have hq0 := hsign hs
        have htpos : 0 ≤ a.tdiv b := by
          have := Int.tdiv_nonneg (a := -a) (b := -b) (by omega) (by omega)
          rwa [Int.neg_tdiv_neg] at this
        omega

/-! ## Shared core-call helper

At a `jal`-successor state `cent` (PC at the core entry, `x1 = q` the core return
address, `x5 = r` the wrapper's saved `t0`), with core operands `A = x10`,
`B = x11`, scratch `x12/x13/minstret` defined, core code loaded, `tick < 2`,
`0 < B`, and `q` 4-aligned, run the core (`udivdi3_spec`, ghost instantiated at
`cent` so `x5 = r` is recovered by the blanket frame) to its return `q` with
`x10 = A / B`, `x11 = A % B`, `x5 = r` preserved. -/
theorem core_call_tail
    (A B r q : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (cent : Config)
    (hG : GoodState cent.σ)
    (hcl : __hidden___udivdi3Loaded cent.σ.mem) (hmem : cent.σ.mem = m0)
    (hpc : cent.σ.regs.get? Register.PC = some (0x800046ac#64))
    (hx10 : cent.σ.regs.get? Register.x10 = some A)
    (hx11 : cent.σ.regs.get? Register.x11 = some B)
    (hx1 : cent.σ.regs.get? Register.x1 = some q)
    (hx5 : cent.σ.regs.get? Register.x5 = some r)
    (hx12 : ∃ v, cent.σ.regs.get? Register.x12 = some v)
    (hx13 : ∃ v, cent.σ.regs.get? Register.x13 = some v)
    (hmi : ∃ v, cent.σ.regs.get? Register.minstret = some v)
    (htick : cent.tick < 2) (hBpos : 0 < B.toNat) (halign : q.toNat % 4 = 0) :
    ∃ c3 : Config, Steps cent c3 ∧ GoodState c3.σ ∧ c3.σ.mem = m0 ∧
      c3.σ.regs.get? Register.PC = some q ∧
      c3.σ.regs.get? Register.x10 = some (A / B) ∧
      c3.σ.regs.get? Register.x11 = some (A % B) ∧
      c3.σ.regs.get? Register.x5 = some r ∧ c3.tick < 2 ∧
      (∃ v, c3.σ.regs.get? Register.minstret = some v) := by
  obtain ⟨v12, h12⟩ := hx12
  obtain ⟨v13, h13⟩ := hx13
  have hcorepre : udivdi3_pre (fun R => cent.σ.regs.get? R) A B q m0 cent.σ.sailOutput cent := by
    refine ⟨⟨v12, v13, ?_⟩, hBpos, halign⟩
    exact {
      good := hG, loaded := hcl, mem := hmem, sailOut := rfl, pc := hpc,
      a0 := hx10, a1 := hx11, a2 := h12, a3 := h13, ra := hx1, minstret := hmi,
      tick := htick, hframe := fun R _ => rfl }
  obtain ⟨c3, hs3, hG3, hmem3, _hout3, hpc3, hq3, hrem3, _hra3, htick3, hframe3, _hx12_3, _hx13_3⟩ :=
    udivdi3_spec (fun R => cent.σ.regs.get? R) A B q m0 cent.σ.sailOutput cent hcorepre
  have hx5_3 : c3.σ.regs.get? Register.x5 = some r := by
    rw [hframe3 Register.x5 (by decide)]; exact hx5
  obtain ⟨vmi3, hmi3⟩ := hG3.minstret
  exact ⟨c3, hs3, hG3, hmem3, hpc3, hq3, hrem3, hx5_3, htick3, ⟨vmi3, hmi3⟩⟩

/-- **Framed core-call tail.** Same run as `core_call_tail` but additionally
exposes the callee-saved frame (`∀ R, NotWritten R → c3.σ.regs = cent.σ.regs`),
the `sailOutput = o` invariance, and `x1 = q`. Built directly on `udivdi3_spec`'s
strong post; leaves the plain `core_call_tail` (and hence `moddi3`) untouched. -/
theorem core_call_tail_f
    (A B r q : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (cent : Config)
    (hG : GoodState cent.σ)
    (hcl : __hidden___udivdi3Loaded cent.σ.mem) (hmem : cent.σ.mem = m0)
    (hout : cent.σ.sailOutput = o)
    (hpc : cent.σ.regs.get? Register.PC = some (0x800046ac#64))
    (hx10 : cent.σ.regs.get? Register.x10 = some A)
    (hx11 : cent.σ.regs.get? Register.x11 = some B)
    (hx1 : cent.σ.regs.get? Register.x1 = some q)
    (hx12 : ∃ v, cent.σ.regs.get? Register.x12 = some v)
    (hx13 : ∃ v, cent.σ.regs.get? Register.x13 = some v)
    (hmi : ∃ v, cent.σ.regs.get? Register.minstret = some v)
    (htick : cent.tick < 2) (hBpos : 0 < B.toNat) (halign : q.toNat % 4 = 0) :
    ∃ c3 : Config, Steps cent c3 ∧ GoodState c3.σ ∧ c3.σ.mem = m0 ∧
      c3.σ.sailOutput = o ∧
      c3.σ.regs.get? Register.PC = some q ∧
      c3.σ.regs.get? Register.x10 = some (A / B) ∧
      c3.σ.regs.get? Register.x11 = some (A % B) ∧
      c3.σ.regs.get? Register.x1 = some q ∧ c3.tick < 2 ∧
      (∀ R : Register, NotWritten R → c3.σ.regs.get? R = cent.σ.regs.get? R) ∧
      (∃ v, c3.σ.regs.get? Register.minstret = some v) := by
  obtain ⟨v12, h12⟩ := hx12
  obtain ⟨v13, h13⟩ := hx13
  have hcorepre : udivdi3_pre (fun R => cent.σ.regs.get? R) A B q m0 o cent := by
    refine ⟨⟨v12, v13, ?_⟩, hBpos, halign⟩
    exact {
      good := hG, loaded := hcl, mem := hmem, sailOut := hout, pc := hpc,
      a0 := hx10, a1 := hx11, a2 := h12, a3 := h13, ra := hx1, minstret := hmi,
      tick := htick, hframe := fun R _ => rfl }
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, hrem3, hra3, htick3, hframe3, _hx12_3, _hx13_3⟩ :=
    udivdi3_spec (fun R => cent.σ.regs.get? R) A B q m0 o cent hcorepre
  obtain ⟨vmi3, hmi3⟩ := hG3.minstret
  exact ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, hrem3, hra3, htick3, hframe3, ⟨vmi3, hmi3⟩⟩

/-! ## Result-combination lemmas (unsigned remainder ⇒ signed `tmod`) -/

/-- `|x.toInt| ≤ 2^63` for any `BitVec 64`. -/
theorem natAbs_le (x : BitVec 64) : x.toInt.natAbs ≤ 2^63 := by
  by_cases h : x.toNat < 2^63
  · rw [natAbs_of_notop x h]; omega
  · rw [natAbs_of_top x (by omega)]; have := x.isLt; omega

/-- Operand magnitude, nonnegative case: `x.toNat = |x.toInt|`. -/
theorem mag_notop (x : BitVec 64) (h : x.toNat < 2^63) : x.toNat = x.toInt.natAbs :=
  (natAbs_of_notop x h).symm

/-- Operand magnitude, negated negative case: `(0 - x).toNat = |x.toInt|`. -/
theorem mag_neg_top (x : BitVec 64) (h : 2^63 ≤ x.toNat) : ((0#64) - x).toNat = x.toInt.natAbs := by
  rw [neg_toNat_of_top x h, natAbs_of_top x h]

/-- Positive-dividend remainder: raw core remainder `A % B` is already `n tmod d`. -/
theorem res_pos (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hnneg : 0 ≤ n.toInt) (hd0 : d.toInt ≠ 0) :
    (A % B).toInt = n.toInt.tmod d.toInt := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hBpos : 0 < B.toNat := by rw [hB]; omega
  have hBle : d.toInt.natAbs ≤ 2^63 := natAbs_le d
  have hmod : (A % B).toNat = n.toInt.natAbs % d.toInt.natAbs := by rw [BitVec.toNat_umod, hA, hB]
  have hlt : (A % B).toNat < 2^63 := by
    rw [hmod]; have := Nat.mod_lt (n.toInt.natAbs) (show 0 < d.toInt.natAbs by omega); omega
  have hresInt : (A % B).toInt = ((A % B).toNat : Int) := toInt_of_notop _ hlt
  apply tmod_of_natAbs_sign
  · rw [hresInt, Int.natAbs_natCast, hmod]
  · intro _; rw [hresInt]; exact Int.natCast_nonneg _
  · intro h; omega

/-- Negative-dividend remainder: core remainder negated (`0 - (A % B)`) is `n tmod d`. -/
theorem res_neg (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hnneg : n.toInt < 0) (hd0 : d.toInt ≠ 0) :
    ((0#64) - (A % B)).toInt = n.toInt.tmod d.toInt := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hBpos : 0 < B.toNat := by rw [hB]; omega
  have hBle : d.toInt.natAbs ≤ 2^63 := natAbs_le d
  have hmod : (A % B).toNat = n.toInt.natAbs % d.toInt.natAbs := by rw [BitVec.toNat_umod, hA, hB]
  have hlt : (A % B).toNat < 2^63 := by
    rw [hmod]; have := Nat.mod_lt (n.toInt.natAbs) (show 0 < d.toInt.natAbs by omega); omega
  by_cases hz : (A % B).toNat = 0
  · have h0 : ((0#64) - (A%B)) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp [hz]
    rw [h0]
    apply tmod_of_natAbs_sign
    · simp only [BitVec.toInt_zero, Int.natAbs_zero]; rw [hmod] at hz; omega
    · intro h; omega
    · intro _; simp
  · have hres : ((0#64) - (A%B)).toNat = 2^64 - (A%B).toNat := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.zero_mod]; have := (A%B).isLt; omega
    have hresTop : 2^63 ≤ ((0#64) - (A%B)).toNat := by rw [hres]; omega
    have hresInt : ((0#64)-(A%B)).toInt = (((0#64)-(A%B)).toNat : Int) - 2^64 := toInt_of_top _ hresTop
    apply tmod_of_natAbs_sign
    · rw [natAbs_of_top _ hresTop, hres, hmod]; omega
    · intro h; omega
    · intro _; rw [hresInt, hres]; omega

/-! ## Result-combination lemmas (unsigned quotient ⇒ signed `tdiv`) -/

theorem toInt_lt_2p63 (n : BitVec 64) : n.toInt < 2^63 := by
  by_cases h : n.toNat < 2^63
  · rw [toInt_of_notop n h]; have := n.isLt; omega
  · rw [toInt_of_top n (by omega)]; have := n.isLt; omega

/-- `|n| / |d| ≤ 2^63`. -/
theorem udiv_le (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs) :
    (A / B).toNat ≤ 2^63 := by
  rw [BitVec.toNat_udiv, hA, hB]
  have h1 : n.toInt.natAbs ≤ 2^63 := natAbs_le n
  calc n.toInt.natAbs / d.toInt.natAbs ≤ n.toInt.natAbs := Nat.div_le_self _ _
    _ ≤ 2^63 := h1

/-- `|n| / |d| < 2^63` unless `n = INT64_MIN ∧ d = -1` (the sole `tdiv` overflow
input; the `__divdi3` entry does not route through the `__divsi3` overflow guard). -/
theorem udiv_lt_of_not_overflow (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hsame : 0 ≤ n.toInt ↔ 0 ≤ d.toInt) (hd0 : d.toInt ≠ 0)
    (hexcl : ¬(n.toInt = -2^63 ∧ d.toInt = -1)) :
    (A / B).toNat < 2^63 := by
  rw [BitVec.toNat_udiv, hA, hB]
  have h1 : n.toInt.natAbs ≤ 2^63 := natAbs_le n
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hnlt : n.toInt < 2^63 := toInt_lt_2p63 n
  by_cases hd1 : d.toInt.natAbs = 1
  · rw [hd1, Nat.div_one]
    by_cases hn : n.toInt.natAbs = 2^63
    · exfalso
      have hnval : n.toInt = -2^63 := by
        rcases Int.natAbs_eq n.toInt with he | he
        · rw [hn] at he; omega
        · rw [hn] at he; omega
      have hdval : d.toInt = -1 := by
        have hdneg : ¬ (0 ≤ d.toInt) := fun hc => absurd (hsame.mpr hc) (by omega)
        rcases Int.natAbs_eq d.toInt with he | he
        · rw [hd1] at he; omega
        · rw [hd1] at he; omega
      exact hexcl ⟨hnval, hdval⟩
    · omega
  · have hd2 : 2 ≤ d.toInt.natAbs := by omega
    calc n.toInt.natAbs / d.toInt.natAbs ≤ n.toInt.natAbs / 2 := Nat.div_le_div_left hd2 (by omega)
      _ < 2^63 := by omega

/-- Same-sign quotient: raw core quotient `A / B` is already `n tdiv d` (no
overflow). -/
theorem res_div_same (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hsame : 0 ≤ n.toInt ↔ 0 ≤ d.toInt) (hd0 : d.toInt ≠ 0)
    (hnov : (A / B).toNat < 2^63) :
    (A / B).toInt = n.toInt.tdiv d.toInt := by
  have hmag : (A / B).toNat = n.toInt.natAbs / d.toInt.natAbs := by rw [BitVec.toNat_udiv, hA, hB]
  have hresInt : (A / B).toInt = ((A/B).toNat : Int) := toInt_of_notop _ hnov
  apply tdiv_of_natAbs_sign _ _ _ hd0
  · rw [hresInt, Int.natAbs_natCast, hmag]
  · intro _; rw [hresInt]; exact Int.natCast_nonneg _
  · intro h; exact absurd hsame h

/-- Mixed-sign quotient: negated core quotient `0 - (A / B)` is `n tdiv d`. -/
theorem res_div_mixed (n d A B : BitVec 64)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hdiff : ¬(0 ≤ n.toInt ↔ 0 ≤ d.toInt)) (hd0 : d.toInt ≠ 0) :
    ((0#64) - (A / B)).toInt = n.toInt.tdiv d.toInt := by
  have hd0' : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h)
  have hmag : (A / B).toNat = n.toInt.natAbs / d.toInt.natAbs := by rw [BitVec.toNat_udiv, hA, hB]
  have hle : (A / B).toNat ≤ 2^63 := udiv_le n d A B hA hB
  by_cases hz : (A / B).toNat = 0
  · have h0 : ((0#64) - (A/B)) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub]; simp [hz]
    rw [h0]
    apply tdiv_of_natAbs_sign _ _ _ hd0
    · simp only [BitVec.toInt_zero, Int.natAbs_zero]; rw [hmag] at hz; omega
    · intro _; simp
    · intro _; simp
  · have hres : ((0#64) - (A/B)).toNat = 2^64 - (A/B).toNat := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.zero_mod]; have := (A/B).isLt; omega
    have hresTop : 2^63 ≤ ((0#64) - (A/B)).toNat := by rw [hres]; omega
    have hresInt : ((0#64)-(A/B)).toInt = (((0#64)-(A/B)).toNat : Int) - 2^64 := toInt_of_top _ hresTop
    apply tdiv_of_natAbs_sign _ _ _ hd0
    · rw [natAbs_of_top _ hresTop, hres, hmag]; omega
    · intro h; exact absurd h hdiff
    · intro _; rw [hresInt, hres]; omega

/-! ## `__moddi3` — signed remainder (entry `0x80004728`) -/

private theorem addi0 (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [sext_zero]; exact BitVec.add_zero v

/-- Blanket ghost-frame predicate for the `__moddi3`/`__divdi3` **wrapper**: like
the core's `NotWritten` but ALSO excluding `x1`/`ra` (clobbered by the internal
`jal`) and `x5`/`t0` (clobbered by `mv t0,ra`). Both are caller-saved so a caller
never relies on them; the callee-saved GPRs (`x2`/`s0-s11`) all satisfy
`NotWrittenD`, so the wrapper's callee-saved restore is recovered from the
strong post's frame. -/
abbrev NotWrittenD (R : Register) : Prop :=
  NotWritten R ∧ (Register.x1 == R) = false ∧ (Register.x5 == R) = false

theorem NotWrittenD.nw {R : Register} (h : NotWrittenD R) : NotWritten R := h.1

/-- Generic `jal` frame step (write-set `rd, PC, minstret, nextPC,
minstret_increment`): a variable-`R` read-back through a `jal` observation.
The caller supplies `(rd == R) = false` and `NotWritten R`. -/
theorem frame_jal {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register)
    (hrd : (rd_reg == R) = false) (hR : NotWritten R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jal σ pc vm imm rd_reg link R hmi hpc hrd hnpc hmii

/-- `moddi3_pre`: at `0x80004728` with `x10 = n`, `x11 = d`, `x1 = r`, `mem = m0`,
`d ≠ 0` (`d.toInt ≠ 0`), `r` 4-aligned, wrapper (`__moddi3Loaded`) + core loaded. -/
def moddi3_pre (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ Vsa.Sim.Code.__moddi3Loaded c.σ.mem ∧ __hidden___udivdi3Loaded c.σ.mem ∧
  c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some (0x80004728#64) ∧
  c.σ.regs.get? Register.x10 = some n ∧ c.σ.regs.get? Register.x11 = some d ∧
  c.σ.regs.get? Register.x1 = some r ∧ (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  (∃ v, c.σ.regs.get? Register.x12 = some v) ∧ (∃ v, c.σ.regs.get? Register.x13 = some v) ∧
  c.tick < 2 ∧ d.toInt ≠ 0 ∧ r.toNat % 4 = 0 ∧
  (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R)

/-- `moddi3_post`: PC back at `r`, `x10.toInt = n.toInt.tmod d.toInt`, `GoodState`,
`mem = m0`, `sailOutput = o`, `tick < 2`, and the blanket ghost frame over
`NotWrittenD` — the strong post matching `divdi3_post` (`x1`/`ra` and `x5`/`t0`
are genuinely clobbered by the wrapper's internal `jal`/`mv t0,ra`, so they are
excluded from the frame set `NotWrittenD`). -/
def moddi3_post (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some r ∧
  c.tick < 2 ∧
  (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) ∧
  ∃ res, c.σ.regs.get? Register.x10 = some res ∧ res.toInt = n.toInt.tmod d.toInt

/-! ### Shared "compute the tmod result and return" tail

From a state `cA` at the core entry `0x800046ac` with core operands `A = x10`,
`B = x11`, `x1 = q` (a core-return address, one of `0x4738`/`0x4750`), `x5 = r`
(the saved `t0`), the wrapper (`__moddi3Loaded`) still loaded, run: core (via
`core_call_tail_f`), then the fixup at `q` (either `mv a0,a1` at `0x4738`, or
`neg a0,a1` at `0x4750`), then `jr t0` back to `r`. `negate = true` for the
`0x4750` path (dividend negative). Delivers the strong `moddi3_post`, threading
the entry ghost frame `hframe0` (`cA → g`) and `sailOutput = o` through the core
and the two fixup steps. -/
theorem moddi3_tail
    (g : (R : Register) → Option (RegisterType R))
    (n d A B r q : BitVec 64) (negate : Bool) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (cA : Config)
    (hG : GoodState cA.σ) (hwl : Vsa.Sim.Code.__moddi3Loaded cA.σ.mem)
    (hcl : __hidden___udivdi3Loaded cA.σ.mem) (hmem : cA.σ.mem = m0)
    (hout : cA.σ.sailOutput = o)
    (hpc : cA.σ.regs.get? Register.PC = some (0x800046ac#64))
    (hx10 : cA.σ.regs.get? Register.x10 = some A)
    (hx11 : cA.σ.regs.get? Register.x11 = some B)
    (hx1 : cA.σ.regs.get? Register.x1 = some q)
    (hx5 : cA.σ.regs.get? Register.x5 = some r)
    (hx12 : ∃ v, cA.σ.regs.get? Register.x12 = some v)
    (hx13 : ∃ v, cA.σ.regs.get? Register.x13 = some v)
    (hmi : ∃ v, cA.σ.regs.get? Register.minstret = some v)
    (htick : cA.tick < 2) (hBpos : 0 < B.toNat) (halign : r.toNat % 4 = 0)
    (hqval : q = (if negate then 0x80004750#64 else 0x80004738#64))
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hd0 : d.toInt ≠ 0)
    (hsign : if negate then n.toInt < 0 else 0 ≤ n.toInt)
    (hframe0 : ∀ R : Register, NotWrittenD R → cA.σ.regs.get? R = g R) :
    ∃ c' : Config, Steps cA c' ∧ moddi3_post g n d r m0 o c' := by
  -- q is 4-aligned (both 0x4738 and 0x4750 are)
  have hqalign : q.toNat % 4 = 0 := by subst hqval; cases negate <;> (simp only [Bool.false_eq_true, if_false, if_true]; decide)
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, hrem3, hra3, htick3, hframe3, hmi3⟩ :=
    core_call_tail_f A B r q m0 o cA hG hcl hmem hout hpc hx10 hx11 hx1 hx12 hx13 hmi htick hBpos hqalign
  have hwl3 : Vsa.Sim.Code.__moddi3Loaded c3.σ.mem := hmem3 ▸ hmem ▸ hwl
  -- x5 = r survives the core (t0 ∈ NotWritten)
  have hx5_3 : c3.σ.regs.get? Register.x5 = some r := by rw [hframe3 Register.x5 (by decide)]; exact hx5
  obtain ⟨vmi3, hmi3v⟩ := hmi3
  cases negate with
  | false =>
    -- q = 0x4738: mv a0,a1  (a0 := a1 = A%B = rem); result = rem
    subst hqval
    simp only [Bool.false_eq_true, if_false] at *
    -- Step 4738: mv a0,a1 ⇒ x10 := x11 = A % B
    obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
      site3_80004738 c3.σ c3.tick c3.steps (0x80004738#64) vmi3 (A % B) hG3 hpc3 hmi3v hrem3 hwl3 rfl htick3
    have hstep4 : Step c3 ⟨σ4, i4, c3.steps + 1⟩ := by cases c3; exact hs4
    have hpc4 : σ4.regs.get? Register.PC = some (0x8000473c#64) := by
      have := obs_alu_pc hobs4
      rwa [show BitVec.addInt (0x80004738#64 : BitVec 64) 4 = (0x8000473c#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hx10_4 : σ4.regs.get? Register.x10 = some (A % B) := by
      have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [addi0 (A % B)] at this
    have hx5_4 : σ4.regs.get? Register.x5 = some r :=
      obs_alu_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
    obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
    have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmem3
    have hwl4 : Vsa.Sim.Code.__moddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hwl
    have hout4 : σ4.sailOutput = o := by rw [hobs4.out, sailOutput_sigmaPost_alu]; exact hout3
    -- Step 473c: jr t0 ⇒ PC := r
    have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt r halign]; exact halign
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site3_8000473c σ4 i4 (c3.steps + 1) (0x8000473c#64) vmi4 r hG4 hpc4 hmi4 hx5_4 hwl4 rfl htgt hi4
    have hstep5 : Step ⟨σ4, i4, c3.steps + 1⟩ ⟨σ5, i5, c3.steps + 1 + 1⟩ := hs5
    refine ⟨⟨σ5, i5, c3.steps + 1 + 1⟩, ?_, hG5, ?_, ?_, ?_, hi5, ?_, A % B, ?_, ?_⟩
    · exact hs3.trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans (.refl _)))
    · rw [hmem5]; exact hmemq4
    · rw [hobs5.out, hout4]
    · rw [obs_jr_pc hobs5, ret_tgt r halign]
    · -- frame: NotWrittenD R preserved through jr, mv (rd=x10), core, entry→g
      intro R hR
      rw [frame_jr hobs5 R hR.nw, frame_alu hobs4 R hR.nw.x10 hR.nw, hframe3 R hR.nw]
      exact hframe0 R hR
    · exact obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
    · exact res_pos n d A B hA hB hsign hd0
  | true =>
    -- q = 0x4750: neg a0,a1  (a0 := 0 - a1 = 0 - (A%B)); result = -(rem)
    subst hqval
    simp only [if_true] at *
    -- Step 4750: neg a0,a1 ⇒ x10 := 0 - x11 = 0 - (A % B)
    obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
      site3_80004750 c3.σ c3.tick c3.steps (0x80004750#64) vmi3 (A % B) hG3 hpc3 hmi3v hrem3 hwl3 rfl htick3
    have hstep4 : Step c3 ⟨σ4, i4, c3.steps + 1⟩ := by cases c3; exact hs4
    have hpc4 : σ4.regs.get? Register.PC = some (0x80004754#64) := by
      have := obs_alu_pc hobs4
      rwa [show BitVec.addInt (0x80004750#64 : BitVec 64) 4 = (0x80004754#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hx10_4 : σ4.regs.get? Register.x10 = some ((0#64) - (A % B)) :=
      obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hx5_4 : σ4.regs.get? Register.x5 = some r :=
      obs_alu_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
    obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
    have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmem3
    have hwl4 : Vsa.Sim.Code.__moddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hwl
    have hout4 : σ4.sailOutput = o := by rw [hobs4.out, sailOutput_sigmaPost_alu]; exact hout3
    have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt r halign]; exact halign
    obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
      site3_80004754 σ4 i4 (c3.steps + 1) (0x80004754#64) vmi4 r hG4 hpc4 hmi4 hx5_4 hwl4 rfl htgt hi4
    have hstep5 : Step ⟨σ4, i4, c3.steps + 1⟩ ⟨σ5, i5, c3.steps + 1 + 1⟩ := hs5
    refine ⟨⟨σ5, i5, c3.steps + 1 + 1⟩, ?_, hG5, ?_, ?_, ?_, hi5, ?_, (0#64) - (A % B), ?_, ?_⟩
    · exact hs3.trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans (.refl _)))
    · rw [hmem5]; exact hmemq4
    · rw [hobs5.out, hout4]
    · rw [obs_jr_pc hobs5, ret_tgt r halign]
    · intro R hR
      rw [frame_jr hobs5 R hR.nw, frame_alu hobs4 R hR.nw.x10 hR.nw, hframe3 R hR.nw]
      exact hframe0 R hR
    · exact obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
    · exact res_neg n d A B hA hB hsign hd0

/-- **`moddi3_spec`** — total-correctness triple for libgcc `__moddi3` (signed
64-bit remainder). Saves `ra` in `t0`, negates each negative operand, calls the
unsigned core on `|n|`, `|d|`, negates the remainder iff the dividend `n` is
negative, and returns via `t0`. Result: `x10.toInt = n.toInt.tmod d.toInt`
(sign of the dividend, magnitude `|n| % |d|`); no `INT64_MIN` overflow guard is
needed because `Int.tmod` never overflows. -/
theorem moddi3_spec (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (moddi3_pre g n d r m0 o) (moddi3_post g n d r m0 o) := by
  intro c hc
  obtain ⟨hG, hwl, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vmi, hmi⟩,
    ⟨v12, h12⟩, ⟨v13, h13⟩, htick, hd0, halign, hframeE⟩ := hc
  -- Step 4728: mv t0,ra ⇒ x5 := r
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site3_80004728 c.σ c.tick c.steps (0x80004728#64) vmi r hG hpc hmi hr (hmem ▸ hwl) rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
  have hpc1 : σ1.regs.get? Register.PC = some (0x8000472c#64) := obs_alu_pc hobs1
  have hx5_1 : σ1.regs.get? Register.x5 = some r := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [addi0 r] at this
  have hx10_1 : σ1.regs.get? Register.x10 = some n :=
    obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn
  have hx11_1 : σ1.regs.get? Register.x11 = some d :=
    obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd
  have hx1_1 : σ1.regs.get? Register.x1 = some r :=
    obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hr
  have hx12_1 : σ1.regs.get? Register.x12 = some v12 :=
    obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12
  have hx13_1 : σ1.regs.get? Register.x13 = some v13 :=
    obs_alu_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13
  obtain ⟨vmi1, hmi1v⟩ := obs_alu_minstret hobs1
  have hmemq1 : σ1.mem = m0 := by rw [hmem1]; exact hmem
  have hwl1 : Vsa.Sim.Code.__moddi3Loaded σ1.mem := hmemq1 ▸ hmem ▸ hwl
  have hcl1 : __hidden___udivdi3Loaded σ1.mem := hmemq1 ▸ hmem ▸ hcl
  -- The `jal` at 0x4734 / 0x474c: helper packaging the core-entry facts + call the tail.
  -- Branch on sign of d (`bltz a1`).
  rcases bltz_cases' d with hdlt | hdge
  · -- d < 0 arm: 472c taken → 4740 neg a1 (x11 := 0-d) → 4744 bgez a0
    have hdtop : 2^63 ≤ d.toNat := bltz_true' d hdlt
    -- Step 472c: bltz a1 taken ⇒ PC := 0x4740
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site3_8000472c_taken σ1 i1 (c.steps + 1) (0x8000472c#64) vmi1 d hG1 hpc1 hmi1v hx11_1 hwl1 rfl hdlt hi1
    have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
    have hpc2 : σ2.regs.get? Register.PC = some (0x80004740#64) := by
      rw [obs_btaken_pc hobs2, show (0x8000472c#64 : BitVec 64) + sign_extend (m := 64) (0x0014#13)
        = (0x80004740#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide]
    have hx10_2 : σ2.regs.get? Register.x10 = some n :=
      obs_btaken_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_1
    have hx11_2 : σ2.regs.get? Register.x11 = some d :=
      obs_btaken_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_1
    have hx1_2 : σ2.regs.get? Register.x1 = some r :=
      obs_btaken_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_1
    have hx5_2 : σ2.regs.get? Register.x5 = some r :=
      obs_btaken_other hobs2 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_1
    have hx12_2 : σ2.regs.get? Register.x12 = some v12 :=
      obs_btaken_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
    have hx13_2 : σ2.regs.get? Register.x13 = some v13 :=
      obs_btaken_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
    obtain ⟨vmi2, hmi2v⟩ := obs_btaken_minstret hobs2
    have hmemq2 : σ2.mem = m0 := by rw [hmem2]; exact hmemq1
    have hwl2 : Vsa.Sim.Code.__moddi3Loaded σ2.mem := hmemq2 ▸ hmem ▸ hwl
    have hcl2 : __hidden___udivdi3Loaded σ2.mem := hmemq2 ▸ hmem ▸ hcl
    -- Step 4740: neg a1,a1 ⇒ x11 := 0 - d
    obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
      site3_80004740 σ2 i2 (c.steps + 1 + 1) (0x80004740#64) vmi2 d hG2 hpc2 hmi2v hx11_2 hwl2 rfl hi2
    have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
    have hpc3 : σ3.regs.get? Register.PC = some (0x80004744#64) := by
      have := obs_alu_pc hobs3
      rwa [show BitVec.addInt (0x80004740#64 : BitVec 64) 4 = (0x80004744#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hx11_3 : σ3.regs.get? Register.x11 = some ((0#64) - d) :=
      obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hx10_3 : σ3.regs.get? Register.x10 = some n :=
      obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_2
    have hx1_3 : σ3.regs.get? Register.x1 = some r :=
      obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_2
    have hx5_3 : σ3.regs.get? Register.x5 = some r :=
      obs_alu_other hobs3 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_2
    have hx12_3 : σ3.regs.get? Register.x12 = some v12 :=
      obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
    have hx13_3 : σ3.regs.get? Register.x13 = some v13 :=
      obs_alu_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_2
    obtain ⟨vmi3, hmi3v⟩ := obs_alu_minstret hobs3
    have hmemq3 : σ3.mem = m0 := by rw [hmem3]; exact hmemq2
    have hwl3 : Vsa.Sim.Code.__moddi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hwl
    have hcl3 : __hidden___udivdi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hcl
    -- B := 0 - d ; magnitude and positivity facts
    have hBmag : ((0#64) - d).toNat = d.toInt.natAbs := mag_neg_top d hdtop
    have hBpos : 0 < ((0#64) - d).toNat := by
      rw [hBmag]; have := natAbs_of_top d hdtop; have := d.isLt; omega
    -- Branch on sign of n (`bgez a0`)
    rcases bgez_cases' n with hnge | hnlt
    · -- n ≥ 0 (Path C): 4744 bgez taken → 4734 jal → core (A=n, B=0-d), no negate
      have hntop : n.toNat < 2^63 := bgez_true' n hnge
      obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
        site3_80004744_taken σ3 i3 (c.steps + 1 + 1 + 1) (0x80004744#64) vmi3 n hG3 hpc3 hmi3v hx10_3 hwl3 rfl hnge hi3
      have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
      have hpc4 : σ4.regs.get? Register.PC = some (0x80004734#64) := by
        rw [obs_btaken_pc hobs4, show (0x80004744#64 : BitVec 64) + sign_extend (m := 64) (0x1ff0#13)
          = (0x80004734#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide]
      have hx10_4 : σ4.regs.get? Register.x10 = some n :=
        obs_btaken_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_3
      have hx11_4 : σ4.regs.get? Register.x11 = some ((0#64) - d) :=
        obs_btaken_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_3
      have hx1_4 : σ4.regs.get? Register.x1 = some r :=
        obs_btaken_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_3
      have hx5_4 : σ4.regs.get? Register.x5 = some r :=
        obs_btaken_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
      have hx12_4 : σ4.regs.get? Register.x12 = some v12 :=
        obs_btaken_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
      have hx13_4 : σ4.regs.get? Register.x13 = some v13 :=
        obs_btaken_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_3
      obtain ⟨vmi4, hmi4v⟩ := obs_btaken_minstret hobs4
      have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmemq3
      have hwl4 : Vsa.Sim.Code.__moddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hwl
      have hcl4 : __hidden___udivdi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hcl
      -- Step 4734: jal ⇒ x1 := 0x4738, PC := 0x46ac
      obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
        site3_80004734 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80004734#64) vmi4 hG4 hpc4 hmi4v hwl4 rfl hi4
      have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
      have hpc5 : σ5.regs.get? Register.PC = some (0x800046ac#64) := by
        have := obs_jal_pc hobs5
        rwa [show (0x80004734#64 : BitVec 64) + sign_extend (m := 64) (0x1fff78#21)
            = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
      have hx1_5 : σ5.regs.get? Register.x1 = some (0x80004738#64) := by
        have := obs_jal_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
        rwa [show BitVec.addInt (0x80004734#64 : BitVec 64) 4 = (0x80004738#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_5 : σ5.regs.get? Register.x10 = some n :=
        obs_jal_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
      have hx11_5 : σ5.regs.get? Register.x11 = some ((0#64) - d) :=
        obs_jal_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_4
      have hx5_5 : σ5.regs.get? Register.x5 = some r :=
        obs_jal_other hobs5 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_4
      have hx12_5 : σ5.regs.get? Register.x12 = some v12 :=
        obs_jal_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
      have hx13_5 : σ5.regs.get? Register.x13 = some v13 :=
        obs_jal_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_4
      have hmi5 : ∃ v, σ5.regs.get? Register.minstret = some v := obs_jal_minstret hobs5
      have hmemq5 : σ5.mem = m0 := by rw [hmem5]; exact hmemq4
      have hwl5 : Vsa.Sim.Code.__moddi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hwl
      have hcl5 : __hidden___udivdi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hcl
      have hout5 : σ5.sailOutput = o := by
        rw [hobs5.out, sailOutput_sigmaPost_jal, hobs4.out, sailOutput_sigmaPost_branch_taken,
          hobs3.out, sailOutput_sigmaPost_alu, hobs2.out, sailOutput_sigmaPost_branch_taken,
          hobs1.out, sailOutput_sigmaPost_alu]; exact hout
      have hframe5 : ∀ R : Register, NotWrittenD R → σ5.regs.get? R = g R := by
        intro R hR
        rw [frame_jal hobs5 R hR.2.1 hR.nw, frame_btaken hobs4 R hR.nw,
          frame_alu hobs3 R hR.nw.x11 hR.nw, frame_btaken hobs2 R hR.nw,
          frame_alu hobs1 R hR.2.2 hR.nw]
        exact hframeE R hR
      obtain ⟨cf, hsf, hpostf⟩ :=
        moddi3_tail g n d n ((0#64) - d) r (0x80004738#64) false m0 o ⟨σ5, i5, _⟩
          hG5 hwl5 hcl5 hmemq5 hout5 hpc5 hx10_5 hx11_5 hx1_5 hx5_5 ⟨v12, hx12_5⟩ ⟨v13, hx13_5⟩ hmi5 hi5 hBpos halign rfl
          (mag_notop n hntop) hBmag hd0 (by rw [toInt_of_notop n hntop]; exact Int.natCast_nonneg _ : 0 ≤ n.toInt) hframe5
      refine ⟨cf, ?_, hpostf⟩
      exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
        ((Steps.single hstep4).trans ((Steps.single hstep5).trans hsf))))
    · -- n < 0 (Path D): 4744 bgez nottaken → 4748 neg a0 → 474c jal → core (A=0-n, B=0-d), negate
      have hntop : 2^63 ≤ n.toNat := bgez_false' n hnlt
      have hnneg : n.toInt < 0 := by rw [toInt_of_top n hntop]; have := n.isLt; omega
      obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
        site3_80004744_nottaken σ3 i3 (c.steps + 1 + 1 + 1) (0x80004744#64) vmi3 n hG3 hpc3 hmi3v hx10_3 hwl3 rfl hnlt hi3
      have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
      have hpc4 : σ4.regs.get? Register.PC = some (0x80004748#64) := by
        have := obs_bnottaken_pc hobs4
        rwa [show BitVec.addInt (0x80004744#64 : BitVec 64) 4 = (0x80004748#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_4 : σ4.regs.get? Register.x10 = some n :=
        obs_bnottaken_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_3
      have hx11_4 : σ4.regs.get? Register.x11 = some ((0#64) - d) :=
        obs_bnottaken_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_3
      have hx1_4 : σ4.regs.get? Register.x1 = some r :=
        obs_bnottaken_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_3
      have hx5_4 : σ4.regs.get? Register.x5 = some r :=
        obs_bnottaken_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
      have hx12_4 : σ4.regs.get? Register.x12 = some v12 :=
        obs_bnottaken_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
      have hx13_4 : σ4.regs.get? Register.x13 = some v13 :=
        obs_bnottaken_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_3
      obtain ⟨vmi4, hmi4v⟩ := obs_bnottaken_minstret hobs4
      have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmemq3
      have hwl4 : Vsa.Sim.Code.__moddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hwl
      have hcl4 : __hidden___udivdi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hcl
      -- Step 4748: neg a0,a0 ⇒ x10 := 0 - n
      obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
        site3_80004748 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80004748#64) vmi4 n hG4 hpc4 hmi4v hx10_4 hwl4 rfl hi4
      have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
      have hpc5 : σ5.regs.get? Register.PC = some (0x8000474c#64) := by
        have := obs_alu_pc hobs5
        rwa [show BitVec.addInt (0x80004748#64 : BitVec 64) 4 = (0x8000474c#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_5 : σ5.regs.get? Register.x10 = some ((0#64) - n) :=
        obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
      have hx11_5 : σ5.regs.get? Register.x11 = some ((0#64) - d) :=
        obs_alu_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_4
      have hx1_5 : σ5.regs.get? Register.x1 = some r :=
        obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_4
      have hx5_5 : σ5.regs.get? Register.x5 = some r :=
        obs_alu_other hobs5 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_4
      have hx12_5 : σ5.regs.get? Register.x12 = some v12 :=
        obs_alu_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
      have hx13_5 : σ5.regs.get? Register.x13 = some v13 :=
        obs_alu_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_4
      obtain ⟨vmi5, hmi5v⟩ := obs_alu_minstret hobs5
      have hmemq5 : σ5.mem = m0 := by rw [hmem5]; exact hmemq4
      have hwl5 : Vsa.Sim.Code.__moddi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hwl
      have hcl5 : __hidden___udivdi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hcl
      -- Step 474c: jal ⇒ x1 := 0x4750, PC := 0x46ac
      obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
        site3_8000474c σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x8000474c#64) vmi5 hG5 hpc5 hmi5v hwl5 rfl hi5
      have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6
      have hpc6 : σ6.regs.get? Register.PC = some (0x800046ac#64) := by
        have := obs_jal_pc hobs6
        rwa [show (0x8000474c#64 : BitVec 64) + sign_extend (m := 64) (0x1fff60#21)
            = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
      have hx1_6 : σ6.regs.get? Register.x1 = some (0x80004750#64) := by
        have := obs_jal_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
        rwa [show BitVec.addInt (0x8000474c#64 : BitVec 64) 4 = (0x80004750#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_6 : σ6.regs.get? Register.x10 = some ((0#64) - n) :=
        obs_jal_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_5
      have hx11_6 : σ6.regs.get? Register.x11 = some ((0#64) - d) :=
        obs_jal_other hobs6 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_5
      have hx5_6 : σ6.regs.get? Register.x5 = some r :=
        obs_jal_other hobs6 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_5
      have hx12_6 : σ6.regs.get? Register.x12 = some v12 :=
        obs_jal_other hobs6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_5
      have hx13_6 : σ6.regs.get? Register.x13 = some v13 :=
        obs_jal_other hobs6 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_5
      have hmi6 : ∃ v, σ6.regs.get? Register.minstret = some v := obs_jal_minstret hobs6
      have hmemq6 : σ6.mem = m0 := by rw [hmem6]; exact hmemq5
      have hwl6 : Vsa.Sim.Code.__moddi3Loaded σ6.mem := hmemq6 ▸ hmem ▸ hwl
      have hcl6 : __hidden___udivdi3Loaded σ6.mem := hmemq6 ▸ hmem ▸ hcl
      have hAmag : ((0#64) - n).toNat = n.toInt.natAbs := mag_neg_top n hntop
      have hout6 : σ6.sailOutput = o := by
        rw [hobs6.out, sailOutput_sigmaPost_jal, hobs5.out, sailOutput_sigmaPost_alu,
          hobs4.out, sailOutput_sigmaPost_branch_nottaken, hobs3.out, sailOutput_sigmaPost_alu,
          hobs2.out, sailOutput_sigmaPost_branch_taken, hobs1.out, sailOutput_sigmaPost_alu]; exact hout
      have hframe6 : ∀ R : Register, NotWrittenD R → σ6.regs.get? R = g R := by
        intro R hR
        rw [frame_jal hobs6 R hR.2.1 hR.nw, frame_alu hobs5 R hR.nw.x10 hR.nw,
          frame_bnottaken hobs4 R hR.nw, frame_alu hobs3 R hR.nw.x11 hR.nw,
          frame_btaken hobs2 R hR.nw, frame_alu hobs1 R hR.2.2 hR.nw]
        exact hframeE R hR
      obtain ⟨cf, hsf, hpostf⟩ :=
        moddi3_tail g n d ((0#64) - n) ((0#64) - d) r (0x80004750#64) true m0 o ⟨σ6, i6, _⟩
          hG6 hwl6 hcl6 hmemq6 hout6 hpc6 hx10_6 hx11_6 hx1_6 hx5_6 ⟨v12, hx12_6⟩ ⟨v13, hx13_6⟩ hmi6 hi6 hBpos halign rfl
          hAmag hBmag hd0 hnneg hframe6
      refine ⟨cf, ?_, hpostf⟩
      exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
        ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans hsf)))))
  · -- d ≥ 0 arm: 472c nottaken → 4730 bltz a0
    have hdtop : d.toNat < 2^63 := bltz_false' d hdge
    have hBmag : d.toNat = d.toInt.natAbs := mag_notop d hdtop
    have hdInt : 0 ≤ d.toInt := by rw [toInt_of_notop d hdtop]; exact Int.natCast_nonneg _
    have hBpos : 0 < d.toNat := by
      rcases Nat.eq_zero_or_pos d.toNat with h0 | h0
      · exfalso; apply hd0; rw [toInt_of_notop d hdtop, h0]; simp
      · exact h0
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site3_8000472c_nottaken σ1 i1 (c.steps + 1) (0x8000472c#64) vmi1 d hG1 hpc1 hmi1v hx11_1 hwl1 rfl hdge hi1
    have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
    have hpc2 : σ2.regs.get? Register.PC = some (0x80004730#64) := by
      have := obs_bnottaken_pc hobs2
      rwa [show BitVec.addInt (0x8000472c#64 : BitVec 64) 4 = (0x80004730#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hx10_2 : σ2.regs.get? Register.x10 = some n :=
      obs_bnottaken_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_1
    have hx11_2 : σ2.regs.get? Register.x11 = some d :=
      obs_bnottaken_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_1
    have hx1_2 : σ2.regs.get? Register.x1 = some r :=
      obs_bnottaken_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_1
    have hx5_2 : σ2.regs.get? Register.x5 = some r :=
      obs_bnottaken_other hobs2 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_1
    have hx12_2 : σ2.regs.get? Register.x12 = some v12 :=
      obs_bnottaken_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
    have hx13_2 : σ2.regs.get? Register.x13 = some v13 :=
      obs_bnottaken_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
    obtain ⟨vmi2, hmi2v⟩ := obs_bnottaken_minstret hobs2
    have hmemq2 : σ2.mem = m0 := by rw [hmem2]; exact hmemq1
    have hwl2 : Vsa.Sim.Code.__moddi3Loaded σ2.mem := hmemq2 ▸ hmem ▸ hwl
    have hcl2 : __hidden___udivdi3Loaded σ2.mem := hmemq2 ▸ hmem ▸ hcl
    rcases bltz_cases' n with hnlt | hnge
    · -- n < 0 (Path B): 4730 bltz taken → 4748 neg a0 → 474c jal → core (A=0-n, B=d), negate
      have hntop : 2^63 ≤ n.toNat := bltz_true' n hnlt
      have hnneg : n.toInt < 0 := by rw [toInt_of_top n hntop]; have := n.isLt; omega
      obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
        site3_80004730_taken σ2 i2 (c.steps + 1 + 1) (0x80004730#64) vmi2 n hG2 hpc2 hmi2v hx10_2 hwl2 rfl hnlt hi2
      have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
      have hpc3 : σ3.regs.get? Register.PC = some (0x80004748#64) := by
        rw [obs_btaken_pc hobs3, show (0x80004730#64 : BitVec 64) + sign_extend (m := 64) (0x0018#13)
          = (0x80004748#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide]
      have hx10_3 : σ3.regs.get? Register.x10 = some n :=
        obs_btaken_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_2
      have hx11_3 : σ3.regs.get? Register.x11 = some d :=
        obs_btaken_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_2
      have hx1_3 : σ3.regs.get? Register.x1 = some r :=
        obs_btaken_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_2
      have hx5_3 : σ3.regs.get? Register.x5 = some r :=
        obs_btaken_other hobs3 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_2
      have hx12_3 : σ3.regs.get? Register.x12 = some v12 :=
        obs_btaken_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
      have hx13_3 : σ3.regs.get? Register.x13 = some v13 :=
        obs_btaken_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_2
      obtain ⟨vmi3, hmi3v⟩ := obs_btaken_minstret hobs3
      have hmemq3 : σ3.mem = m0 := by rw [hmem3]; exact hmemq2
      have hwl3 : Vsa.Sim.Code.__moddi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hwl
      have hcl3 : __hidden___udivdi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hcl
      -- Step 4748: neg a0,a0 ⇒ x10 := 0 - n
      obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
        site3_80004748 σ3 i3 (c.steps + 1 + 1 + 1) (0x80004748#64) vmi3 n hG3 hpc3 hmi3v hx10_3 hwl3 rfl hi3
      have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
      have hpc4 : σ4.regs.get? Register.PC = some (0x8000474c#64) := by
        have := obs_alu_pc hobs4
        rwa [show BitVec.addInt (0x80004748#64 : BitVec 64) 4 = (0x8000474c#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_4 : σ4.regs.get? Register.x10 = some ((0#64) - n) :=
        obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
      have hx11_4 : σ4.regs.get? Register.x11 = some d :=
        obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_3
      have hx1_4 : σ4.regs.get? Register.x1 = some r :=
        obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_3
      have hx5_4 : σ4.regs.get? Register.x5 = some r :=
        obs_alu_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
      have hx12_4 : σ4.regs.get? Register.x12 = some v12 :=
        obs_alu_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
      have hx13_4 : σ4.regs.get? Register.x13 = some v13 :=
        obs_alu_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_3
      obtain ⟨vmi4, hmi4v⟩ := obs_alu_minstret hobs4
      have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmemq3
      have hwl4 : Vsa.Sim.Code.__moddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hwl
      have hcl4 : __hidden___udivdi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hcl
      obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
        site3_8000474c σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000474c#64) vmi4 hG4 hpc4 hmi4v hwl4 rfl hi4
      have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
      have hpc5 : σ5.regs.get? Register.PC = some (0x800046ac#64) := by
        have := obs_jal_pc hobs5
        rwa [show (0x8000474c#64 : BitVec 64) + sign_extend (m := 64) (0x1fff60#21)
            = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
      have hx1_5 : σ5.regs.get? Register.x1 = some (0x80004750#64) := by
        have := obs_jal_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
        rwa [show BitVec.addInt (0x8000474c#64 : BitVec 64) 4 = (0x80004750#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_5 : σ5.regs.get? Register.x10 = some ((0#64) - n) :=
        obs_jal_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
      have hx11_5 : σ5.regs.get? Register.x11 = some d :=
        obs_jal_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_4
      have hx5_5 : σ5.regs.get? Register.x5 = some r :=
        obs_jal_other hobs5 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_4
      have hx12_5 : σ5.regs.get? Register.x12 = some v12 :=
        obs_jal_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
      have hx13_5 : σ5.regs.get? Register.x13 = some v13 :=
        obs_jal_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_4
      have hmi5 : ∃ v, σ5.regs.get? Register.minstret = some v := obs_jal_minstret hobs5
      have hmemq5 : σ5.mem = m0 := by rw [hmem5]; exact hmemq4
      have hwl5 : Vsa.Sim.Code.__moddi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hwl
      have hcl5 : __hidden___udivdi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hcl
      have hAmag : ((0#64) - n).toNat = n.toInt.natAbs := mag_neg_top n hntop
      have hout5 : σ5.sailOutput = o := by
        rw [hobs5.out, sailOutput_sigmaPost_jal, hobs4.out, sailOutput_sigmaPost_alu,
          hobs3.out, sailOutput_sigmaPost_branch_taken, hobs2.out, sailOutput_sigmaPost_branch_nottaken,
          hobs1.out, sailOutput_sigmaPost_alu]; exact hout
      have hframe5 : ∀ R : Register, NotWrittenD R → σ5.regs.get? R = g R := by
        intro R hR
        rw [frame_jal hobs5 R hR.2.1 hR.nw, frame_alu hobs4 R hR.nw.x10 hR.nw,
          frame_btaken hobs3 R hR.nw, frame_bnottaken hobs2 R hR.nw,
          frame_alu hobs1 R hR.2.2 hR.nw]
        exact hframeE R hR
      obtain ⟨cf, hsf, hpostf⟩ :=
        moddi3_tail g n d ((0#64) - n) d r (0x80004750#64) true m0 o ⟨σ5, i5, _⟩
          hG5 hwl5 hcl5 hmemq5 hout5 hpc5 hx10_5 hx11_5 hx1_5 hx5_5 ⟨v12, hx12_5⟩ ⟨v13, hx13_5⟩ hmi5 hi5 hBpos halign rfl
          hAmag hBmag hd0 hnneg hframe5
      refine ⟨cf, ?_, hpostf⟩
      exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
        ((Steps.single hstep4).trans ((Steps.single hstep5).trans hsf))))
    · -- n ≥ 0 (Path A): 4730 bltz nottaken → 4734 jal → core (A=n, B=d), no negate
      have hntop : n.toNat < 2^63 := bltz_false' n hnge
      obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
        site3_80004730_nottaken σ2 i2 (c.steps + 1 + 1) (0x80004730#64) vmi2 n hG2 hpc2 hmi2v hx10_2 hwl2 rfl hnge hi2
      have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
      have hpc3 : σ3.regs.get? Register.PC = some (0x80004734#64) := by
        have := obs_bnottaken_pc hobs3
        rwa [show BitVec.addInt (0x80004730#64 : BitVec 64) 4 = (0x80004734#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_3 : σ3.regs.get? Register.x10 = some n :=
        obs_bnottaken_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_2
      have hx11_3 : σ3.regs.get? Register.x11 = some d :=
        obs_bnottaken_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_2
      have hx1_3 : σ3.regs.get? Register.x1 = some r :=
        obs_bnottaken_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_2
      have hx5_3 : σ3.regs.get? Register.x5 = some r :=
        obs_bnottaken_other hobs3 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_2
      have hx12_3 : σ3.regs.get? Register.x12 = some v12 :=
        obs_bnottaken_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
      have hx13_3 : σ3.regs.get? Register.x13 = some v13 :=
        obs_bnottaken_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_2
      obtain ⟨vmi3, hmi3v⟩ := obs_bnottaken_minstret hobs3
      have hmemq3 : σ3.mem = m0 := by rw [hmem3]; exact hmemq2
      have hwl3 : Vsa.Sim.Code.__moddi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hwl
      have hcl3 : __hidden___udivdi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hcl
      obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
        site3_80004734 σ3 i3 (c.steps + 1 + 1 + 1) (0x80004734#64) vmi3 hG3 hpc3 hmi3v hwl3 rfl hi3
      have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
      have hpc4 : σ4.regs.get? Register.PC = some (0x800046ac#64) := by
        have := obs_jal_pc hobs4
        rwa [show (0x80004734#64 : BitVec 64) + sign_extend (m := 64) (0x1fff78#21)
            = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
      have hx1_4 : σ4.regs.get? Register.x1 = some (0x80004738#64) := by
        have := obs_jal_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
        rwa [show BitVec.addInt (0x80004734#64 : BitVec 64) 4 = (0x80004738#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_4 : σ4.regs.get? Register.x10 = some n :=
        obs_jal_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_3
      have hx11_4 : σ4.regs.get? Register.x11 = some d :=
        obs_jal_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_3
      have hx5_4 : σ4.regs.get? Register.x5 = some r :=
        obs_jal_other hobs4 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_3
      have hx12_4 : σ4.regs.get? Register.x12 = some v12 :=
        obs_jal_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
      have hx13_4 : σ4.regs.get? Register.x13 = some v13 :=
        obs_jal_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_3
      have hmi4 : ∃ v, σ4.regs.get? Register.minstret = some v := obs_jal_minstret hobs4
      have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmemq3
      have hwl4 : Vsa.Sim.Code.__moddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hwl
      have hcl4 : __hidden___udivdi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hcl
      have hnge' : 0 ≤ n.toInt := by rw [toInt_of_notop n hntop]; exact Int.natCast_nonneg _
      have hout4 : σ4.sailOutput = o := by
        rw [hobs4.out, sailOutput_sigmaPost_jal, hobs3.out, sailOutput_sigmaPost_branch_nottaken,
          hobs2.out, sailOutput_sigmaPost_branch_nottaken, hobs1.out, sailOutput_sigmaPost_alu]; exact hout
      have hframe4 : ∀ R : Register, NotWrittenD R → σ4.regs.get? R = g R := by
        intro R hR
        rw [frame_jal hobs4 R hR.2.1 hR.nw, frame_bnottaken hobs3 R hR.nw,
          frame_bnottaken hobs2 R hR.nw, frame_alu hobs1 R hR.2.2 hR.nw]
        exact hframeE R hR
      obtain ⟨cf, hsf, hpostf⟩ :=
        moddi3_tail g n d n d r (0x80004738#64) false m0 o ⟨σ4, i4, _⟩
          hG4 hwl4 hcl4 hmemq4 hout4 hpc4 hx10_4 hx11_4 hx1_4 hx5_4 ⟨v12, hx12_4⟩ ⟨v13, hx13_4⟩ hmi4 hi4 hBpos halign rfl
          (mag_notop n hntop) hBmag hd0 hnge' hframe4
      refine ⟨cf, ?_, hpostf⟩
      exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
        ((Steps.single hstep4).trans hsf)))

/-! ## `__divdi3` — signed quotient (entry `0x800046a4`) -/

/-- `divdi3_pre`: at `0x800046a4` with `x10 = n`, `x11 = d`, `x1 = r`, `mem = m0`,
`d ≠ 0`, `¬(n = INT64_MIN ∧ d = -1)` (excludes the sole `tdiv` overflow, which the
`__divdi3` entry does not guard), `r` 4-aligned, wrapper + core loaded, `sailOutput
= o`, and the entry ghost-frame `hframe` (every `NotWrittenD` register reads as the
entry snapshot `g`). Carries `g`/`o` exactly as `muldi3_pre`. -/
def divdi3_pre (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ Vsa.Sim.Code.__divdi3Loaded c.σ.mem ∧ Vsa.Sim.Code.__umoddi3Loaded c.σ.mem ∧
  __hidden___udivdi3Loaded c.σ.mem ∧
  c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some (0x800046a4#64) ∧
  c.σ.regs.get? Register.x10 = some n ∧ c.σ.regs.get? Register.x11 = some d ∧
  c.σ.regs.get? Register.x1 = some r ∧ (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  (∃ v, c.σ.regs.get? Register.x12 = some v) ∧ (∃ v, c.σ.regs.get? Register.x13 = some v) ∧
  c.tick < 2 ∧ d.toInt ≠ 0 ∧ ¬(n.toInt = -2^63 ∧ d.toInt = -1) ∧ r.toNat % 4 = 0 ∧
  (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R)

/-- `divdi3_post`: PC back at `r`, `x10.toInt = n.toInt.tdiv d.toInt`, `GoodState`,
`mem = m0`, `sailOutput = o`, `tick < 2`, and the blanket ghost frame over
`NotWrittenD` — the strong post matching `muldi3_post` (note `x1`/`ra` and
`x5`/`t0` are genuinely clobbered by the wrapper's internal `jal`/`mv t0,ra`, so
they are excluded from the frame set `NotWrittenD` rather than pinned to `r`). -/
def divdi3_post (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some r ∧
  c.tick < 2 ∧
  (∀ R : Register, NotWrittenD R → c.σ.regs.get? R = g R) ∧
  ∃ res, c.σ.regs.get? Register.x10 = some res ∧ res.toInt = n.toInt.tdiv d.toInt

/-- Mixed-sign tail (`0x4720 neg a0,a0 ; 0x4724 jr t0`): from the core entry
`0x46ac` with `x1 = 0x4720`, `x5 = r`, run core then negate the quotient and
return via `t0`. Delivers the strong `divdi3_post` with `res = 0 - (A / B)`,
threading the entry ghost frame `hframe0` (`cA → g`) and `sailOutput` through the
core and the two fixup steps. -/
theorem divdi3_mixed_tail
    (g : (R : Register) → Option (RegisterType R))
    (n d A B r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (cA : Config)
    (hG : GoodState cA.σ) (hwl : Vsa.Sim.Code.__umoddi3Loaded cA.σ.mem)
    (hcl : __hidden___udivdi3Loaded cA.σ.mem) (hmem : cA.σ.mem = m0)
    (hout : cA.σ.sailOutput = o)
    (hpc : cA.σ.regs.get? Register.PC = some (0x800046ac#64))
    (hx10 : cA.σ.regs.get? Register.x10 = some A)
    (hx11 : cA.σ.regs.get? Register.x11 = some B)
    (hx1 : cA.σ.regs.get? Register.x1 = some (0x80004720#64))
    (hx5 : cA.σ.regs.get? Register.x5 = some r)
    (hx12 : ∃ v, cA.σ.regs.get? Register.x12 = some v)
    (hx13 : ∃ v, cA.σ.regs.get? Register.x13 = some v)
    (hmi : ∃ v, cA.σ.regs.get? Register.minstret = some v)
    (htick : cA.tick < 2) (hBpos : 0 < B.toNat) (halign : r.toNat % 4 = 0)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hd0 : d.toInt ≠ 0) (hdiff : ¬(0 ≤ n.toInt ↔ 0 ≤ d.toInt))
    (hframe0 : ∀ R : Register, NotWrittenD R → cA.σ.regs.get? R = g R) :
    ∃ c' : Config, Steps cA c' ∧ divdi3_post g n d r m0 o c' := by
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, hrem3, _hra3, htick3, hframe3, hmi3⟩ :=
    core_call_tail_f A B r (0x80004720#64) m0 o cA hG hcl hmem hout hpc hx10 hx11 hx1 hx12 hx13 hmi htick hBpos (by decide)
  have hwl3 : Vsa.Sim.Code.__umoddi3Loaded c3.σ.mem := hmem3 ▸ hmem ▸ hwl
  obtain ⟨vmi3, hmi3v⟩ := hmi3
  -- Step 4720: neg a0,a0 ⇒ x10 := 0 - (A/B)
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site3_80004720 c3.σ c3.tick c3.steps (0x80004720#64) vmi3 (A / B) hG3 hpc3 hmi3v hq3 hwl3 rfl htick3
  have hstep4 : Step c3 ⟨σ4, i4, c3.steps + 1⟩ := by cases c3; exact hs4
  have hpc4 : σ4.regs.get? Register.PC = some (0x80004724#64) := by
    have := obs_alu_pc hobs4
    rwa [show BitVec.addInt (0x80004720#64 : BitVec 64) 4 = (0x80004724#64 : BitVec 64) from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hx10_4 : σ4.regs.get? Register.x10 = some ((0#64) - (A / B)) :=
    obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmem3
  have hwl4 : Vsa.Sim.Code.__umoddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hwl
  -- x5 (= t0 = r) still live for the `jr t0`: preserved through `neg a0` (rd = x10)
  have hx5_4 : σ4.regs.get? Register.x5 = some r := by
    have := hframe3 Register.x5 (by decide)
    rw [frame_alu hobs4 Register.x5 (by decide) (by decide), this]; exact hx5
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site3_80004724 σ4 i4 (c3.steps + 1) (0x80004724#64) vmi4 r hG4 hpc4 hmi4 hx5_4 hwl4 rfl htgt hi4
  have hstep5 : Step ⟨σ4, i4, c3.steps + 1⟩ ⟨σ5, i5, c3.steps + 1 + 1⟩ := hs5
  refine ⟨⟨σ5, i5, c3.steps + 1 + 1⟩, ?_, hG5, ?_, ?_, ?_, hi5, ?_, (0#64) - (A / B), ?_, ?_⟩
  · exact hs3.trans ((Steps.single hstep4).trans ((Steps.single hstep5).trans (.refl _)))
  · rw [hmem5]; exact hmemq4
  · -- sailOutput = o through neg + jr
    rw [hobs5.out, hobs4.out, sailOutput_sigmaPost_alu, hout3]
  · rw [obs_jr_pc hobs5, ret_tgt r halign]
  · -- frame: NotWrittenD R preserved through jr, neg (rd=x10), core, entry→g
    intro R hR
    rw [frame_jr hobs5 R hR.nw, frame_alu hobs4 R (by
        have := hR.nw.x10; exact this) hR.nw, hframe3 R hR.nw]
    exact hframe0 R hR
  · exact obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
  · exact res_div_mixed n d A B hA hB hdiff hd0

/-- Same-sign tail: from core entry `0x46ac` with `x1 = r` (the caller's own
return address), the core returns straight to `r` with `x10 = A / B`. Delivers
the strong `divdi3_post` with `res = A / B` (no fixup), threading the entry ghost
frame `hframe0` and `sailOutput` through the core. -/
theorem divdi3_same_tail
    (g : (R : Register) → Option (RegisterType R))
    (n d A B r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (cA : Config)
    (hG : GoodState cA.σ)
    (hcl : __hidden___udivdi3Loaded cA.σ.mem) (hmem : cA.σ.mem = m0)
    (hout : cA.σ.sailOutput = o)
    (hpc : cA.σ.regs.get? Register.PC = some (0x800046ac#64))
    (hx10 : cA.σ.regs.get? Register.x10 = some A)
    (hx11 : cA.σ.regs.get? Register.x11 = some B)
    (hx1 : cA.σ.regs.get? Register.x1 = some r)
    (hx12 : ∃ v, cA.σ.regs.get? Register.x12 = some v)
    (hx13 : ∃ v, cA.σ.regs.get? Register.x13 = some v)
    (hmi : ∃ v, cA.σ.regs.get? Register.minstret = some v)
    (htick : cA.tick < 2) (hBpos : 0 < B.toNat) (halign : r.toNat % 4 = 0)
    (hA : A.toNat = n.toInt.natAbs) (hB : B.toNat = d.toInt.natAbs)
    (hd0 : d.toInt ≠ 0) (hsame : 0 ≤ n.toInt ↔ 0 ≤ d.toInt)
    (hnov : (A / B).toNat < 2^63)
    (hframe0 : ∀ R : Register, NotWrittenD R → cA.σ.regs.get? R = g R) :
    ∃ c' : Config, Steps cA c' ∧ divdi3_post g n d r m0 o c' := by
  obtain ⟨c3, hs3, hG3, hmem3, hout3, hpc3, hq3, _hrem3, _hra3, htick3, hframe3, _hmi3⟩ :=
    core_call_tail_f A B r r m0 o cA hG hcl hmem hout hpc hx10 hx11 hx1 hx12 hx13 hmi htick hBpos halign
  refine ⟨c3, hs3, hG3, hmem3, hout3, hpc3, htick3, ?_, A / B, hq3,
    res_div_same n d A B hA hB hsame hd0 hnov⟩
  -- frame: core frame (rel cA) composed with entry frame hframe0
  intro R hR
  rw [hframe3 R hR.nw]; exact hframe0 R hR

/-- **`divdi3_spec`** — total-correctness triple for libgcc `__divdi3` (signed
64-bit quotient). Negates each negative operand, calls the unsigned core on `|n|`,
`|d|`, and negates the quotient iff the operand signs differ; same-sign paths reuse
the caller's return slot directly. Result: `x10.toInt = n.toInt.tdiv d.toInt`,
excluding the `INT64_MIN / -1` overflow input (unrepresentable `+2^63`, and not
guarded by the `__divdi3` entry). -/
theorem divdi3_spec (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (divdi3_pre g n d r m0 o) (divdi3_post g n d r m0 o) := by
  intro c hc
  obtain ⟨hG, hdl, hul, hcl, hmem, hout, hpc, hn, hd, hr, ⟨vmi, hmi⟩,
    ⟨v12, h12⟩, ⟨v13, h13⟩, htick, hd0, hexcl, halign, hframeE⟩ := hc
  -- magnitude/positivity facts for d
  have hdcases := bltz_cases' d
  -- Branch on sign of n at 0x46a4 (`bltz a0`)
  rcases bltz_cases' n with hnlt | hnge
  · -- n < 0: 46a4 taken → 4704 neg a0 → 4708 bgtz a1
    have hntop : 2^63 ≤ n.toNat := bltz_true' n hnlt
    have hnneg : n.toInt < 0 := by rw [toInt_of_top n hntop]; have := n.isLt; omega
    have hAmag : ((0#64) - n).toNat = n.toInt.natAbs := mag_neg_top n hntop
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site2_800046a4_taken c.σ c.tick c.steps (0x800046a4#64) vmi n hG hpc hmi hn (hmem ▸ hdl) rfl hnlt htick
    have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
    have hpc1 : σ1.regs.get? Register.PC = some (0x80004704#64) := by
      rw [obs_btaken_pc hobs1, show (0x800046a4#64 : BitVec 64) + sign_extend (m := 64) (0x0060#13)
        = (0x80004704#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide]
    have hx10_1 : σ1.regs.get? Register.x10 = some n :=
      obs_btaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn
    have hx11_1 : σ1.regs.get? Register.x11 = some d :=
      obs_btaken_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd
    have hx1_1 : σ1.regs.get? Register.x1 = some r :=
      obs_btaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hr
    have hx12_1 : σ1.regs.get? Register.x12 = some v12 :=
      obs_btaken_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12
    have hx13_1 : σ1.regs.get? Register.x13 = some v13 :=
      obs_btaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13
    obtain ⟨vmi1, hmi1v⟩ := obs_btaken_minstret hobs1
    have hmemq1 : σ1.mem = m0 := by rw [hmem1]; exact hmem
    have hul1 : Vsa.Sim.Code.__umoddi3Loaded σ1.mem := hmemq1 ▸ hmem ▸ hul
    have hcl1 : __hidden___udivdi3Loaded σ1.mem := hmemq1 ▸ hmem ▸ hcl
    -- Step 4704: neg a0,a0 ⇒ x10 := 0 - n
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site3_80004704 σ1 i1 (c.steps + 1) (0x80004704#64) vmi1 n hG1 hpc1 hmi1v hx10_1 hul1 rfl hi1
    have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
    have hpc2 : σ2.regs.get? Register.PC = some (0x80004708#64) := by
      have := obs_alu_pc hobs2
      rwa [show BitVec.addInt (0x80004704#64 : BitVec 64) 4 = (0x80004708#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hx10_2 : σ2.regs.get? Register.x10 = some ((0#64) - n) :=
      obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hx11_2 : σ2.regs.get? Register.x11 = some d :=
      obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_1
    have hx1_2 : σ2.regs.get? Register.x1 = some r :=
      obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_1
    have hx12_2 : σ2.regs.get? Register.x12 = some v12 :=
      obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
    have hx13_2 : σ2.regs.get? Register.x13 = some v13 :=
      obs_alu_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
    obtain ⟨vmi2, hmi2v⟩ := obs_alu_minstret hobs2
    have hmemq2 : σ2.mem = m0 := by rw [hmem2]; exact hmemq1
    have hul2 : Vsa.Sim.Code.__umoddi3Loaded σ2.mem := hmemq2 ▸ hmem ▸ hul
    have hcl2 : __hidden___udivdi3Loaded σ2.mem := hmemq2 ▸ hmem ▸ hcl
    -- Branch on sign of d at 0x4708 (`bgtz a1`)
    rcases bgtz_cases' d with hdgt | hdle
    · -- d > 0 (MX-A, mixed): 4708 taken → 4718 mv t0,ra → 471c jal → mixed_tail
      have hdpos : 0 < d.toInt := bgtz_true' d hdgt
      have hdInt0 : 0 ≤ d.toInt := Int.le_of_lt hdpos
      have hdtop : d.toNat < 2^63 := by
        by_cases hc' : d.toNat < 2^63
        · exact hc'
        · rw [toInt_of_top d (by omega)] at hdpos; have := d.isLt; omega
      have hBmag : d.toNat = d.toInt.natAbs := mag_notop d hdtop
      have hBpos : 0 < d.toNat := by rw [hBmag]; have : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h); omega
      have hdiff : ¬(0 ≤ n.toInt ↔ 0 ≤ d.toInt) := fun hi => absurd (hi.mpr hdInt0) (by omega)
      obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
        site3_80004708_taken σ2 i2 (c.steps + 1 + 1) (0x80004708#64) vmi2 d hG2 hpc2 hmi2v hx11_2 hul2 rfl hdgt hi2
      have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
      have hpc3 : σ3.regs.get? Register.PC = some (0x80004718#64) := by
        rw [obs_btaken_pc hobs3, show (0x80004708#64 : BitVec 64) + sign_extend (m := 64) (0x0010#13)
          = (0x80004718#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide]
      have hx10_3 : σ3.regs.get? Register.x10 = some ((0#64) - n) :=
        obs_btaken_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_2
      have hx11_3 : σ3.regs.get? Register.x11 = some d :=
        obs_btaken_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_2
      have hx1_3 : σ3.regs.get? Register.x1 = some r :=
        obs_btaken_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_2
      have hx12_3 : σ3.regs.get? Register.x12 = some v12 :=
        obs_btaken_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
      have hx13_3 : σ3.regs.get? Register.x13 = some v13 :=
        obs_btaken_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_2
      obtain ⟨vmi3, hmi3v⟩ := obs_btaken_minstret hobs3
      have hmemq3 : σ3.mem = m0 := by rw [hmem3]; exact hmemq2
      have hul3 : Vsa.Sim.Code.__umoddi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hul
      have hcl3 : __hidden___udivdi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hcl
      -- Step 4718: mv t0,ra ⇒ x5 := r
      obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
        site3_80004718 σ3 i3 (c.steps + 1 + 1 + 1) (0x80004718#64) vmi3 r hG3 hpc3 hmi3v hx1_3 hul3 rfl hi3
      have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
      have hpc4 : σ4.regs.get? Register.PC = some (0x8000471c#64) := by
        have := obs_alu_pc hobs4
        rwa [show BitVec.addInt (0x80004718#64 : BitVec 64) 4 = (0x8000471c#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx5_4 : σ4.regs.get? Register.x5 = some r := by
        have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
        rwa [addi0 r] at this
      have hx10_4 : σ4.regs.get? Register.x10 = some ((0#64) - n) :=
        obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_3
      have hx11_4 : σ4.regs.get? Register.x11 = some d :=
        obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_3
      have hx12_4 : σ4.regs.get? Register.x12 = some v12 :=
        obs_alu_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
      have hx13_4 : σ4.regs.get? Register.x13 = some v13 :=
        obs_alu_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_3
      obtain ⟨vmi4, hmi4v⟩ := obs_alu_minstret hobs4
      have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmemq3
      have hul4 : Vsa.Sim.Code.__umoddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hul
      have hcl4 : __hidden___udivdi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hcl
      -- Step 471c: jal ⇒ x1 := 0x4720, PC := 0x46ac
      obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
        site3_8000471c σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000471c#64) vmi4 hG4 hpc4 hmi4v hul4 rfl hi4
      have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
      have hpc5 : σ5.regs.get? Register.PC = some (0x800046ac#64) := by
        have := obs_jal_pc hobs5
        rwa [show (0x8000471c#64 : BitVec 64) + sign_extend (m := 64) (0x1fff90#21)
            = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
      have hx1_5 : σ5.regs.get? Register.x1 = some (0x80004720#64) := by
        have := obs_jal_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
        rwa [show BitVec.addInt (0x8000471c#64 : BitVec 64) 4 = (0x80004720#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_5 : σ5.regs.get? Register.x10 = some ((0#64) - n) :=
        obs_jal_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
      have hx11_5 : σ5.regs.get? Register.x11 = some d :=
        obs_jal_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_4
      have hx5_5 : σ5.regs.get? Register.x5 = some r :=
        obs_jal_other hobs5 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_4
      have hx12_5 : σ5.regs.get? Register.x12 = some v12 :=
        obs_jal_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
      have hx13_5 : σ5.regs.get? Register.x13 = some v13 :=
        obs_jal_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_4
      have hmi5 : ∃ v, σ5.regs.get? Register.minstret = some v := obs_jal_minstret hobs5
      have hmemq5 : σ5.mem = m0 := by rw [hmem5]; exact hmemq4
      have hul5 : Vsa.Sim.Code.__umoddi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hul
      have hcl5 : __hidden___udivdi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hcl
      -- sailOutput o and entry-frame g threaded to σ5 (btaken ; neg ; btaken ; mv ; jal)
      have hout5 : σ5.sailOutput = o := by
        rw [hobs5.out, sailOutput_sigmaPost_jal, hobs4.out, sailOutput_sigmaPost_alu,
          hobs3.out, sailOutput_sigmaPost_branch_taken, hobs2.out, sailOutput_sigmaPost_alu,
          hobs1.out, sailOutput_sigmaPost_branch_taken]; exact hout
      have hframe5 : ∀ R : Register, NotWrittenD R → σ5.regs.get? R = g R := by
        intro R hR
        rw [frame_jal hobs5 R hR.2.1 hR.nw, frame_alu hobs4 R hR.2.2 hR.nw,
          frame_btaken hobs3 R hR.nw, frame_alu hobs2 R hR.nw.x10 hR.nw,
          frame_btaken hobs1 R hR.nw]
        exact hframeE R hR
      obtain ⟨cf, hsf, hpostf⟩ :=
        divdi3_mixed_tail g n d ((0#64) - n) d r m0 o ⟨σ5, i5, _⟩
          hG5 hul5 hcl5 hmemq5 hout5 hpc5 hx10_5 hx11_5 hx1_5 hx5_5 ⟨v12, hx12_5⟩ ⟨v13, hx13_5⟩ hmi5 hi5 hBpos halign
          hAmag hBmag hd0 hdiff hframe5
      refine ⟨cf, ?_, hpostf⟩
      exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
        ((Steps.single hstep4).trans ((Steps.single hstep5).trans hsf))))
    · -- d ≤ 0, and d ≠ 0 ⇒ d < 0 (SS-B, both neg): 4708 nottaken → 470c neg a1 → 4710 j → same_tail
      have hdle' : d.toInt ≤ 0 := bgtz_false' d hdle
      have hdneg : d.toInt < 0 := by
        rcases Int.lt_trichotomy d.toInt 0 with h | h | h
        · exact h
        · exact absurd h hd0
        · omega
      have hdtop : 2^63 ≤ d.toNat := by
        by_cases hc' : d.toNat < 2^63
        · rw [toInt_of_notop d hc'] at hdneg; have := d.isLt; omega
        · omega
      have hBmag : ((0#64) - d).toNat = d.toInt.natAbs := mag_neg_top d hdtop
      have hBpos : 0 < ((0#64) - d).toNat := by
        rw [hBmag]; have : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h); omega
      have hsame : (0 ≤ n.toInt ↔ 0 ≤ d.toInt) := ⟨fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
      have hnov : (((0#64) - n) / ((0#64) - d)).toNat < 2^63 :=
        udiv_lt_of_not_overflow n d ((0#64) - n) ((0#64) - d) hAmag hBmag hsame hd0 hexcl
      obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
        site3_80004708_nottaken σ2 i2 (c.steps + 1 + 1) (0x80004708#64) vmi2 d hG2 hpc2 hmi2v hx11_2 hul2 rfl hdle hi2
      have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
      have hpc3 : σ3.regs.get? Register.PC = some (0x8000470c#64) := by
        have := obs_bnottaken_pc hobs3
        rwa [show BitVec.addInt (0x80004708#64 : BitVec 64) 4 = (0x8000470c#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_3 : σ3.regs.get? Register.x10 = some ((0#64) - n) :=
        obs_bnottaken_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_2
      have hx11_3 : σ3.regs.get? Register.x11 = some d :=
        obs_bnottaken_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_2
      have hx1_3 : σ3.regs.get? Register.x1 = some r :=
        obs_bnottaken_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_2
      have hx12_3 : σ3.regs.get? Register.x12 = some v12 :=
        obs_bnottaken_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
      have hx13_3 : σ3.regs.get? Register.x13 = some v13 :=
        obs_bnottaken_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_2
      obtain ⟨vmi3, hmi3v⟩ := obs_bnottaken_minstret hobs3
      have hmemq3 : σ3.mem = m0 := by rw [hmem3]; exact hmemq2
      have hul3 : Vsa.Sim.Code.__umoddi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hul
      have hcl3 : __hidden___udivdi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hcl
      -- Step 470c: neg a1,a1 ⇒ x11 := 0 - d
      obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
        site3_8000470c σ3 i3 (c.steps + 1 + 1 + 1) (0x8000470c#64) vmi3 d hG3 hpc3 hmi3v hx11_3 hul3 rfl hi3
      have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
      have hpc4 : σ4.regs.get? Register.PC = some (0x80004710#64) := by
        have := obs_alu_pc hobs4
        rwa [show BitVec.addInt (0x8000470c#64 : BitVec 64) 4 = (0x80004710#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx11_4 : σ4.regs.get? Register.x11 = some ((0#64) - d) :=
        obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
      have hx10_4 : σ4.regs.get? Register.x10 = some ((0#64) - n) :=
        obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_3
      have hx1_4 : σ4.regs.get? Register.x1 = some r :=
        obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_3
      have hx12_4 : σ4.regs.get? Register.x12 = some v12 :=
        obs_alu_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
      have hx13_4 : σ4.regs.get? Register.x13 = some v13 :=
        obs_alu_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_3
      obtain ⟨vmi4, hmi4v⟩ := obs_alu_minstret hobs4
      have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmemq3
      have hul4 : Vsa.Sim.Code.__umoddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hul
      have hcl4 : __hidden___udivdi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hcl
      -- Step 4710: j 0x46ac
      obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
        site2_80004710 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80004710#64) vmi4 hG4 hpc4 hmi4v hul4 rfl hi4
      have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
      have hpc5 : σ5.regs.get? Register.PC = some (0x800046ac#64) := by
        have := obs_jr_pc hobs5
        rwa [show ((0x80004710#64 : BitVec 64) + sign_extend (m := 64) (0x1fff9c#21))
            = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_5 : σ5.regs.get? Register.x10 = some ((0#64) - n) :=
        obs_jr_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
      have hx11_5 : σ5.regs.get? Register.x11 = some ((0#64) - d) :=
        obs_jr_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_4
      have hx1_5 : σ5.regs.get? Register.x1 = some r :=
        obs_jr_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_4
      have hx12_5 : σ5.regs.get? Register.x12 = some v12 :=
        obs_jr_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
      have hx13_5 : σ5.regs.get? Register.x13 = some v13 :=
        obs_jr_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_4
      obtain ⟨vmi5, hmi5v⟩ := obs_jr_minstret hobs5
      have hmemq5 : σ5.mem = m0 := by rw [hmem5]; exact hmemq4
      have hcl5 : __hidden___udivdi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hcl
      -- sailOutput o and entry-frame g threaded to σ5 (btaken ; neg ; bnottaken ; neg ; jr)
      have hout5 : σ5.sailOutput = o := by
        rw [hobs5.out, sailOutput_sigmaPost_jump_x0, hobs4.out, sailOutput_sigmaPost_alu,
          hobs3.out, sailOutput_sigmaPost_branch_nottaken, hobs2.out, sailOutput_sigmaPost_alu,
          hobs1.out, sailOutput_sigmaPost_branch_taken]; exact hout
      have hframe5 : ∀ R : Register, NotWrittenD R → σ5.regs.get? R = g R := by
        intro R hR
        rw [frame_jr hobs5 R hR.nw, frame_alu hobs4 R hR.nw.x11 hR.nw,
          frame_bnottaken hobs3 R hR.nw, frame_alu hobs2 R hR.nw.x10 hR.nw,
          frame_btaken hobs1 R hR.nw]
        exact hframeE R hR
      obtain ⟨cf, hsf, hpostf⟩ :=
        divdi3_same_tail g n d ((0#64) - n) ((0#64) - d) r m0 o ⟨σ5, i5, _⟩
          hG5 hcl5 hmemq5 hout5 hpc5 hx10_5 hx11_5 hx1_5 ⟨v12, hx12_5⟩ ⟨v13, hx13_5⟩ ⟨vmi5, hmi5v⟩ hi5 hBpos halign
          hAmag hBmag hd0 hsame hnov hframe5
      refine ⟨cf, ?_, hpostf⟩
      exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
        ((Steps.single hstep4).trans ((Steps.single hstep5).trans hsf))))
  · -- n ≥ 0: 46a4 nottaken → 46a8 bltz a1
    have hntop : n.toNat < 2^63 := bltz_false' n hnge
    have hnInt : 0 ≤ n.toInt := by rw [toInt_of_notop n hntop]; exact Int.natCast_nonneg _
    have hAmag : n.toNat = n.toInt.natAbs := mag_notop n hntop
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site2_800046a4_nottaken c.σ c.tick c.steps (0x800046a4#64) vmi n hG hpc hmi hn (hmem ▸ hdl) rfl hnge htick
    have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1
    have hpc1 : σ1.regs.get? Register.PC = some (0x800046a8#64) := by
      have := obs_bnottaken_pc hobs1
      rwa [show BitVec.addInt (0x800046a4#64 : BitVec 64) 4 = (0x800046a8#64 : BitVec 64) from by
        apply BitVec.eq_of_toNat_eq; decide] at this
    have hx10_1 : σ1.regs.get? Register.x10 = some n :=
      obs_bnottaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn
    have hx11_1 : σ1.regs.get? Register.x11 = some d :=
      obs_bnottaken_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hd
    have hx1_1 : σ1.regs.get? Register.x1 = some r :=
      obs_bnottaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hr
    have hx12_1 : σ1.regs.get? Register.x12 = some v12 :=
      obs_bnottaken_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h12
    have hx13_1 : σ1.regs.get? Register.x13 = some v13 :=
      obs_bnottaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h13
    obtain ⟨vmi1, hmi1v⟩ := obs_bnottaken_minstret hobs1
    have hmemq1 : σ1.mem = m0 := by rw [hmem1]; exact hmem
    have hdl1 : Vsa.Sim.Code.__divdi3Loaded σ1.mem := hmemq1 ▸ hmem ▸ hdl
    have hul1 : Vsa.Sim.Code.__umoddi3Loaded σ1.mem := hmemq1 ▸ hmem ▸ hul
    have hcl1 : __hidden___udivdi3Loaded σ1.mem := hmemq1 ▸ hmem ▸ hcl
    -- Branch on sign of d at 0x46a8 (`bltz a1`)
    rcases bltz_cases' d with hdlt | hdge
    · -- d < 0 (MX-B, mixed): 46a8 taken → 4714 neg a1 → 4718 mv t0,ra → 471c jal → mixed_tail
      have hdtop : 2^63 ≤ d.toNat := bltz_true' d hdlt
      have hdneg : d.toInt < 0 := by rw [toInt_of_top d hdtop]; have := d.isLt; omega
      have hBmag : ((0#64) - d).toNat = d.toInt.natAbs := mag_neg_top d hdtop
      have hBpos : 0 < ((0#64) - d).toNat := by
        rw [hBmag]; have : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h); omega
      have hdiff : ¬(0 ≤ n.toInt ↔ 0 ≤ d.toInt) := fun hi => absurd (hi.mp hnInt) (by omega)
      obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
        site3_800046a8_taken σ1 i1 (c.steps + 1) (0x800046a8#64) vmi1 d hG1 hpc1 hmi1v hx11_1 hdl1 rfl hdlt hi1
      have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
      have hpc2 : σ2.regs.get? Register.PC = some (0x80004714#64) := by
        rw [obs_btaken_pc hobs2, show (0x800046a8#64 : BitVec 64) + sign_extend (m := 64) (0x006c#13)
          = (0x80004714#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide]
      have hx10_2 : σ2.regs.get? Register.x10 = some n :=
        obs_btaken_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_1
      have hx11_2 : σ2.regs.get? Register.x11 = some d :=
        obs_btaken_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_1
      have hx1_2 : σ2.regs.get? Register.x1 = some r :=
        obs_btaken_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_1
      have hx12_2 : σ2.regs.get? Register.x12 = some v12 :=
        obs_btaken_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
      have hx13_2 : σ2.regs.get? Register.x13 = some v13 :=
        obs_btaken_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
      obtain ⟨vmi2, hmi2v⟩ := obs_btaken_minstret hobs2
      have hmemq2 : σ2.mem = m0 := by rw [hmem2]; exact hmemq1
      have hul2 : Vsa.Sim.Code.__umoddi3Loaded σ2.mem := hmemq2 ▸ hmem ▸ hul
      have hcl2 : __hidden___udivdi3Loaded σ2.mem := hmemq2 ▸ hmem ▸ hcl
      -- Step 4714: neg a1,a1 ⇒ x11 := 0 - d
      obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
        site3_80004714 σ2 i2 (c.steps + 1 + 1) (0x80004714#64) vmi2 d hG2 hpc2 hmi2v hx11_2 hul2 rfl hi2
      have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3
      have hpc3 : σ3.regs.get? Register.PC = some (0x80004718#64) := by
        have := obs_alu_pc hobs3
        rwa [show BitVec.addInt (0x80004714#64 : BitVec 64) 4 = (0x80004718#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx11_3 : σ3.regs.get? Register.x11 = some ((0#64) - d) :=
        obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
      have hx10_3 : σ3.regs.get? Register.x10 = some n :=
        obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_2
      have hx1_3 : σ3.regs.get? Register.x1 = some r :=
        obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_2
      have hx12_3 : σ3.regs.get? Register.x12 = some v12 :=
        obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_2
      have hx13_3 : σ3.regs.get? Register.x13 = some v13 :=
        obs_alu_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_2
      obtain ⟨vmi3, hmi3v⟩ := obs_alu_minstret hobs3
      have hmemq3 : σ3.mem = m0 := by rw [hmem3]; exact hmemq2
      have hul3 : Vsa.Sim.Code.__umoddi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hul
      have hcl3 : __hidden___udivdi3Loaded σ3.mem := hmemq3 ▸ hmem ▸ hcl
      -- Step 4718: mv t0,ra ⇒ x5 := r
      obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
        site3_80004718 σ3 i3 (c.steps + 1 + 1 + 1) (0x80004718#64) vmi3 r hG3 hpc3 hmi3v hx1_3 hul3 rfl hi3
      have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4
      have hpc4 : σ4.regs.get? Register.PC = some (0x8000471c#64) := by
        have := obs_alu_pc hobs4
        rwa [show BitVec.addInt (0x80004718#64 : BitVec 64) 4 = (0x8000471c#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx5_4 : σ4.regs.get? Register.x5 = some r := by
        have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
        rwa [addi0 r] at this
      have hx10_4 : σ4.regs.get? Register.x10 = some n :=
        obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_3
      have hx11_4 : σ4.regs.get? Register.x11 = some ((0#64) - d) :=
        obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_3
      have hx12_4 : σ4.regs.get? Register.x12 = some v12 :=
        obs_alu_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
      have hx13_4 : σ4.regs.get? Register.x13 = some v13 :=
        obs_alu_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_3
      obtain ⟨vmi4, hmi4v⟩ := obs_alu_minstret hobs4
      have hmemq4 : σ4.mem = m0 := by rw [hmem4]; exact hmemq3
      have hul4 : Vsa.Sim.Code.__umoddi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hul
      have hcl4 : __hidden___udivdi3Loaded σ4.mem := hmemq4 ▸ hmem ▸ hcl
      -- Step 471c: jal ⇒ x1 := 0x4720, PC := 0x46ac
      obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
        site3_8000471c σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x8000471c#64) vmi4 hG4 hpc4 hmi4v hul4 rfl hi4
      have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5
      have hpc5 : σ5.regs.get? Register.PC = some (0x800046ac#64) := by
        have := obs_jal_pc hobs5
        rwa [show (0x8000471c#64 : BitVec 64) + sign_extend (m := 64) (0x1fff90#21)
            = (0x800046ac#64 : BitVec 64) from by apply BitVec.eq_of_toNat_eq; decide] at this
      have hx1_5 : σ5.regs.get? Register.x1 = some (0x80004720#64) := by
        have := obs_jal_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
        rwa [show BitVec.addInt (0x8000471c#64 : BitVec 64) 4 = (0x80004720#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_5 : σ5.regs.get? Register.x10 = some n :=
        obs_jal_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_4
      have hx11_5 : σ5.regs.get? Register.x11 = some ((0#64) - d) :=
        obs_jal_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_4
      have hx5_5 : σ5.regs.get? Register.x5 = some r :=
        obs_jal_other hobs5 Register.x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx5_4
      have hx12_5 : σ5.regs.get? Register.x12 = some v12 :=
        obs_jal_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
      have hx13_5 : σ5.regs.get? Register.x13 = some v13 :=
        obs_jal_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_4
      have hmi5 : ∃ v, σ5.regs.get? Register.minstret = some v := obs_jal_minstret hobs5
      have hmemq5 : σ5.mem = m0 := by rw [hmem5]; exact hmemq4
      have hul5 : Vsa.Sim.Code.__umoddi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hul
      have hcl5 : __hidden___udivdi3Loaded σ5.mem := hmemq5 ▸ hmem ▸ hcl
      -- sailOutput o and entry-frame g threaded to σ5 (bnottaken ; btaken ; neg ; mv ; jal)
      have hout5 : σ5.sailOutput = o := by
        rw [hobs5.out, sailOutput_sigmaPost_jal, hobs4.out, sailOutput_sigmaPost_alu,
          hobs3.out, sailOutput_sigmaPost_alu, hobs2.out, sailOutput_sigmaPost_branch_taken,
          hobs1.out, sailOutput_sigmaPost_branch_nottaken]; exact hout
      have hframe5 : ∀ R : Register, NotWrittenD R → σ5.regs.get? R = g R := by
        intro R hR
        rw [frame_jal hobs5 R hR.2.1 hR.nw, frame_alu hobs4 R hR.2.2 hR.nw,
          frame_alu hobs3 R hR.nw.x11 hR.nw, frame_btaken hobs2 R hR.nw,
          frame_bnottaken hobs1 R hR.nw]
        exact hframeE R hR
      obtain ⟨cf, hsf, hpostf⟩ :=
        divdi3_mixed_tail g n d n ((0#64) - d) r m0 o ⟨σ5, i5, _⟩
          hG5 hul5 hcl5 hmemq5 hout5 hpc5 hx10_5 hx11_5 hx1_5 hx5_5 ⟨v12, hx12_5⟩ ⟨v13, hx13_5⟩ hmi5 hi5 hBpos halign
          hAmag hBmag hd0 hdiff hframe5
      refine ⟨cf, ?_, hpostf⟩
      exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
        ((Steps.single hstep4).trans ((Steps.single hstep5).trans hsf))))
    · -- d ≥ 0 (SS-A, both nonneg): 46a8 nottaken → core at 46ac, x1 = r → same_tail
      have hdtop : d.toNat < 2^63 := bltz_false' d hdge
      have hdInt : 0 ≤ d.toInt := by rw [toInt_of_notop d hdtop]; exact Int.natCast_nonneg _
      have hBmag : d.toNat = d.toInt.natAbs := mag_notop d hdtop
      have hBpos : 0 < d.toNat := by rw [hBmag]; have : d.toInt.natAbs ≠ 0 := fun h => hd0 (Int.natAbs_eq_zero.mp h); omega
      have hsame : (0 ≤ n.toInt ↔ 0 ≤ d.toInt) := ⟨fun _ => hdInt, fun _ => hnInt⟩
      have hnov : (n / d).toNat < 2^63 :=
        udiv_lt_of_not_overflow n d n d hAmag hBmag hsame hd0 hexcl
      obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
        site3_800046a8_nottaken σ1 i1 (c.steps + 1) (0x800046a8#64) vmi1 d hG1 hpc1 hmi1v hx11_1 hdl1 rfl hdge hi1
      have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2
      have hpc2 : σ2.regs.get? Register.PC = some (0x800046ac#64) := by
        have := obs_bnottaken_pc hobs2
        rwa [show BitVec.addInt (0x800046a8#64 : BitVec 64) 4 = (0x800046ac#64 : BitVec 64) from by
          apply BitVec.eq_of_toNat_eq; decide] at this
      have hx10_2 : σ2.regs.get? Register.x10 = some n :=
        obs_bnottaken_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_1
      have hx11_2 : σ2.regs.get? Register.x11 = some d :=
        obs_bnottaken_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_1
      have hx1_2 : σ2.regs.get? Register.x1 = some r :=
        obs_bnottaken_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx1_1
      have hx12_2 : σ2.regs.get? Register.x12 = some v12 :=
        obs_bnottaken_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_1
      have hx13_2 : σ2.regs.get? Register.x13 = some v13 :=
        obs_bnottaken_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx13_1
      obtain ⟨vmi2, hmi2v⟩ := obs_bnottaken_minstret hobs2
      have hmemq2 : σ2.mem = m0 := by rw [hmem2]; exact hmemq1
      have hcl2 : __hidden___udivdi3Loaded σ2.mem := hmemq2 ▸ hmem ▸ hcl
      -- sailOutput o and entry-frame g threaded to σ2 = cent (bnottaken ; bnottaken)
      have hout2 : σ2.sailOutput = o := by
        rw [hobs2.out, sailOutput_sigmaPost_branch_nottaken,
          hobs1.out, sailOutput_sigmaPost_branch_nottaken]; exact hout
      have hframe2 : ∀ R : Register, NotWrittenD R → σ2.regs.get? R = g R := by
        intro R hR
        rw [frame_bnottaken hobs2 R hR.nw, frame_bnottaken hobs1 R hR.nw]
        exact hframeE R hR
      obtain ⟨cf, hsf, hpostf⟩ :=
        divdi3_same_tail g n d n d r m0 o ⟨σ2, i2, _⟩
          hG2 hcl2 hmemq2 hout2 hpc2 hx10_2 hx11_2 hx1_2 ⟨v12, hx12_2⟩ ⟨v13, hx13_2⟩ ⟨vmi2, hmi2v⟩ hi2 hBpos halign
          hAmag hBmag hd0 hsame hnov hframe2
      refine ⟨cf, ?_, hpostf⟩
      exact (Steps.single hstep1).trans ((Steps.single hstep2).trans hsf)

end Vsa.Sim
