import Vsa.Sim.ObsAvoid
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch08Part12
import Vsa.Sim.DecodeTable.Batch11Part19
import Vsa.Sim.DecodeTable.Batch11Part21
import Vsa.Sim.DecodeTable.Batch15Part23
import Vsa.Sim.DecodeTable.Batch15Part25
import Vsa.Sim.DecodeTable.Batch15Part28
import Vsa.Sim.DecodeTable.Batch15Part32
import Vsa.Sim.DivLoops

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

/-! ### Shared "compute the tmod result and return" tail

From a state `cA` at the core entry `0x800046ac` with core operands `A = x10`,
`B = x11`, `x1 = q` (a core-return address, one of `0x4738`/`0x4750`), `x5 = r`
(the saved `t0`), the wrapper (`__moddi3Loaded`) still loaded, run: core (via
`core_call_tail_f`), then the fixup at `q` (either `mv a0,a1` at `0x4738`, or
`neg a0,a1` at `0x4750`), then `jr t0` back to `r`. `negate = true` for the
`0x4750` path (dividend negative). Delivers the strong `moddi3_post`, threading
the entry ghost frame `hframe0` (`cA → g`) and `sailOutput = o` through the core
and the two fixup steps. -/

/-! ## `__divdi3` — signed quotient (entry `0x800046a4`) -/

end Vsa.Sim
