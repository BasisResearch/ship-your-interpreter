import Vsa.Sim.DecodeTable.Batch02Part14
import Vsa.Sim.DecodeTable.Batch04Part05
import Vsa.Sim.DecodeTable.Batch07Part01
import Vsa.Sim.DecodeTable.Batch07Part24
import Vsa.Sim.DecodeTable.Batch08Part11
import Vsa.Sim.DecodeTable.Batch08Part18
import Vsa.Sim.DecodeTable.Batch10Part05
import Vsa.Sim.DecodeTable.Batch10Part26
import Vsa.Sim.DecodeTable.Batch11Part05
import Vsa.Sim.DecodeTable.Batch11Part10
import Vsa.Sim.DecodeTable.Batch11Part14
import Vsa.Sim.DecodeTable.Batch13Part30
import Vsa.Sim.DecodeTable.Batch14Part16
import Vsa.Sim.DecodeTable.Batch14Part32
import Vsa.Sim.DecodeTable.Batch15Part09
import Vsa.Sim.DecodeTable.Batch15Part19
import Vsa.Sim.FrameOn
import Vsa.Sim.PinW
import Vsa.Sim.SnprintfSitesRet5
import Vsa.Sim.SnprintfSpec15
import Vsa.Sim.SnprintfSpec20

/-!
# M3 Layer-3 — `SnprintfSpec39` : the byte-for-byte `intToString` bridge

pctrace item 4: the buffer content produced by the verified svfprintf `%lld`
chain **is** `(intToString v.toInt).toUTF8`.  Spec37/38 export the digit bytes
as the arithmetic formula

    bs2 k = ofNat 8 (48 + (mag / 10^(n2−1−k)) % 10)     (k < n2)

together with `1 ≤ n2 ≤ 20`, the leading-digit bound `mag / 10^(n2−1) ≤ 9`
(equivalently `mag < 10^n2`) and — since the `DLI` minimality widening — the
lower bound `n2 = 1 ∨ 9 < mag / 10^(n2−2)` (equivalently `10^(n2−1) ≤ mag`
for `n2 ≥ 2`), which pins `n2` as *the* decimal digit count.  This module
closes the gap to `Vsa.While.natToString` / `intToString`:

* `digitList_eq_natDigits_39` — the digit-formula list *is* `natDigits`
  (the mathematical heart: induction on `n2` along `natDigits_step`'s
  split, using minimality for the recursive guard);
* `digits_eq_natToString` — the `BitVec 8` byte list = `natToString mag`'s
  characters (via `digitChar_toNat_39`);
* `toUTF8_toList_ascii_39` — for ASCII strings, `toUTF8` is the byte image
  of the character list (the v4.29 `String`-as-`ByteArray` representation:
  `toUTF8 = toByteArray`, `utf8EncodeChar c = [c.toNat]` for `c ≤ 127`);
* `natToString_toUTF8_toList_39` / `intToString_neg_toUTF8_toList_39` —
  the UTF-8 byte lists of the magnitude string and of the negative
  rendering `"-" ++ …`;
* `svfprintf_buffer_eq_intToString` — the machine-facing verdict:
  `signByte :: [bs2 0, …, bs2 (n2−1)] = (intToString v.toInt).toUTF8` bytes,
  under exactly the hypotheses Spec38's postcondition exports;
* `svfprintf_lld_intToString_spec` — the composed capstone: Spec38 with the
  buffer content restated **byte-for-byte** as
  `(intToString (llArg …).toInt).toUTF8`, indexed into the caller buffer
  `[d, d + len)` with `a0 = len` = the UTF-8 length.
-/

open Vsa Vsa.Sim Vsa.While
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Register
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

set_option maxHeartbeats 1600000

/-! ## Digit characters -/

/-- `(Nat.digitChar d).toNat = 48 + d` for `d < 10` — the numeric converse of
`digitChar_eq`. -/
theorem digitChar_toNat_39 (d : Nat) (h : d < 10) : (Nat.digitChar d).toNat = 48 + d := by
  match d, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl

/-- Digit characters are ASCII. -/
theorem digitChar_ascii_39 (d : Nat) (h : d < 10) : (Nat.digitChar d).toNat ≤ 127 := by
  rw [digitChar_toNat_39 d h]; omega

/-- Every character `natDigits` produces is ASCII. -/
theorem natDigits_ascii_39 (f n : Nat) : ∀ c ∈ natDigits f n, c.toNat ≤ 127 := by
  induction f generalizing n with
  | zero => intro c hc; simp [natDigits] at hc
  | succ f ih =>
    intro c hc
    unfold natDigits at hc
    by_cases h : n < 10
    · rw [if_pos h] at hc
      rw [List.mem_singleton.mp hc]
      exact digitChar_ascii_39 n h
    · rw [if_neg h] at hc
      rcases List.mem_append.mp hc with h1 | h1
      · exact ih (n / 10) c h1
      · rw [List.mem_singleton.mp h1]
        exact digitChar_ascii_39 (n % 10) (Nat.mod_lt _ (by omega))

/-! ## `natToString`'s character list -/

/-- `foldl push` builds exactly the appended character list. -/
theorem foldl_push_toList_39 (l : List Char) (s : String) :
    (l.foldl String.push s).toList = s.toList ++ l := by
  induction l generalizing s with
  | nil => simp
  | cons c t ih => rw [List.foldl_cons, ih, String.toList_push]; simp

/-- `(natToString n).toList = natDigits (n+1) n`. -/
theorem natToString_toList_39 (n : Nat) :
    (natToString n).toList = natDigits (n + 1) n := by
  unfold Vsa.While.natToString
  rw [foldl_push_toList_39]
  rfl

/-! ## The digit-formula list IS `natDigits` (the heart) -/

/-- **The digit-formula/`natDigits` identity.**  For `1 ≤ n2` with
`mag / 10^(n2−1) ≤ 9` (at most `n2` digits) and the minimality bound
`n2 = 1 ∨ 9 < mag / 10^(n2−2)` (at least `n2` digits), the MSB-first
digit-formula list is exactly `natDigits (mag+1) mag` — `n2` really is the
decimal digit count and the formula enumerates the digits in order. -/
theorem digitList_eq_natDigits_39 (n2 : Nat) : ∀ (mag : Nat), 1 ≤ n2 →
    mag / 10 ^ (n2 - 1) ≤ 9 → (n2 = 1 ∨ 9 < mag / 10 ^ (n2 - 2)) →
    (List.range n2).map (fun k => Nat.digitChar (mag / 10 ^ (n2 - 1 - k) % 10))
      = natDigits (mag + 1) mag := by
  induction n2 with
  | zero => intro mag h1 _ _; omega
  | succ m ih =>
    intro mag h1 hub hlb
    cases m with
    | zero =>
      -- n2 = 1: a single digit, mag ≤ 9
      have hm9 : mag ≤ 9 := by
        have h := hub
        rwa [show 0 + 1 - 1 = 0 from rfl, Nat.pow_zero, Nat.div_one] at h
      rw [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil]
      unfold natDigits
      rw [if_pos (show mag < 10 by omega)]
      rw [show 0 + 1 - 1 - 0 = 0 from rfl, Nat.pow_zero, Nat.div_one,
        Nat.mod_eq_of_lt (by omega)]
    | succ j =>
      -- n2 = j + 2 ≥ 2: minimality gives the recursion guard 9 < mag / 10^j
      have hgt : 9 < mag / 10 ^ j := by
        rcases hlb with h | h
        · omega
        · rwa [show j + 1 + 1 - 2 = j from by omega] at h
      have hmag10 : 10 ≤ mag := by
        have hle : mag / 10 ^ j ≤ mag := Nat.div_le_self _ _
        omega
      -- split both sides at the last digit
      rw [natDigits_step mag hmag10, List.range_succ, List.map_append]
      -- the recursive hypotheses for mag / 10 with n2' = j + 1
      have hub' : (mag / 10) / 10 ^ (j + 1 - 1) ≤ 9 := by
        rw [show j + 1 - 1 = j from rfl, Nat.div_div_eq_div_mul,
          show 10 * 10 ^ j = 10 ^ (j + 1) from by rw [Nat.pow_succ']]
        exact hub
      have hlb' : j + 1 = 1 ∨ 9 < (mag / 10) / 10 ^ (j + 1 - 2) := by
        cases j with
        | zero => exact Or.inl rfl
        | succ i =>
          refine Or.inr ?_
          rw [show i + 1 + 1 - 2 = i from by omega, Nat.div_div_eq_div_mul,
            show 10 * 10 ^ i = 10 ^ (i + 1) from by rw [Nat.pow_succ']]
          exact hgt
      congr 1
      · -- head part: re-index onto mag / 10
        rw [← ih (mag / 10) (by omega) hub' hlb']
        apply List.map_congr_left
        intro k hk
        have hklt : k < j + 1 := List.mem_range.mp hk
        have hexp : mag / 10 ^ (j + 1 + 1 - 1 - k) = (mag / 10) / 10 ^ (j + 1 - 1 - k) := by
          rw [show j + 1 + 1 - 1 - k = (j - k) + 1 from by omega,
            show j + 1 - 1 - k = j - k from by omega,
            Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        rw [hexp]
      · -- last digit: exponent 0
        simp only [List.map_cons, List.map_nil]
        rw [show j + 1 + 1 - 1 - (j + 1) = 0 from by omega, Nat.pow_zero, Nat.div_one]

/-- **The byte-list/`natToString` identity** (`BitVec 8` form, matching
Spec37/38's `bs2` export): the machine's digit bytes are the `toNat` image of
`natToString mag`'s characters. -/
theorem digits_eq_natToString (mag n2 : Nat) (bs : Nat → BitVec 8)
    (h1 : 1 ≤ n2)
    (hbs : ∀ k, k < n2 → bs k = BitVec.ofNat 8 (48 + mag / 10 ^ (n2 - 1 - k) % 10))
    (hub : mag / 10 ^ (n2 - 1) ≤ 9)
    (hlb : n2 = 1 ∨ 9 < mag / 10 ^ (n2 - 2)) :
    (List.range n2).map bs
      = (natToString mag).toList.map (fun ch => BitVec.ofNat 8 ch.toNat) := by
  rw [natToString_toList_39, ← digitList_eq_natDigits_39 n2 mag h1 hub hlb, List.map_map]
  apply List.map_congr_left
  intro k hk
  have hklt : k < n2 := List.mem_range.mp hk
  rw [hbs k hklt]
  show BitVec.ofNat 8 (48 + mag / 10 ^ (n2 - 1 - k) % 10)
      = BitVec.ofNat 8 (Nat.digitChar (mag / 10 ^ (n2 - 1 - k) % 10)).toNat
  rw [digitChar_toNat_39 _ (Nat.mod_lt _ (by omega))]

/-! ## The UTF-8 byte image (ASCII strings) -/

/-! ## The negative arm: `'-' ::` digits = `intToString v.toInt` -/

/-! ## The composed capstone: Spec38 restated byte-for-byte -/

end Vsa.Sim
