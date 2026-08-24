import Vsa.Sim.DivSpec3
import Vsa.While.Semantics

/-!
# M3 Layer-3 — `snprintf("%lld", v)` = `intToString v` : the arithmetic core

This file lands the **mathematical heart** of the `snprintf`-for-`%lld`
verification described in `experiments/M3-snprintf-lld.md` §3 / §5.3 / §6(b,c):
the digit-emission correspondence and the INT64_MIN-safe sign/magnitude bridge
between the binary's decimal core and `Vsa.While.intToString` / `natDigits`
(`Vsa/While/Semantics.lean`).

These are the pure-arithmetic lemmas that the machine-level Triples
(`decimalLoop_spec`, `svfprintf_lld_spec`, `snprintf_lld_spec`) will consume;
they are independent of the Sail stepping layer, so they are proved and
kernel-checked here in full (no `sorry`/`axiom`/`native_decide`/`bv_decide`).

## What is proved here

* `digitChar_eq` — `Nat.digitChar d = Char.ofNat (48 + d)` for `d < 10`: the
  `addiw a0,a0,48` emit (§1.4) equals `natDigits`' `Nat.digitChar`.
* `natDigits_fuel` — fuel irrelevance of `natDigits` (the `fuel` argument is a
  Lean termination device with no binary analogue; §3.2).
* `natDigits_step` — **the digit-split identity**
  `natDigits (n+1) n = natDigits (n/10+1) (n/10) ++ [digitChar (n%10)]` for
  `n ≥ 10`.  This is the load-bearing induction step of the digit-loop invariant
  (§5.3): the machine emits `n%10` low-digit-first into a descending buffer, then
  recurses on `n/10`.
* `loopDigits` + `loopDigits_eq_natDigits` — a functional model of the machine's
  do-while loop (emit `n%10`, `n := n/10`, while pre-value `> 9`) and its proof
  of agreement with `natDigits`.  The future machine Triple need only match
  `loopDigits`; this lemma bridges it to `natDigits` (hence `natToString`).
* `neg_magnitude` — for a negative `v : BitVec 64` (top bit set),
  `(-v).toNat = (-v.toInt).toNat`: the `neg a4,a4` (§1.4) read as **unsigned**
  is exactly the magnitude `|v.toInt|`, **including INT64_MIN** where
  `neg 0x8000…0 = 0x8000…0` read unsigned `= 2^63` (§6(c), no UB).
* `intToString_nonneg` / `intToString_neg` — the sign-branch correspondence:
  `intToString v.toInt` equals `natToString v.toNat` (top bit clear) resp.
  `"-" ++ natToString (-v).toNat` (top bit set).  Combined in
  `intToString_of_bv` below, this is the byte-for-byte verdict of §3.
-/

open Vsa Vsa.Sim Vsa.While

namespace Vsa.Sim

set_option maxHeartbeats 800000

/-! ## Digit-character correspondence (`'0' + d` = `Nat.digitChar d`) -/

/-- `Nat.digitChar d = Char.ofNat (48 + d)` for `d < 10`: the machine's
`addiw a0,a0,48` (`0x80008328`, §1.4) emits exactly `natDigits`' digit char. -/
theorem digitChar_eq (d : Nat) (h : d < 10) : Nat.digitChar d = Char.ofNat (48 + d) := by
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

/-! ## `natDigits` fuel irrelevance and the digit-split identity -/

/-- Fuel irrelevance: any two fuels `≥ n+1` compute the same `natDigits n`.  The
`fuel` argument is a Lean structural-recursion device with no binary analogue
(§3.2); the machine loop terminates by the `bgeu a5,s6` exit test. -/
theorem natDigits_fuel (f1 f2 n : Nat) (h1 : n + 1 ≤ f1) (h2 : n + 1 ≤ f2) :
    natDigits f1 n = natDigits f2 n := by
  induction f1 generalizing f2 n with
  | zero => omega
  | succ f1 ih =>
    cases f2 with
    | zero => omega
    | succ f2 =>
      unfold natDigits
      by_cases hlt : n < 10
      · simp [hlt]
      · simp only [hlt, if_false]
        rw [ih f2 (n/10) (by omega) (by omega)]

/-- **The digit-split identity** (the load-bearing induction step, §5.3):
for `n ≥ 10`, `natDigits (n+1) n = natDigits (n/10+1) (n/10) ++ [digitChar (n%10)]`.
Mirrors the machine loop emitting `n%10` (low digit) then recursing on `n/10`
into a descending buffer, giving the identical MSB-first byte order. -/
theorem natDigits_step (n : Nat) (h : 10 ≤ n) :
    natDigits (n + 1) n = natDigits (n / 10 + 1) (n / 10) ++ [Nat.digitChar (n % 10)] := by
  unfold natDigits
  have hlt : ¬ n < 10 := by omega
  simp only [hlt, if_false]
  congr 1
  exact natDigits_fuel n (n / 10 + 1) (n / 10) (by omega) (by omega)

/-! ## Functional model of the machine digit loop

`loopDigits fuel n` models the binary's do-while decimal loop (§1.4): the single
digit fast path (magnitude `≤ 9`) and the multi-digit loop (emit `n%10`, set
`n := n/10`, repeat while the pre-division value was `> 9`), producing the
MSB-first digit list.  The machine's descending-buffer write order (low digit
written first, into a top-down buffer) reads back as this same MSB-first list. -/

/-- Functional model of the machine's decimal digit loop, MSB-first. -/
def loopDigits : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n =>
    if n ≤ 9 then [Nat.digitChar n]
    else loopDigits fuel (n / 10) ++ [Nat.digitChar (n % 10)]

/-- The machine loop's output equals `natDigits` of the magnitude.  Together with
`natToString`'s definition this closes the digit-string half of the byte-for-byte
correspondence (§3.2). -/
theorem loopDigits_eq_natDigits (fuel n : Nat) (h : n + 1 ≤ fuel) :
    loopDigits fuel n = natDigits fuel n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    unfold loopDigits natDigits
    by_cases hle : n ≤ 9
    · simp [hle, show n < 10 by omega]
    · have hlt : ¬ n < 10 := by omega
      simp only [hle, hlt, if_false]
      rw [ih (n / 10) (by omega)]

/-- `loopDigits n n` (fuel = the value, which suffices for `n ≥ 1`) equals the
`natToString` digit list.  `natToString n = (natDigits (n+1) n).foldl .push ""`. -/
theorem loopDigits_natToString (n : Nat) :
    loopDigits (n + 1) n = natDigits (n + 1) n :=
  loopDigits_eq_natDigits (n + 1) n (Nat.le_refl _)

/-! ## INT64_MIN-safe sign/magnitude bridge

The machine reads the sign bit, stores `'-'` iff negative, then negates
(`neg a4,a4`) and formats the result **as unsigned** (§1.4, §6(c)).  For
INT64_MIN, `neg 0x8000…0 = 0x8000…0`, which read unsigned is `2^63`, the correct
magnitude — no signed overflow is exercised. -/

/-- The unsigned magnitude of the machine's `neg` of a negative value equals the
`Nat` magnitude `|v.toInt|`, **including INT64_MIN** (`2^63 ≤ v.toNat` is exactly
"top bit set" = "`v.toInt < 0`").  This encodes §6(c) as a `toNat`/`toInt`
identity. -/
theorem neg_magnitude (v : BitVec 64) (hneg : 2 ^ 63 ≤ v.toNat) :
    (- v).toNat = (- v.toInt).toNat := by
  have hv : v.toNat < 2 ^ 64 := v.isLt
  have hn : (- v) = (0#64) - v := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_neg, BitVec.toNat_sub]; simp
  rw [hn, neg_toNat_of_top v hneg, toInt_of_top v hneg]
  omega

/-! ## `intToString` sign-branch correspondence

`intToString` (`Vsa/While/Semantics.lean`) matches on the `Int` constructor;
these two lemmas re-express it in the sign-bit / magnitude vocabulary the
machine uses, so the top-level spec's `Q` (buffer = `intToString v.toInt`) is
discharged by the digit-loop result plus the sign store. -/

/-- Nonnegative branch (top bit clear): `intToString v.toInt = natToString v.toNat`. -/
theorem intToString_nonneg (v : BitVec 64) (h : v.toNat < 2 ^ 63) :
    intToString v.toInt = natToString v.toNat := by
  rw [toInt_of_notop v h]; rfl

/-- Negative branch (top bit set): `intToString v.toInt = "-" ++ natToString (-v).toNat`
where `(-v).toNat` is the unsigned magnitude produced by the machine's `neg`
(equal to `|v.toInt|` by `neg_magnitude`), **including INT64_MIN**. -/
theorem intToString_neg (v : BitVec 64) (h : 2 ^ 63 ≤ v.toNat) :
    intToString v.toInt = "-" ++ natToString (- v).toNat := by
  rw [neg_magnitude v h]
  have hlt : v.toInt < 0 := by rw [toInt_of_top v h]; have := v.isLt; omega
  rcases hi : v.toInt with m | m
  · exact absurd (hi ▸ hlt) (by simp)
  · rfl

/-- **The full byte-for-byte verdict (§3)** at the `String` level: `intToString`
of the signed interpretation of `v` equals the sign prefix (`"-"` iff negative)
concatenated with the decimal magnitude `natToString`, where the magnitude is the
machine's unsigned view of `v` (top bit clear) resp. of `neg v` (top bit set).
The two arms correspond exactly to the machine's `bgez` split (§1.4). -/
theorem intToString_of_bv (v : BitVec 64) :
    intToString v.toInt =
      (if 2 ^ 63 ≤ v.toNat then "-" ++ natToString (- v).toNat
       else natToString v.toNat) := by
  by_cases h : 2 ^ 63 ≤ v.toNat
  · rw [if_pos h, intToString_neg v h]
  · rw [if_neg h, intToString_nonneg v (by omega)]

end Vsa.Sim
