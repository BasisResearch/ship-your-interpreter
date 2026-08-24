import Vsa.Sim.MemLoadTotal

/-!
# The magic-constant zero-byte detection arithmetic (`strlen` word-wise core)

The word-wise `strlen` loop (`0x80006d10 … 0x80006d28`) scans 8 bytes at a time,
detecting whether the aligned word `w` contains a zero byte with the classic
`0x7f7f7f7f7f7f7f7f` trick (newlib's `strlen`, matching the disassembly):

```
a3 = 0x7f7f7f7f7f7f7f7f ; the magic mask
a1 = -1                 ; all ones
loop:
  a2 = ld [a4] ; w
  a5 = a2 & a3            ; w & 0x7f..
  a5 = a5 + a3            ; + 0x7f..
  a5 = a5 | a2            ; | w
  a5 = a5 | a3            ; | 0x7f..
  beq a5, a1, loop        ; a5 == all-ones  ⇔  NO zero byte in w
```

The key fact: the computed `a5 = strlenWordVal w` equals `0xFF…FF` (all ones,
`a1`) **iff** every byte of `w` is nonzero; equivalently `a5 ≠ all-ones` iff `w`
has a zero byte.

## What lands here (fully proved)

* `byte_all` / `byte_struct_ff` — the **single-byte kernel**: for `b < 256`,
  `((b &&& 0x7f) + 0x7f) ||| b ||| 0x7f = 0xFF ↔ b ≠ 0`. Proved by exhaustive
  `decide` over `Fin 256`. This is the arithmetic heart: the 64-bit result is
  eight byte-independent copies of it.
* `strlenWordVal_add_noCarry` — the **carry-free addition**: `(w &&& m) + m`
  never overflows and never carries across a byte boundary, because each masked
  byte is `≤ 0x7f` and `0x7f + 0x7f = 0xfe < 0x100`. Stated on `toNat` (no mod
  reduction). This is what makes the byte decomposition sound.

## Remaining crux (documented, not stated with `sorry`)

`detect_all_ones : strlenWordVal w = allOnes 64 ↔ ∀ k<8, byte k of w ≠ 0`. The
proof is a per-bit `BitVec.getLsbD` argument: bits `0..6` of every byte are
forced `true` by the final `||| magic7f` (whose bits `0..6` are set); bit `7` of
byte `k` reduces — via `BitVec.getLsbD_add` + `strlenWordVal_add_noCarry` (carry
into `8k+7` depends only on byte `k`) — to the single-byte `byte_all` fact. The
only missing pieces are the `BitVec.carry (8k+7) (w&&&m) m` per-byte-locality
lemma (proved from the `toNat` carry-free bound) and its assembly; the arithmetic
content is entirely captured by the two lemmas below.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The magic mask `0x7f7f7f7f7f7f7f7f`. -/
abbrev magic7f : BitVec 64 := 0x7f7f7f7f7f7f7f7f#64

/-- The `strlen` per-word structure value:
`a5 = ((w &&& 0x7f..) + 0x7f..) ||| w ||| 0x7f..`. -/
abbrev strlenWordVal (w : BitVec 64) : BitVec 64 :=
  (((w &&& magic7f) + magic7f) ||| w) ||| magic7f

/-- **Single-byte kernel (over `Fin 256`).** For a byte value `b`, the byte-level
structure `((b &&& 0x7f) + 0x7f) ||| b ||| 0x7f` equals `0xFF` iff `b ≠ 0`.
Exhaustive `decide` over the 256 byte values. The 64-bit `strlenWordVal` result
decomposes into eight independent copies of this (the low 7 bits are forced set
by `||| 0x7f`; bit 7 is the byte-nonzero discriminant). -/
theorem byte_all : ∀ b : Fin 256,
    (((b.val &&& 0x7f) + 0x7f) ||| b.val ||| 0x7f = 0xFF) ↔ b.val ≠ 0 := by
  decide

/-- `Nat` form of the single-byte kernel. -/
theorem byte_struct_ff (b : Nat) (hb : b < 256) :
    (((b &&& 0x7f) + 0x7f) ||| b ||| 0x7f = 0xFF) ↔ b ≠ 0 :=
  byte_all ⟨b, hb⟩

/-- **Magic mask bit pattern.** `magic7f.getLsbD i = (i % 8 ≠ 7)` for `i < 64`:
bits `0..6` of every byte are set, bit `7` clear. This is why the final `||| m`
of `strlenWordVal` forces bits `0..6` of each byte to `true`, leaving bit `7`
(`i % 8 = 7`) as the sole per-byte discriminant. `decide` over `Fin 64`. -/
theorem magic_bit : ∀ i : Fin 64, magic7f.getLsbD i.val = decide (i.val % 8 ≠ 7) := by
  decide

/-- **Result-bit reduction.** Bit `i` of `strlenWordVal w` is the `or` of the
addition's bit, `w`'s bit, and the magic bit. Pure `getLsbD_or` unfolding — the
starting point of the per-bit analysis: for `i % 8 ≠ 7` the magic bit is `true`
(`magic_bit`) so the whole bit is `true`; only bit `7` of each byte carries
information. -/
theorem strlenWordVal_bit (w : BitVec 64) (i : Nat) :
    (strlenWordVal w).getLsbD i =
      (((w &&& magic7f) + magic7f).getLsbD i || w.getLsbD i || magic7f.getLsbD i) := by
  simp only [strlenWordVal, BitVec.getLsbD_or]

/-- **Carry-free addition (no overflow).** `((w &&& magic7f) + magic7f).toNat`
equals the exact `Nat` sum with no mod-2^64 reduction, because
`(w &&& magic7f).toNat ≤ magic7f.toNat = 0x7f7f7f7f7f7f7f7f` and
`0x7f7f… + 0x7f7f… = 0xfefe… < 2^64`. This is the fact that makes the byte-wise
decomposition of `strlenWordVal` sound: the masked operand's high (bit-7) lanes
are all zero, so no addition carry crosses a byte boundary. -/
theorem strlenWordVal_add_noCarry (w : BitVec 64) :
    ((w &&& magic7f) + magic7f).toNat = (w &&& magic7f).toNat + magic7f.toNat := by
  rw [BitVec.toNat_add]
  have hm : magic7f.toNat = 0x7f7f7f7f7f7f7f7f := by decide
  have hle : (w &&& magic7f).toNat ≤ magic7f.toNat := by
    rw [BitVec.toNat_and, hm]; exact Nat.le_trans Nat.and_le_right (by decide)
  rw [Nat.mod_eq_of_lt]; rw [hm] at hle ⊢; omega

/-! ## Cross-byte detection (`detect_all_ones`)

The crux the file header documented as "remaining". `strlenWordVal w` equals
`allOnes 64` **iff every byte of `w` is nonzero**. The proof is a per-bit
`getLsbD` argument:

* bits `i` with `i % 8 ≠ 7` are forced `true` by the final `||| magic7f` (whose
  bits `0..6` of every byte are set — `magic_bit`);
* bit `8k+7` of each byte `k` reduces, via `BitVec.getLsbD_add` +
  `strlenWordVal_add_noCarry` (**carry-locality**: no carry crosses a byte
  boundary), to the single carry `BitVec.carry (8k+7) (w &&& magic7f) magic7f
  false`, which — by `magic_carry` — equals `w`'s byte-`k` low-7-bits being
  nonzero; `or`'d with `w`'s bit `8k+7` this is exactly "byte `k` ≠ 0".

`magic_carry` is the carry-locality kernel: unfolding `BitVec.carry` to the
`toNat` `≥`-shape and using `Nat.mod_mul` to split `mod 2^(8k+7)` into
lower-byte + partial-byte-`k` parts, the lower-byte sum is bounded below `2^(8k)`
(masked bytes are `≤ 0x7f`, magic bytes `= 0x7f`, sum `≤ 0xfe·… < 2^(8k)`), so
the carry out of bit `8k+6` is decided purely by byte `k` — `omega` over the 8
concrete byte positions. -/

/-- **Carry-locality kernel.** The carry into bit `8k+7` of `(w &&& magic7f) +
magic7f` depends only on byte `k` of `w`: it is set iff the low 7 bits of byte
`k` are nonzero. Proved by unfolding `BitVec.carry` to its `toNat` `≥`-form,
splitting `mod 2^(8k+7)` with `Nat.mod_mul`, and `omega` over the 8 concrete `k`
(`k < 8`); the lower-byte sum is `< 2^(8k)` because each masked byte is `≤ 0x7f`
and the magic bytes are `0x7f`. -/
theorem magic_carry (w : BitVec 64) (k : Nat) (hk : k < 8) :
    BitVec.carry (8*k+7) (w &&& magic7f) magic7f false
      = decide (w.toNat / 2^(8*k) % 128 ≠ 0) := by
  have hmv : magic7f.toNat = 0x7f7f7f7f7f7f7f7f := by decide
  have hand : (w &&& magic7f).toNat / 2^(8*k) % 128 = w.toNat / 2^(8*k) % 128 := by
    have hmd : magic7f.toNat / 2^(8*k) % 128 = 127 := by
      rw [hmv]; rcases k with _|_|_|_|_|_|_|_|k <;> first | rfl | omega
    rw [BitVec.toNat_and, Nat.and_div_two_pow, Nat.and_mod_two_pow (n := 7),
        show (128:Nat) = 2^7 from rfl] at *
    rw [hmd, show (127:Nat) = 2^7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod]
  have ha : (w &&& magic7f).toNat % 2^(8*k) ≤ magic7f.toNat % 2^(8*k) := by
    rw [BitVec.toNat_and, Nat.and_mod_two_pow]; exact Nat.and_le_right
  have hn : (2:Nat)^(8*k+7) = 2^(8*k) * 128 := by rw [Nat.pow_add]
  have key : ((w &&& magic7f).toNat % 2^(8*k+7) + magic7f.toNat % 2^(8*k+7) + (false:Bool).toNat ≥ 2^(8*k+7))
      ↔ (w.toNat / 2^(8*k) % 128 ≠ 0) := by
    rw [hn, Nat.mod_mul, Nat.mod_mul, Bool.toNat_false, hmv, ← hand]
    rw [hmv] at ha
    rcases k with _|_|_|_|_|_|_|_|k
    all_goals (first | omega | (simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at ha ⊢; omega))
  unfold BitVec.carry
  rw [show ∀ a b : Nat, (a ≥b b) = decide (a ≥ b) from fun _ _ => rfl]
  exact decide_eq_decide.mpr key

/-- **Per-byte result bit.** Bit `8k+7` of `strlenWordVal w` is `true` iff byte
`k` of `w` is nonzero. Assembles `strlenWordVal_bit` (result bit = `add`-bit `or`
`w`-bit `or` magic-bit), `BitVec.getLsbD_add` (add bit `8k+7` = the carry, since
`w &&& magic7f` and `magic7f` are both `0` at bit `8k+7`), and `magic_carry`;
the final `or` with `w`'s bit `8k+7` upgrades "low-7-bits nonzero" to "byte ≠ 0".
`w`'s byte `k` as a `Nat` is `w.toNat / 2^(8k) % 256`. -/
theorem strlenWordVal_bit_high (w : BitVec 64) (k : Nat) (hk : k < 8) :
    (strlenWordVal w).getLsbD (8*k+7) = decide (w.toNat / 2^(8*k) % 256 ≠ 0) := by
  rw [strlenWordVal_bit]
  have hlt : 8*k+7 < 64 := by omega
  rw [BitVec.getLsbD_add hlt, BitVec.getLsbD_and]
  have hmb : magic7f.getLsbD (8*k+7) = false := by
    rcases k with _|_|_|_|_|_|_|_|k <;> first | rfl | omega
  rw [hmb, magic_carry w k hk]
  simp only [Bool.and_false, Bool.false_xor, Bool.or_false]
  have hwb : w.getLsbD (8*k+7) = decide (w.toNat / 2^(8*k) / 128 % 2 = 1) := by
    rw [← BitVec.testBit_toNat, show 8*k+7 = 7 + 8*k from by omega, Nat.testBit_add,
        Nat.testBit_eq_decide_div_mod_eq, show (2:Nat)^7 = 128 from rfl]
  rw [hwb, ← Bool.decide_or, decide_eq_decide]
  generalize w.toNat / 2^(8*k) = y
  omega

/-- Byte-`k` of `w` (as a width-8 `extractLsb'`) is nonzero iff its `Nat` value
`w.toNat / 2^(8k) % 256` is nonzero. Bridges the `extractLsb'` byte form (used in
`detect_all_ones`' statement) to the `Nat`-quotient form of `strlenWordVal_bit_high`. -/
theorem extractLsb'_byte_ne_zero (w : BitVec 64) (k : Nat) :
    (w.extractLsb' (8*k) 8 ≠ 0) ↔ (w.toNat / 2^(8*k) % 256 ≠ 0) := by
  constructor <;> intro h <;> intro hc <;> apply h
  · apply BitVec.eq_of_toNat_eq
    show w.toNat >>> (8*k) % 256 = _
    rw [Nat.shiftRight_eq_div_pow, hc]; rfl
  · have : (w.extractLsb' (8*k) 8).toNat = 0 := by rw [hc]; rfl
    show w.toNat / 2^(8*k) % 256 = 0
    rw [← Nat.shiftRight_eq_div_pow]; exact this

/-- **Cross-byte zero-byte detection.** `strlenWordVal w = allOnes 64` **iff every
byte of `w` is nonzero**. The `strlen` word-loop uses `a5 ≠ allOnes` as "found a
zero byte". Forward: bit `8k+7` of `allOnes` is `true`, so `strlenWordVal_bit_high`
forces byte `k` nonzero. Backward: `BitVec.eq_of_getLsbD_eq` — bits `i % 8 ≠ 7`
are `true` by `magic_bit`; bits `8k+7` are `true` by `strlenWordVal_bit_high`
from the byte-nonzero hypothesis. -/
theorem detect_all_ones (w : BitVec 64) :
    strlenWordVal w = BitVec.allOnes 64 ↔ ∀ k, k < 8 → w.extractLsb' (8*k) 8 ≠ 0 := by
  constructor
  · intro h k hk
    have hbit : (strlenWordVal w).getLsbD (8*k+7) = true := by
      rw [h, BitVec.getLsbD_allOnes]; simp only [decide_eq_true_eq]; omega
    rw [strlenWordVal_bit_high w k hk, decide_eq_true_eq] at hbit
    exact (extractLsb'_byte_ne_zero w k).mpr hbit
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_allOnes]
    simp only [hi, decide_true]
    by_cases hmod : i % 8 = 7
    · have hk : i / 8 < 8 := by omega
      have hi7 : i = 8*(i/8) + 7 := by omega
      rw [hi7, strlenWordVal_bit_high w (i/8) hk, decide_eq_true_eq]
      exact (extractLsb'_byte_ne_zero w (i/8)).mp (h (i/8) hk)
    · rw [strlenWordVal_bit]
      have hmbi : magic7f.getLsbD i = true := by
        have := magic_bit ⟨i, hi⟩
        simp only at this
        rw [this]; simp only [decide_eq_true_eq]; exact hmod
      rw [hmbi]; simp

end Vsa.Sim
