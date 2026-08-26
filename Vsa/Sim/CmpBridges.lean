import Vsa.Sim.ValueSpec

/-!
# Value bridges for the shared inline comparison arm (`lt`/`le`/`gt`)

The comparison arm @0x80003628 computes, on two int operands `vl = .int a`
(payload word `Wl`, so `Wl.toInt = a`) and `vr = .int b` (payload word `Wr`,
`Wr.toInt = b`):

    cmp = subw (zext (slt Wr Wl)) (zext (slt Wl Wr))          -- = sign(a - b)

then an op-specific fixup, then `value_bool(sret, x11)` — which produces
`ValueRepr … (.bool (x11 != 0))`. These three bridges show that the fixup
output `x11` satisfies `(x11 != 0) = <spec comparison>`:

* **`lt`** (fixup `srli a1,a1,0x3f` = sign-bit extract): `(x11 != 0) = (a < b)`.
* **`le`** (fixup `slti a1,a1,1`):                        `(x11 != 0) = (a ≤ b)`.
* **`gt`** (fixup `sgtz a1,a1` = `slt x0,a1`):            `(x11 != 0) = (b < a)`.

`zopz0zI_s x y = (x.toInt < y.toInt)` (Sail signed-less-than on the 64-bit
payloads, which are in `[-2^63, 2^63)` — so `BitVec.slt` on the payloads
matches `Int` `<` directly, no range side-condition needed).

Proof shape: `zopz0zI_s` unfolds to the `Int` comparison definitionally; the
two comparisons `(a<b)`, `(b<a)` are mutually exclusive, so a trichotomy split
(`by_cases`) reduces each fixup to a concrete `BitVec` computation dischargeable
by `decide` after `unfold bool_to_bit bool_bit_forwards zopz0zI_s`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa

set_option maxHeartbeats 4000000

namespace Vsa.Sim

/-- The machine 64-bit comparison scalar `cmp = subw(zext(slt Wr Wl), zext(slt Wl Wr))`,
which equals `sign(Wl.toInt - Wr.toInt)` in `{-1, 0, 1}`. -/
def cmpScalar (Wl Wr : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64)
    ((Sail.BitVec.extractLsb (zero_extend (m := 64) (bool_to_bit (zopz0zI_s Wr Wl))) 31 0)
      - (Sail.BitVec.extractLsb (zero_extend (m := 64) (bool_to_bit (zopz0zI_s Wl Wr))) 31 0))

/-- **`lt` fixup bridge**: the `lt`-arm output `srli cmp 0x3f` (sign-bit extract)
is nonzero iff `Wl.toInt < Wr.toInt`, i.e. `a < b`. -/
theorem lt_fixup_bridge (Wl Wr : BitVec 64) :
    (shift_bits_right (cmpScalar Wl Wr) (Sail.BitVec.extractLsb (0x3f#6) 5 0) != 0#64)
      = decide (Wl.toInt < Wr.toInt) := by
  unfold cmpScalar
  have hbr : zopz0zI_s Wl Wr = decide (Wl.toInt < Wr.toInt) := by unfold zopz0zI_s; rfl
  have hbl : zopz0zI_s Wr Wl = decide (Wr.toInt < Wl.toInt) := by unfold zopz0zI_s; rfl
  rw [hbr, hbl]
  by_cases hlt : Wl.toInt < Wr.toInt
  · rw [decide_eq_true hlt, decide_eq_false (show ¬ Wr.toInt < Wl.toInt by omega)]
    unfold bool_to_bit bool_bit_forwards; decide
  · rw [decide_eq_false hlt]
    by_cases hgt : Wr.toInt < Wl.toInt
    · rw [decide_eq_true hgt]; unfold bool_to_bit bool_bit_forwards; decide
    · rw [decide_eq_false hgt]; unfold bool_to_bit bool_bit_forwards; decide

/-- **`gt` fixup bridge**: the `gt`-arm output `sgtz cmp` (`= slt x0,cmp`) is
nonzero iff `Wr.toInt < Wl.toInt`, i.e. `b < a` (`= a > b`). -/
theorem gt_fixup_bridge (Wl Wr : BitVec 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) (cmpScalar Wl Wr))) != 0#64)
      = decide (Wr.toInt < Wl.toInt) := by
  unfold cmpScalar
  have hbr : zopz0zI_s Wl Wr = decide (Wl.toInt < Wr.toInt) := by unfold zopz0zI_s; rfl
  have hbl : zopz0zI_s Wr Wl = decide (Wr.toInt < Wl.toInt) := by unfold zopz0zI_s; rfl
  rw [hbr, hbl]
  by_cases hgt : Wr.toInt < Wl.toInt
  · rw [decide_eq_true hgt, decide_eq_false (show ¬ Wl.toInt < Wr.toInt by omega)]
    unfold bool_to_bit bool_bit_forwards zopz0zI_s; decide
  · rw [decide_eq_false hgt]
    by_cases hlt : Wl.toInt < Wr.toInt
    · rw [decide_eq_true hlt]; unfold bool_to_bit bool_bit_forwards zopz0zI_s; decide
    · rw [decide_eq_false hlt]; unfold bool_to_bit bool_bit_forwards zopz0zI_s; decide

/-- **`le` fixup bridge**: the `le`-arm output `slti cmp,1` is nonzero iff
`Wl.toInt ≤ Wr.toInt`, i.e. `a ≤ b`. -/
theorem le_fixup_bridge (Wl Wr : BitVec 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (cmpScalar Wl Wr)
      (sign_extend (m := 64) (0x001#12)))) != 0#64)
      = decide (Wl.toInt ≤ Wr.toInt) := by
  unfold cmpScalar
  have hbr : zopz0zI_s Wl Wr = decide (Wl.toInt < Wr.toInt) := by unfold zopz0zI_s; rfl
  have hbl : zopz0zI_s Wr Wl = decide (Wr.toInt < Wl.toInt) := by unfold zopz0zI_s; rfl
  rw [hbr, hbl]
  by_cases hgt : Wr.toInt < Wl.toInt
  · rw [decide_eq_true hgt, decide_eq_false (show ¬ Wl.toInt < Wr.toInt by omega),
        decide_eq_false (show ¬ Wl.toInt ≤ Wr.toInt by omega)]
    unfold bool_to_bit bool_bit_forwards zopz0zI_s; decide
  · rw [decide_eq_false hgt, decide_eq_true (show Wl.toInt ≤ Wr.toInt by omega)]
    by_cases hlt : Wl.toInt < Wr.toInt
    · rw [decide_eq_true hlt]; unfold bool_to_bit bool_bit_forwards zopz0zI_s; decide
    · rw [decide_eq_false hlt]; unfold bool_to_bit bool_bit_forwards zopz0zI_s; decide

end Vsa.Sim
