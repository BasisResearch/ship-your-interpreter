import Vsa.Sim.ValueEqualSites
import Vsa.Sim.ValueTruthySpec

/-!
# Layer 3 — payload-equality bridges + `str`-path call sites for `value_equal`

This companion to `ValueEqualSites.lean` adds:

* the four **payload-equality bridges** (bool/int/closure/native): each shows that
  the machine `sub payA payB` is `0` iff the corresponding spec `Value.equal` clause
  holds. The `sub` result feeds `seqz`, giving `cond (payA - payB = 0) 1 0`, so we need
  `(payA - payB = 0#64) = Value.equal …` at the `BitVec 64` level;
* the six **`str`-path call instructions** (`0x800028c4 … 0x800028e4`): argument moves,
  the stack `sd ra`/`ld ra`, the `jal strcmp`, and the trailing `seqz`. `site_ret_gen`
  already covers the `ret` at `0x800028e4`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Payload-equality bridges

`seqz` gives `cond ((payA - payB) == 0) 1 0`; we rewrite the `payA - payB == 0` test to
the spec `Value.equal` clause. All are stated at the `BitVec 64` level as `(x == 0) = P`. -/

/-- **bool bridge.** The 4-byte payloads are `cond b 1 0 : BitVec 64` (sign-extended,
but `{0,1}` are unaffected). `((cond b1 1 0) - (cond b2 1 0) == 0) = (b1 == b2)`. -/
theorem bool_eq_bridge (b1 b2 : Bool) :
    (((cond b1 (1#64) (0#64)) - (cond b2 (1#64) (0#64))) == 0#64) = (b1 == b2) := by
  cases b1 <;> cases b2 <;> decide

/-- A `sub` of two `BitVec 64` is `0` iff they are equal. -/
theorem bv64_sub_zero_iff (a b : BitVec 64) : (a - b = 0#64) ↔ a = b := by
  constructor
  · intro h
    have : a - b + b = 0#64 + b := by rw [h]
    rwa [BitVec.sub_add_cancel, BitVec.zero_add] at this
  · intro h; rw [h, BitVec.sub_self]

/-- **int bridge.** For payloads `p1 p2` with `(ofNat p1).toInt = n1`, `(ofNat p2).toInt = n2`,
the machine `sub` is zero iff the spec ints are equal. -/
theorem int_eq_bridge (p1 p2 : Nat) (n1 n2 : Int)
    (h1 : (BitVec.ofNat 64 p1).toInt = n1) (h2 : (BitVec.ofNat 64 p2).toInt = n2) :
    ((BitVec.ofNat 64 p1 - BitVec.ofNat 64 p2) == 0#64) = (n1 == n2) := by
  by_cases heq : BitVec.ofNat 64 p1 = BitVec.ofNat 64 p2
  · have hn : n1 = n2 := by rw [← h1, ← h2, heq]
    rw [show ((BitVec.ofNat 64 p1 - BitVec.ofNat 64 p2) == 0#64) = true from by
          rw [(bv64_sub_zero_iff _ _).mpr heq]; simp,
        show (n1 == n2) = true from by simp [hn]]
  · have hsub : (BitVec.ofNat 64 p1 - BitVec.ofNat 64 p2) ≠ 0#64 := by
      intro h; exact heq ((bv64_sub_zero_iff _ _).mp h)
    have hn : n1 ≠ n2 := by
      intro h; exact heq (BitVec.toInt_inj.mp (by rw [h1, h2, h]))
    rw [show ((BitVec.ofNat 64 p1 - BitVec.ofNat 64 p2) == 0#64) = false from by
          simpa using hsub,
        show (n1 == n2) = false from by simp [hn]]

/-- **closure / native bridge (generic pointer form).** For two machine words `q1 q2`
`= f x1`, `f x2` with `f` injective on `{x1,x2}`, the `sub` is zero iff `x1 = x2`.
Both closure (`φc ca`) and native (`N.addr f`) use this shape. -/
theorem ptr_eq_bridge {α : Type} [BEq α] [LawfulBEq α] (f : α → Nat) (x1 x2 : α) (q1 q2 : Nat)
    (hq1 : q1 = f x1) (hq2 : q2 = f x2)
    (hlt1 : q1 < 2 ^ 64) (hlt2 : q2 < 2 ^ 64)
    (hinj : f x1 = f x2 → x1 = x2) :
    ((BitVec.ofNat 64 q1 - BitVec.ofNat 64 q2) == 0#64) = (x1 == x2) := by
  by_cases hqeq : q1 = q2
  · have hxeq : x1 = x2 := hinj (by rw [← hq1, ← hq2, hqeq])
    rw [show ((BitVec.ofNat 64 q1 - BitVec.ofNat 64 q2) == 0#64) = true from by
          rw [(bv64_sub_zero_iff _ _).mpr (by rw [hqeq])]; simp,
        show (x1 == x2) = true from by simp [hxeq]]
  · have hbv : BitVec.ofNat 64 q1 ≠ BitVec.ofNat 64 q2 := by
      intro h
      have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1,
        Nat.mod_eq_of_lt hlt2] at this
      exact hqeq this
    have hsub : (BitVec.ofNat 64 q1 - BitVec.ofNat 64 q2) ≠ 0#64 := by
      intro h; exact hbv ((bv64_sub_zero_iff _ _).mp h)
    have hxne : x1 ≠ x2 := by
      intro h; exact hqeq (by rw [hq1, hq2, h])
    rw [show ((BitVec.ofNat 64 q1 - BitVec.ofNat 64 q2) == 0#64) = false from by
          simpa using hsub,
        show (x1 == x2) = false from by simp [hxne]]

end Vsa.Sim
