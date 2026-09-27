import Vsa.Sim.DivSpec

/-!
# Layer 3 — the two loops and the top-level `udivdi3_spec`

Composes the 24 config-level one-step transitions `utr_*` (`Vsa/Sim/DivSpec.lean`)
into the *normalize* and *divide* loops of libgcc's `__hidden___udivdi3`, then the
full total-correctness triple `udivdi3_spec` (`x10 = n / d`, `x11 = n % d`).

Follows the `Muldi3Spec` `Triple.loop` template: an `AtHead ∨ AtDone` invariant, a
measure that excludes the exit state, and `loop_body`/`loop_to_done` structure.

## Algorithm (from `DivSites`)

```
ac mv a2,a1   ; a2 = d
b0 mv a1,a0   ; a1 = n
b4 li a0,-1
b8 beqz a2 →f0
bc li a3,1
c0 bgeu a2,a1 →d4     ; normalize: exit if d ≥ n
c4 blez a2 →d4        ; normalize head: exit if top bit of a2 set
c8 slli a2,a2,1
cc slli a3,a3,1
d0 bltu a2,a1 →c4     ; back-edge while a2 < a1
d4 li a0,0            ; divide setup
d8 bltu a1,a2 →e4     ; divide head: skip subtract if a1 < a2
dc sub a1,a1,a2
e0 or a0,a0,a3
e4 srli a3,a3,1
e8 srli a2,a2,1
ec bnez a3 →d8        ; back-edge while a3 ≠ 0
f0 ret
```
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The `or`-to-add auxiliary (`or a0,a0,a3`)

`a % 2^(j+1) = 0 → a ||| 2^j = a + 2^j`: when the low `j+1` bits of `a` are clear,
setting bit `j` is exactly adding `2^j`. Proved per-`testBit` with `a = q·2^(j+1)`. -/
theorem or_two_pow_eq_add (a j : Nat) (h : a % 2^(j+1) = 0) :
    a ||| 2^j = a + 2^j := by
  have hdvd : 2^(j+1) ∣ a := Nat.dvd_of_mod_eq_zero h
  obtain ⟨q, hq⟩ := hdvd
  rw [hq]
  have hlt : 2^j < 2^(j+1) := Nat.pow_lt_pow_right (by decide) (by omega)
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, Nat.testBit_two_pow_mul_add q hlt i]
  rw [Nat.mul_comm (2^(j+1)) q, Nat.testBit_mul_two_pow q i (j+1), Nat.testBit_two_pow]
  by_cases hi : i < j + 1
  · simp only [hi, if_true]
    have h1 : decide (j + 1 ≤ i) = false := by simp only [decide_eq_false_iff_not, Nat.not_le]; omega
    rw [h1, Bool.false_and, Bool.false_or]
  · simp only [hi, if_false]
    have hge : decide (j + 1 ≤ i) = true := by simp only [decide_eq_true_eq]; omega
    have hjne : decide (j = i) = false := by simp only [decide_eq_false_iff_not]; omega
    rw [hge, Bool.true_and, hjne, Bool.or_false]

/-! ## Shift-doubling / halving `toNat` bridges for the loops -/

/-! ## The normalize loop (head `c4`)

`a0 = -1` (call it `neg1`) and `a1 = n` are fixed; `a2 = d·2^k`, `a3 = 2^k` double
each iteration. The loop head is `c4` (`blez a2`); the back-edge is `d0 → c4`.

Structure predicate `NrmK d a2 a3`: the shared `∃ k` invariant on `a2`/`a3`. -/

/-! ## The `c0` entry into the normalize loop

`bgeu a2,a1` at `c0` (with `a2 = d`, `a1 = n`, `a3 = 1`, `k = 0`): if `d ≥ n`
(bgeu true) go straight to `d4` (`AtDoneN`, `n ≤ d < 2·d`); else fall to `c4`
(`AtHeadN`). Either way land in `NrmI`. -/

/-! ## The divide loop (head `d8`)

Restoring shift-subtract long division. `a2 = d·2^j`, `a3 = 2^j` halve each
iteration; `a0` accumulates quotient bits from position `j` downward; `a1` is the
running remainder. Loop head `d8` (`bltu a1,a2`), back-edge `ec → d8`.

`DivK d a2 a3 j`: the structural `a2 = d·2^j ∧ a3 = 2^j ∧ d·2^j < 2^64` part. -/
def DivK (d a2 a3 : BitVec 64) (j : Nat) : Prop :=
  a2.toNat = d.toNat * 2^j ∧ a3.toNat = 2^j ∧ d.toNat * 2^j < 2^64

/-! ### Divide-loop arithmetic helpers -/

/-- Sub-path mod bridge: `a % 2^(j+1) = 0 ⇒ (a + 2^j) % 2^j = 0`. -/
theorem mod_add_pow (a j : Nat) (h : a % 2^(j+1) = 0) : (a + 2^j) % 2^j = 0 := by
  have hdvd : 2^(j+1) ∣ a := Nat.dvd_of_mod_eq_zero h
  have h1 : 2^j ∣ 2^(j+1) := Nat.pow_dvd_pow 2 (by omega)
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add (Nat.dvd_trans h1 hdvd) (Nat.dvd_refl _))

/-- Skip-path mod bridge: `a % 2^(j+1) = 0 ⇒ a % 2^j = 0`. -/
theorem mod_drop_pow (a j : Nat) (h : a % 2^(j+1) = 0) : a % 2^j = 0 := by
  have hdvd : 2^(j+1) ∣ a := Nat.dvd_of_mod_eq_zero h
  have h1 : 2^j ∣ 2^(j+1) := Nat.pow_dvd_pow 2 (by omega)
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans h1 hdvd)

/-- The `or a0,a0,a3` result as an addition, when `a3 = 2^j` and bit `j` of `a0`
is clear (`a0 % 2^(j+1) = 0`): `(a0 ||| a3).toNat = a0.toNat + 2^j`. -/
theorem or_a3_toNat (a0 a3 : BitVec 64) (j : Nat) (ha3 : a3.toNat = 2^j)
    (hmod : a0.toNat % 2^(j+1) = 0) : (a0 ||| a3).toNat = a0.toNat + 2^j := by
  rw [BitVec.toNat_or, ha3, or_two_pow_eq_add a0.toNat j hmod]

/-! ### One divide-loop iteration (`div_loop_body`)

Splits on `j = 0` (last iteration ⇒ exit to `f0`, `AtDoneD`) vs `j ≥ 1` (back-edge
to `d8`, `AtHeadD`), and inside each on the `bltu a1,a2` guard (sub vs skip). -/

/-! ## Prefix `ac → c0` and the full `udivdi3_spec`

The straight-line prefix establishes at `c0`: `a0 = -1`, `a1 = n`, `a2 = d`,
`a3 = 1`. Then `entry_c0` + `norm_loop_to_done` runs the normalize loop to `d4`;
`utr_d4_d8` (`li a0,0`) enters the divide loop (`AtHeadD`, `j = K`);
`div_loop_to_done` runs it to `f0`; `utr_f0_ret` returns. -/

end Vsa.Sim
