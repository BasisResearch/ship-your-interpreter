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
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

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

/-- `slli a,a,1` doubles exactly when `2·a < 2^64`. (Rephrasing `shl1_toNat`.) -/
theorem shl_double (a : BitVec 64) (h : 2 * a.toNat < 2^64) :
    (a <<< (1:Nat)).toNat = 2 * a.toNat := by
  rw [shl1_toNat a h]; exact Nat.mul_comm a.toNat 2

/-- Normalize-loop measure strictly decreases: doubling a non-top-bit `a2`
raises `a2.toNat`, so `2^64 - a2.toNat` drops. -/
theorem normMeasure_lt (a2 : BitVec 64) (hpos : 0 < a2.toNat) (h : 2 * a2.toNat < 2^64) :
    2^64 - (a2 <<< (1:Nat)).toNat < 2^64 - a2.toNat := by
  rw [shl_double a2 h]; omega

/-! ## The normalize loop (head `c4`)

`a0 = -1` (call it `neg1`) and `a1 = n` are fixed; `a2 = d·2^k`, `a3 = 2^k` double
each iteration. The loop head is `c4` (`blez a2`); the back-edge is `d0 → c4`.

Structure predicate `NrmK d a2 a3`: the shared `∃ k` invariant on `a2`/`a3`. -/

/-- The `∃ k, a2 = d·2^k ∧ a3 = 2^k ∧ d·2^k < 2^64` structural invariant. -/
def NrmK (d a2 a3 : BitVec 64) : Prop :=
  ∃ k, a2.toNat = d.toNat * 2^k ∧ a3.toNat = 2^k ∧ d.toNat * 2^k < 2^64

/-- At the normalize-loop head `c4`, with the shared invariant. -/
def AtHeadN (g : (R : Register) → Option (RegisterType R)) (d n neg1 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a2 a3, Ust g (0x800046c4#64) neg1 n a2 a3 r m0 o c ∧ NrmK d a2 a3

/-- Normalize done at `d4`: divide-loop entry facts (`a2 = d·2^K`, `n < 2·a2`). -/
def AtDoneN (g : (R : Register) → Option (RegisterType R)) (d n neg1 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a2 a3, Ust g (0x800046d4#64) neg1 n a2 a3 r m0 o c ∧ NrmK d a2 a3 ∧ n.toNat < 2 * a2.toNat

def NrmI (g : (R : Register) → Option (RegisterType R)) (d n neg1 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  AtHeadN g d n neg1 r m0 o c ∨ AtDoneN g d n neg1 r m0 o c

/-- Guard: at `c4` (`AtHeadN`). -/
def NrmB (g : (R : Register) → Option (RegisterType R)) (d n neg1 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  AtHeadN g d n neg1 r m0 o c

/-- Measure: `2^64 - a2.toNat` **at the loop head `c4`**, else `0`. The PC guard
makes the measure strictly drop on the exit edge (to `d4`, where it is `0`) as well
as on the back-edge (to `c4`, where `a2` has doubled). -/
def NrmMu (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some (0x800046c4#64)
  then 2^64 - ((c.σ.regs.get? Register.x12).getD (0#64)).toNat
  else 0

/-- One normalize-loop iteration from `c4` reaches `c4` again (measure ↓) or `d4`
(exit). Uses `d ≠ 0` to keep the measure strict on the back-edge. -/
theorem norm_loop_body (g : (R : Register) → Option (RegisterType R)) (d n neg1 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hd : 0 < d.toNat) (mmeas : Nat) :
    Triple (fun c => NrmI g d n neg1 r m0 o c ∧ NrmB g d n neg1 r m0 o c ∧ NrmMu c = mmeas)
           (fun c => NrmI g d n neg1 r m0 o c ∧ NrmMu c < mmeas) := by
  intro c hc
  obtain ⟨_, ⟨a2, a3, hSt, k, hk2, hk3, hkbnd⟩, hmu⟩ := hc
  have hmu_eq : NrmMu c = 2^64 - a2.toNat := by
    simp only [NrmMu, hSt.pc, hSt.a2, Option.getD_some, if_pos]
  rw [hmu_eq] at hmu
  -- mmeas is positive: a2 < 2^64 ⇒ 2^64 - a2 ≥ 1
  have ha2lt : a2.toNat < 2^64 := a2.isLt
  have hmpos : 0 < mmeas := by rw [← hmu]; omega
  -- a2 positive: d·2^k with d ≥ 1
  have ha2pos : 0 < a2.toNat := by rw [hk2]; exact Nat.mul_pos hd (Nat.two_pow_pos k)
  have ha2ne : a2 ≠ 0#64 := by intro h; rw [h] at ha2pos; simp at ha2pos
  -- On an exit to d4, the measure is 0 (PC ≠ c4), hence < mmeas.
  have exit_mu : ∀ (c' : Config), c'.σ.regs.get? Register.PC = some (0x800046d4#64) → NrmMu c' < mmeas := by
    intro c' hpc'
    have : NrmMu c' = 0 := by
      simp only [NrmMu, hpc']
      rw [if_neg (by intro h; injection h with h; exact absurd h (by decide))]
    rw [this]; exact hmpos
  -- c4: blez a2 case split
  rcases blez_cases a2 with hblez | hblez
  · -- blez true: top bit set, exit to d4 with same k
    have htop : 2^63 ≤ a2.toNat := toInt_nonpos_top a2 (blez_true a2 hblez) ha2ne
    obtain ⟨c1, hs1, hSt1⟩ := utr_c4_d4 g neg1 n a2 a3 r m0 o hblez c hSt
    refine ⟨c1, hs1, Or.inr ⟨a2, a3, hSt1, ⟨k, hk2, hk3, hkbnd⟩, ?_⟩, exit_mu c1 hSt1.pc⟩
    have hnlt : n.toNat < 2^64 := n.isLt
    omega
  · -- blez false: top bit clear ⇒ 2·a2 < 2^64. Do the shifts.
    have hnotop : 2 * a2.toNat < 2^64 := toInt_pos_notop a2 (blez_false a2 hblez)
    obtain ⟨c1, hs1, hSt1⟩ := utr_c4_c8 g neg1 n a2 a3 r m0 o hblez c hSt
    obtain ⟨c2, hs2, hSt2⟩ := utr_c8_cc g neg1 n a2 a3 r m0 o c1 hSt1
    obtain ⟨c3, hs3, hSt3⟩ := utr_cc_d0 g neg1 n (a2 <<< (1:Nat)) a3 r m0 o c2 hSt2
    -- doubled values
    have hpk : (2:Nat)^(k+1) = 2 * 2^k := by rw [Nat.pow_succ, Nat.mul_comm]
    have hdd : d.toNat * 2^(k+1) = 2 * (d.toNat * 2^k) := by
      rw [hpk, Nat.mul_left_comm]
    have hd2 : (a2 <<< (1:Nat)).toNat = d.toNat * 2^(k+1) := by
      rw [shl_double a2 hnotop, hk2, hdd]
    have hd3 : (a3 <<< (1:Nat)).toNat = 2^(k+1) := by
      have hh : 2 * a3.toNat < 2^64 := by
        rw [hk3]
        have hle : 2^k ≤ d.toNat * 2^k := Nat.le_mul_of_pos_left _ hd
        omega
      rw [shl_double a3 hh, hk3, hpk]
    have hbnd2 : d.toNat * 2^(k+1) < 2^64 := by
      rw [hdd, ← hk2]; exact hnotop
    -- d0: bltu a2', a1  (a2' = a2<<<1, a1 = n)
    rcases bltu_cases (a2 <<< (1:Nat)) n with hbltu | hbltu
    · -- back-edge to c4: a2 < n, loop continues
      obtain ⟨c4', hs4, hSt4⟩ := utr_d0_c4 g neg1 n (a2 <<< (1:Nat)) (a3 <<< (1:Nat)) r m0 o hbltu c3 hSt3
      refine ⟨c4', hs1.trans (hs2.trans (hs3.trans hs4)),
        Or.inl ⟨_, _, hSt4, ⟨k+1, hd2, hd3, hbnd2⟩⟩, ?_⟩
      -- NrmMu c4' = 2^64 - a2'.toNat < 2^64 - a2.toNat = mmeas
      have hmu4 : NrmMu c4' = 2^64 - (a2 <<< (1:Nat)).toNat := by
        simp only [NrmMu, hSt4.pc, hSt4.a2, Option.getD_some, if_pos]
      rw [hmu4, ← hmu]
      exact normMeasure_lt a2 ha2pos hnotop
    · -- exit to d4: a2 ≥ n ⇒ n ≤ a2 < 2·a2
      obtain ⟨c4', hs4, hSt4⟩ := utr_d0_d4 g neg1 n (a2 <<< (1:Nat)) (a3 <<< (1:Nat)) r m0 o hbltu c3 hSt3
      have hge : n.toNat ≤ (a2 <<< (1:Nat)).toNat := bltu_false (a2 <<< (1:Nat)) n hbltu
      refine ⟨c4', hs1.trans (hs2.trans (hs3.trans hs4)),
        Or.inr ⟨_, _, hSt4, ⟨k+1, hd2, hd3, hbnd2⟩, ?_⟩, exit_mu c4' hSt4.pc⟩
      -- n < 2·a2'
      have : 0 < (a2 <<< (1:Nat)).toNat := by rw [hd2]; exact Nat.mul_pos hd (Nat.two_pow_pos _)
      omega

/-- The normalize loop runs from `NrmI` to `AtDoneN` (at `d4`). -/
theorem norm_loop_to_done (g : (R : Register) → Option (RegisterType R)) (d n neg1 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hd : 0 < d.toNat) :
    Triple (NrmI g d n neg1 r m0 o) (AtDoneN g d n neg1 r m0 o) := by
  have hloop := Triple.loop (I := NrmI g d n neg1 r m0 o) (B := NrmB g d n neg1 r m0 o)
    NrmMu (norm_loop_body g d n neg1 r m0 o hd)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  · -- AtHeadN g with ¬NrmB ⇒ contradiction (AtHeadN = NrmB)
    exact absurd hHead hnB
  · exact ⟨c, .refl c, hDone⟩

/-! ## The `c0` entry into the normalize loop

`bgeu a2,a1` at `c0` (with `a2 = d`, `a1 = n`, `a3 = 1`, `k = 0`): if `d ≥ n`
(bgeu true) go straight to `d4` (`AtDoneN`, `n ≤ d < 2·d`); else fall to `c4`
(`AtHeadN`). Either way land in `NrmI`. -/
theorem entry_c0 (g : (R : Register) → Option (RegisterType R)) (d n neg1 r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hd : 0 < d.toNat) (hdbnd : d.toNat < 2^64) :
    Triple (Ust g (0x800046c0#64) neg1 n d (1#64) r m0 o) (NrmI g d n neg1 r m0 o) := by
  intro c hSt
  have hK : NrmK d d (1#64) := by
    refine ⟨0, ?_, ?_, ?_⟩
    · simp
    · simp
    · simpa using hdbnd
  rcases bgeu_cases d n with hb | hb
  · -- d ≥ n: exit to d4, n < 2·d
    obtain ⟨c1, hs1, hSt1⟩ := utr_c0_d4 g neg1 n d (1#64) r m0 o hb c hSt
    have hge : n.toNat ≤ d.toNat := bgeu_true d n hb
    exact ⟨c1, hs1, Or.inr ⟨d, 1#64, hSt1, hK, by omega⟩⟩
  · -- d < n: to c4, AtHeadN
    obtain ⟨c1, hs1, hSt1⟩ := utr_c0_c4 g neg1 n d (1#64) r m0 o hb c hSt
    exact ⟨c1, hs1, Or.inl ⟨d, 1#64, hSt1, hK⟩⟩

/-! ## The divide loop (head `d8`)

Restoring shift-subtract long division. `a2 = d·2^j`, `a3 = 2^j` halve each
iteration; `a0` accumulates quotient bits from position `j` downward; `a1` is the
running remainder. Loop head `d8` (`bltu a1,a2`), back-edge `ec → d8`.

`DivK d a2 a3 j`: the structural `a2 = d·2^j ∧ a3 = 2^j ∧ d·2^j < 2^64` part. -/
def DivK (d a2 a3 : BitVec 64) (j : Nat) : Prop :=
  a2.toNat = d.toNat * 2^j ∧ a3.toNat = 2^j ∧ d.toNat * 2^j < 2^64

/-- At the divide-loop head `d8`, with the full division invariant. -/
def AtHeadD (g : (R : Register) → Option (RegisterType R)) (d n r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a0 a1 a2 a3, Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o c ∧ ∃ j,
    DivK d a2 a3 j ∧ a0.toNat % 2^(j+1) = 0 ∧
    n.toNat = d.toNat * a0.toNat + a1.toNat ∧ a1.toNat < 2 * a2.toNat

/-- Divide done at `f0`: `a0 = n/d`, `a1 = n%d` (as `Nat` facts). -/
def AtDoneD (g : (R : Register) → Option (RegisterType R)) (d n r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a0 a1 a2 a3, Ust g (0x800046f0#64) a0 a1 a2 a3 r m0 o c ∧
    a0.toNat = n.toNat / d.toNat ∧ a1.toNat = n.toNat % d.toNat

def DvI (g : (R : Register) → Option (RegisterType R)) (d n r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  AtHeadD g d n r m0 o c ∨ AtDoneD g d n r m0 o c

/-- Guard: at `d8` (`AtHeadD`) with a nonzero `a3`. -/
def DvB (g : (R : Register) → Option (RegisterType R)) (d n r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ a0 a1 a2 a3, Ust g (0x800046d8#64) a0 a1 a2 a3 r m0 o c ∧ (∃ j,
    DivK d a2 a3 j ∧ a0.toNat % 2^(j+1) = 0 ∧
    n.toNat = d.toNat * a0.toNat + a1.toNat ∧ a1.toNat < 2 * a2.toNat) ∧ a3 ≠ 0#64

/-- Measure: `a3.toNat` **at the loop head `d8`**, else `0`. -/
def DvMu (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some (0x800046d8#64)
  then ((c.σ.regs.get? Register.x13).getD (0#64)).toNat
  else 0

/-! ### Divide-loop arithmetic helpers -/

/-- `2^j / 2 = 2^(j-1)` and `(d·2^j)/2 = d·2^(j-1)` for `j ≥ 1`. -/
theorem half_pow (j : Nat) (hj : 1 ≤ j) : (2:Nat)^j / 2 = 2^(j-1) := by
  have h : (2:Nat)^j = 2^(j-1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  rw [h, Nat.mul_div_cancel _ (by decide)]

theorem half_mul_pow (d j : Nat) (hj : 1 ≤ j) : (d * 2^j) / 2 = d * 2^(j-1) := by
  have h : (2:Nat)^j = 2^(j-1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  rw [h, ← Nat.mul_assoc, Nat.mul_div_cancel _ (by decide)]

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

/-- Halved `a3 = 2^j`: `(a3>>>1).toNat = 2^(j-1)` for `j ≥ 1`, `= 0` for `j = 0`. -/
theorem a3_half (a3 : BitVec 64) (j : Nat) (hk3 : a3.toNat = 2^j) :
    (a3 >>> (1:Nat)).toNat = 2^j / 2 := by rw [shr1_toNat, hk3]

/-- `d·2^j` halved for `j ≥ 1`: `(a2>>>1).toNat = d·2^(j-1)`. -/
theorem a2_half (d a2 : BitVec 64) (j : Nat) (hj : 1 ≤ j) (hk2 : a2.toNat = d.toNat * 2^j) :
    (a2 >>> (1:Nat)).toNat = d.toNat * 2^(j-1) := by
  rw [shr1_toNat, hk2, half_mul_pow d.toNat j hj]

/-- `2·(d·2^(j-1)) = d·2^j` for `j ≥ 1`. -/
theorem two_mul_pow_pred (d j : Nat) (hj : 1 ≤ j) : 2 * (d * 2^(j-1)) = d * 2^j := by
  have h : (2:Nat)^j = 2 * 2^(j-1) := by rw [← Nat.pow_succ']; congr 1; omega
  rw [h, Nat.mul_left_comm]

/-! ### One divide-loop iteration (`div_loop_body`)

Splits on `j = 0` (last iteration ⇒ exit to `f0`, `AtDoneD`) vs `j ≥ 1` (back-edge
to `d8`, `AtHeadD`), and inside each on the `bltu a1,a2` guard (sub vs skip). -/
theorem div_loop_body (g : (R : Register) → Option (RegisterType R)) (d n r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hd : 0 < d.toNat) (mmeas : Nat) :
    Triple (fun c => DvI g d n r m0 o c ∧ DvB g d n r m0 o c ∧ DvMu c = mmeas)
           (fun c => DvI g d n r m0 o c ∧ DvMu c < mmeas) := by
  intro c hc
  obtain ⟨_, ⟨a0, a1, a2, a3, hSt, ⟨j, ⟨hk2, hk3, hkbnd⟩, hmod, hprog, hbound⟩, ha3ne⟩, hmu⟩ := hc
  have hmu_eq : DvMu c = a3.toNat := by
    simp only [DvMu, hSt.pc, hSt.a3, Option.getD_some, if_pos]
  rw [hmu_eq] at hmu
  -- a3 = 2^j ≥ 1, so mmeas ≥ 1
  have ha3pos : 0 < a3.toNat := by rw [hk3]; exact Nat.two_pow_pos j
  have hmpos : 0 < mmeas := by rw [← hmu]; exact ha3pos
  -- exit-to-f0 has measure 0 < mmeas
  have exit_mu : ∀ (c' : Config), c'.σ.regs.get? Register.PC = some (0x800046f0#64) → DvMu c' < mmeas := by
    intro c' hpc'
    have : DvMu c' = 0 := by
      simp only [DvMu, hpc']
      rw [if_neg (by intro h; injection h with h; exact absurd h (by decide))]
    rw [this]; exact hmpos
  by_cases hj : j = 0
  · -- j = 0: a2 = d, a3 = 1, exit to f0 (AtDoneD)
    subst hj
    have hk2' : a2.toNat = d.toNat := by simpa using hk2
    have hmod' : a0.toNat % 2 = 0 := by simpa using hmod
    have hbound' : a1.toNat < 2 * d.toNat := by rw [hk2'] at hbound; exact hbound
    rcases bltu_cases a1 a2 with hbltu | hbltu
    · -- a1 < d: skip subtract. a0 = quotient, a1 = remainder.
      obtain ⟨c1, hs1, hSt1⟩ := utr_d8_e4 g a0 a1 a2 a3 r m0 o hbltu c hSt
      obtain ⟨c2, hs2, hSt2⟩ := utr_e4_e8 g a0 a1 a2 a3 r m0 o c1 hSt1
      obtain ⟨c3, hs3, hSt3⟩ := utr_e8_ec g a0 a1 a2 (a3 >>> (1:Nat)) r m0 o c2 hSt2
      have ha1lt : a1.toNat < d.toNat := by have := bltu_true a1 a2 hbltu; rw [hk2'] at this; exact this
      -- bnez a3' with a3' = a3>>>1 = 1>>>1 = 0 ⇒ not taken ⇒ f0
      have ha3half0 : (a3 >>> (1:Nat)) = 0#64 := by
        apply BitVec.eq_of_toNat_eq; rw [a3_half a3 0 hk3]; decide
      have hbnz : ((a3 >>> (1:Nat)) != (0#64)) = false := by rw [ha3half0]; rfl
      obtain ⟨c4, hs4, hSt4⟩ := utr_ec_f0 g a0 a1 (a2 >>> (1:Nat)) (a3 >>> (1:Nat)) r m0 o hbnz c3 hSt3
      -- a0 = n/d, a1 = n%d
      have hdm : n.toNat / d.toNat = a0.toNat ∧ n.toNat % d.toNat = a1.toNat := by
        rw [Nat.div_mod_unique hd]; exact ⟨by omega, ha1lt⟩
      refine ⟨c4, hs1.trans (hs2.trans (hs3.trans hs4)),
        Or.inr ⟨a0, a1, _, _, hSt4, hdm.1.symm, hdm.2.symm⟩, exit_mu c4 hSt4.pc⟩
    · -- a1 ≥ d: subtract. a0' = a0+1, a1' = a1-d.
      obtain ⟨c1, hs1, hSt1⟩ := utr_d8_dc g a0 a1 a2 a3 r m0 o hbltu c hSt
      obtain ⟨c2, hs2, hSt2⟩ := utr_dc_e0 g a0 a1 a2 a3 r m0 o c1 hSt1
      obtain ⟨c3, hs3, hSt3⟩ := utr_e0_e4 g a0 (a1 - a2) a2 a3 r m0 o c2 hSt2
      obtain ⟨c4, hs4, hSt4⟩ := utr_e4_e8 g (a0 ||| a3) (a1 - a2) a2 a3 r m0 o c3 hSt3
      obtain ⟨c5, hs5, hSt5⟩ := utr_e8_ec g (a0 ||| a3) (a1 - a2) a2 (a3 >>> (1:Nat)) r m0 o c4 hSt4
      have hge : a2.toNat ≤ a1.toNat := bltu_false a1 a2 hbltu
      have ha2le : a2 ≤ a1 := BitVec.le_def.mpr hge
      have ha1sub : (a1 - a2).toNat = a1.toNat - a2.toNat := BitVec.toNat_sub_of_le ha2le
      -- a0 ||| a3 = a0 + 1 (j=0, 2^0=1)
      have hora0 : (a0 ||| a3).toNat = a0.toNat + 1 := by
        have := or_a3_toNat a0 a3 0 hk3 hmod
        simpa using this
      have ha3half0 : (a3 >>> (1:Nat)) = 0#64 := by
        apply BitVec.eq_of_toNat_eq; rw [a3_half a3 0 hk3]; decide
      have hbnz : ((a3 >>> (1:Nat)) != (0#64)) = false := by rw [ha3half0]; rfl
      obtain ⟨c6, hs6, hSt6⟩ := utr_ec_f0 g (a0 ||| a3) (a1 - a2) (a2 >>> (1:Nat)) (a3 >>> (1:Nat)) r m0 o hbnz c5 hSt5
      -- a0' = n/d, a1' = n%d
      have ha1'lt : (a1 - a2).toNat < d.toNat := by rw [ha1sub, hk2']; omega
      have hprog' : n.toNat = d.toNat * (a0 ||| a3).toNat + (a1 - a2).toNat := by
        rw [hora0, ha1sub, hk2']; rw [Nat.mul_add]; omega
      have hdm : n.toNat / d.toNat = (a0 ||| a3).toNat ∧ n.toNat % d.toNat = (a1 - a2).toNat := by
        rw [Nat.div_mod_unique hd]; exact ⟨by omega, ha1'lt⟩
      refine ⟨c6, hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans hs6)))),
        Or.inr ⟨_, _, _, _, hSt6, hdm.1.symm, hdm.2.symm⟩, exit_mu c6 hSt6.pc⟩
  · -- j ≥ 1: back-edge to d8 (AtHeadD g with j-1)
    have hj1 : 1 ≤ j := by omega
    have ha3half : (a3 >>> (1:Nat)).toNat = 2^(j-1) := by rw [a3_half a3 j hk3, half_pow j hj1]
    have ha2half : (a2 >>> (1:Nat)).toNat = d.toNat * 2^(j-1) := a2_half d a2 j hj1 hk2
    have ha3half_ne : (a3 >>> (1:Nat)) ≠ 0#64 := by
      intro h; rw [h] at ha3half
      have hz : (0#64 : BitVec 64).toNat = 0 := by decide
      rw [hz] at ha3half
      have := Nat.two_pow_pos (j-1); omega
    have hbnz : ((a3 >>> (1:Nat)) != (0#64)) = true := by rw [bne_iff_ne]; exact ha3half_ne
    have hkbnd' : d.toNat * 2^(j-1) < 2^64 := by
      have hle : d.toNat * 2^(j-1) ≤ d.toNat * 2^j :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
      omega
    have hmeas_lt : (a3 >>> (1:Nat)).toNat < a3.toNat := by
      rw [ha3half, hk3]; exact Nat.pow_lt_pow_right (by decide) (by omega)
    rcases bltu_cases a1 a2 with hbltu | hbltu
    · -- skip subtract
      obtain ⟨c1, hs1, hSt1⟩ := utr_d8_e4 g a0 a1 a2 a3 r m0 o hbltu c hSt
      obtain ⟨c2, hs2, hSt2⟩ := utr_e4_e8 g a0 a1 a2 a3 r m0 o c1 hSt1
      obtain ⟨c3, hs3, hSt3⟩ := utr_e8_ec g a0 a1 a2 (a3 >>> (1:Nat)) r m0 o c2 hSt2
      obtain ⟨c4, hs4, hSt4⟩ := utr_ec_d8 g a0 a1 (a2 >>> (1:Nat)) (a3 >>> (1:Nat)) r m0 o hbnz c3 hSt3
      have ha1lt : a1.toNat < a2.toNat := bltu_true a1 a2 hbltu
      refine ⟨c4, hs1.trans (hs2.trans (hs3.trans hs4)),
        Or.inl ⟨a0, a1, _, _, hSt4, j-1, ⟨ha2half, ha3half, hkbnd'⟩, ?_, hprog, ?_⟩, ?_⟩
      · -- a0 % 2^(j-1+1) = a0 % 2^j = 0
        have : j - 1 + 1 = j := by omega
        rw [this]; exact mod_drop_pow a0.toNat j hmod
      · -- a1 < 2·(a2>>>1) = a2, and a1 < a2 ✓
        rw [ha2half, two_mul_pow_pred d.toNat j hj1, ← hk2]; exact ha1lt
      · -- measure
        have hmu4 : DvMu c4 = (a3 >>> (1:Nat)).toNat := by
          simp only [DvMu, hSt4.pc, hSt4.a3, Option.getD_some, if_pos]
        rw [hmu4, ← hmu]; exact hmeas_lt
    · -- subtract
      obtain ⟨c1, hs1, hSt1⟩ := utr_d8_dc g a0 a1 a2 a3 r m0 o hbltu c hSt
      obtain ⟨c2, hs2, hSt2⟩ := utr_dc_e0 g a0 a1 a2 a3 r m0 o c1 hSt1
      obtain ⟨c3, hs3, hSt3⟩ := utr_e0_e4 g a0 (a1 - a2) a2 a3 r m0 o c2 hSt2
      obtain ⟨c4, hs4, hSt4⟩ := utr_e4_e8 g (a0 ||| a3) (a1 - a2) a2 a3 r m0 o c3 hSt3
      obtain ⟨c5, hs5, hSt5⟩ := utr_e8_ec g (a0 ||| a3) (a1 - a2) a2 (a3 >>> (1:Nat)) r m0 o c4 hSt4
      obtain ⟨c6, hs6, hSt6⟩ := utr_ec_d8 g (a0 ||| a3) (a1 - a2) (a2 >>> (1:Nat)) (a3 >>> (1:Nat)) r m0 o hbnz c5 hSt5
      have hge : a2.toNat ≤ a1.toNat := bltu_false a1 a2 hbltu
      have ha2le : a2 ≤ a1 := BitVec.le_def.mpr hge
      have ha1sub : (a1 - a2).toNat = a1.toNat - a2.toNat := BitVec.toNat_sub_of_le ha2le
      have hora0 : (a0 ||| a3).toNat = a0.toNat + 2^j := or_a3_toNat a0 a3 j hk3 hmod
      refine ⟨c6, hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans hs6)))),
        Or.inl ⟨_, _, _, _, hSt6, j-1, ⟨ha2half, ha3half, hkbnd'⟩, ?_, ?_, ?_⟩, ?_⟩
      · -- (a0 + 2^j) % 2^j = 0, and j-1+1 = j
        have hjj : j - 1 + 1 = j := by omega
        rw [hjj, hora0]; exact mod_add_pow a0.toNat j hmod
      · -- n = d·(a0+2^j) + (a1-a2), with a2 = d·2^j
        rw [hora0, ha1sub, Nat.mul_add, hk2]
        -- n = d·a0 + d·2^j + (a1 - d·2^j); a1 ≥ a2 = d·2^j
        rw [hk2] at hge; omega
      · -- a1' < 2·(a2>>>1) = a2; a1' = a1 - a2 < a2 since a1 < 2·a2
        rw [ha2half, two_mul_pow_pred d.toNat j hj1, ← hk2, ha1sub]; omega
      · have hmu6 : DvMu c6 = (a3 >>> (1:Nat)).toNat := by
          simp only [DvMu, hSt6.pc, hSt6.a3, Option.getD_some, if_pos]
        rw [hmu6, ← hmu]; exact hmeas_lt

/-- The divide loop runs from `DvI` to `AtDoneD` (at `f0`). On loop exit
(`DvI ∧ ¬DvB`) we are either already `AtDoneD`, or at `d8` with `a3 = 0` — but
`a3 = 2^j ≠ 0` in `AtHeadD`, so that branch is vacuous. -/
theorem div_loop_to_done (g : (R : Register) → Option (RegisterType R)) (d n r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String)
    (hd : 0 < d.toNat) :
    Triple (DvI g d n r m0 o) (AtDoneD g d n r m0 o) := by
  have hloop := Triple.loop (I := DvI g d n r m0 o) (B := DvB g d n r m0 o)
    DvMu (div_loop_body g d n r m0 o hd)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  · obtain ⟨a0, a1, a2, a3, hSt, j, ⟨hk2, hk3, hkbnd⟩, hmod, hprog, hbound⟩ := hHead
    have ha3ne : a3 ≠ 0#64 := by
      intro h; rw [h] at hk3
      have hz : (0#64 : BitVec 64).toNat = 0 := by decide
      rw [hz] at hk3; have := Nat.two_pow_pos j; omega
    exact absurd ⟨a0, a1, a2, a3, hSt, ⟨j, ⟨hk2, hk3, hkbnd⟩, hmod, hprog, hbound⟩, ha3ne⟩ hnB
  · exact ⟨c, .refl c, hDone⟩

/-! ## Prefix `ac → c0` and the full `udivdi3_spec`

The straight-line prefix establishes at `c0`: `a0 = -1`, `a1 = n`, `a2 = d`,
`a3 = 1`. Then `entry_c0` + `norm_loop_to_done` runs the normalize loop to `d4`;
`utr_d4_d8` (`li a0,0`) enters the divide loop (`AtHeadD`, `j = K`);
`div_loop_to_done` runs it to `f0`; `utr_f0_ret` returns. -/

/-- `li a0,-1` value. -/
private def neg1c : BitVec 64 := (0#64) + sign_extend (m := 64) (0xfff#12)
/-- `li a3,1` value equals `1#64`. -/
private theorem one_c : ((0#64) + sign_extend (m := 64) (0x001#12) : BitVec 64) = (1#64 : BitVec 64) := by
  apply BitVec.eq_of_toNat_eq; decide

/-- `udivdi3_pre n d r m0 o c`: entry `Ust` at `0x800046ac` with `x10 = n`, `x11 = d`,
`x1 = r`, `mem = m0`, plus `d ≠ 0` and `r` 4-aligned. -/
def udivdi3_pre (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  (∃ a2old a3old, Ust g (0x800046ac#64) n d a2old a3old r m0 o c) ∧ 0 < d.toNat ∧ r.toNat % 4 = 0

/-- `udivdi3_post`: PC back at `r`, `x10 = n / d` (`BitVec.udiv`), `x11 = n % d`,
`GoodState`, memory unchanged, `x1 = r` intact. Also surfaces that the scratch
registers `x12`/`x13` (which the divide loop writes as `a2`/`a3` = `d·2^0` and `0`
on the last iteration) are left defined — needed by callers whose next callee
reads `a2`/`a3` (e.g. the `%lld` decimal loop's second `__umoddi3`). -/
def udivdi3_post (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some (n / d) ∧ c.σ.regs.get? Register.x11 = some (n % d) ∧
  c.σ.regs.get? Register.x1 = some r ∧ c.tick < 2 ∧
  (∀ R : Register, NotWritten R → c.σ.regs.get? R = g R) ∧
  (∃ v, c.σ.regs.get? Register.x12 = some v) ∧ (∃ v, c.σ.regs.get? Register.x13 = some v)

/-- **`udivdi3_spec`** — total-correctness triple for libgcc `__hidden___udivdi3`
(unsigned 64-bit division). From the entry precondition (`x10 = n`, `x11 = d`,
`d ≠ 0`, `x1 = r` 4-aligned) the machine runs to the return address `r` with
`x10 = n / d` (`BitVec.udiv` = Nat division), `x11 = n % d`, `GoodState` preserved,
memory unchanged, and the return register `x1 = r` intact. -/
theorem udivdi3_spec (g : (R : Register) → Option (RegisterType R)) (n d r : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (udivdi3_pre g n d r m0 o) (udivdi3_post g n d r m0 o) := by
  -- Prefix ac → c0 establishing Ust c0 neg1 n d 1 r
  have hpre : Triple (udivdi3_pre g n d r m0 o)
      (fun c => Ust g (0x800046c0#64) neg1c n d (1#64) r m0 o c ∧ 0 < d.toNat ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨⟨a2old, a3old, hEntry⟩, hd, halign⟩ := hc
    obtain ⟨c1, hs1, hSt1⟩ := utr_ac_b0 g n d a2old a3old r m0 o c hEntry
    obtain ⟨c2, hs2, hSt2⟩ := utr_b0_b4 g n d d a3old r m0 o c1 hSt1
    obtain ⟨c3, hs3, hSt3⟩ := utr_b4_b8 g n n d a3old r m0 o c2 hSt2
    -- b8: beqz a2, a2 = d ≠ 0 ⇒ not taken
    have hbeq : (d == (0#64)) = false := by
      have hne : d ≠ 0#64 := by intro h; rw [h] at hd; simp at hd
      simpa using hne
    obtain ⟨c4, hs4, hSt4⟩ := utr_b8_bc g neg1c n d a3old r m0 o hbeq c3 hSt3
    obtain ⟨c5, hs5, hSt5⟩ := utr_bc_c0 g neg1c n d a3old r m0 o c4 hSt4
    -- fold a3 = (0#64)+sext(0x001) = 1#64
    rw [one_c] at hSt5
    exact ⟨c5, hs1.trans (hs2.trans (hs3.trans (hs4.trans hs5))), hSt5, hd, halign⟩
  -- entry_c0 → NrmI → AtDoneN g (normalize loop)
  have hnorm : Triple (fun c => Ust g (0x800046c0#64) neg1c n d (1#64) r m0 o c ∧ 0 < d.toNat ∧ r.toNat % 4 = 0)
      (fun c => AtDoneN g d n neg1c r m0 o c ∧ 0 < d.toNat ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨hSt, hd, halign⟩ := hc
    obtain ⟨c1, hs1, hI⟩ := entry_c0 g d n neg1c r m0 o hd d.isLt c hSt
    obtain ⟨c2, hs2, hDone⟩ := norm_loop_to_done g d n neg1c r m0 o hd c1 hI
    exact ⟨c2, hs1.trans hs2, hDone, hd, halign⟩
  -- d4 → d8 (li a0,0) entering divide loop, then div_loop_to_done → AtDoneD
  have hdiv : Triple (fun c => AtDoneN g d n neg1c r m0 o c ∧ 0 < d.toNat ∧ r.toNat % 4 = 0)
      (fun c => AtDoneD g d n r m0 o c ∧ r.toNat % 4 = 0) := by
    intro c hc
    obtain ⟨⟨a2, a3, hSt, ⟨K, hk2, hk3, hkbnd⟩, hn2a2⟩, hd, halign⟩ := hc
    -- utr_d4_d8: a0 := 0
    obtain ⟨c1, hs1, hSt1⟩ := utr_d4_d8 g neg1c n a2 a3 r m0 o c hSt
    -- AtHeadD g with j = K, a0 = 0
    have hHead : AtHeadD g d n r m0 o c1 := by
      refine ⟨0#64, n, a2, a3, hSt1, K, ⟨hk2, hk3, hkbnd⟩, ?_, ?_, hn2a2⟩
      · simp
      · simp
    obtain ⟨c2, hs2, hDone⟩ := div_loop_to_done g d n r m0 o hd c1 (Or.inl hHead)
    exact ⟨c2, hs1.trans hs2, hDone, halign⟩
  -- f0 → ret
  have hret : Triple (fun c => AtDoneD g d n r m0 o c ∧ r.toNat % 4 = 0) (udivdi3_post g n d r m0 o) := by
    -- Inline the `f0 → ret` step (mirrors `utr_f0_ret`) so we additionally read
    -- back `x12 = a2` and `x13 = a3` off the `ret` (`jr x0` writes only PC): the
    -- divide loop leaves them defined (`AtDoneD`'s `Ust` pins them).
    apply Triple.of_step
    intro c hc
    obtain ⟨⟨a0, a1, a2, a3, hSt, hq, hr⟩, halign⟩ := hc
    obtain ⟨vmi, hmi⟩ := hSt.minstret
    have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt r halign]; exact halign
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_800046f0 c.σ c.tick c.steps (0x800046f0#64) vmi r hSt.good hSt.pc hmi hSt.ra hSt.loaded rfl htgt hSt.tick
    -- a0 = n/d, a1 = n%d as BitVec
    have ha0eq : a0 = n / d := by apply BitVec.eq_of_toNat_eq; rw [hq, BitVec.toNat_udiv]
    have ha1eq : a1 = n % d := by apply BitVec.eq_of_toNat_eq; rw [hr, BitVec.toNat_umod]
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
      hG', by rw [hmem']; exact hSt.mem, by rw [hobs.out]; exact hSt.sailOut, by rw [obs_jr_pc hobs, ret_tgt r halign],
      ha0eq ▸ obs_jr_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a0,
      ha1eq ▸ obs_jr_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a1,
      obs_jr_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.ra,
      hi',
      fun R hR => (frame_jr hobs R hR).trans (hSt.hframe R hR),
      ⟨a2, obs_jr_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a2⟩,
      ⟨a3, obs_jr_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hSt.a3⟩⟩
  exact (((hpre.seq hnorm).seq hdiv).seq hret)

end Vsa.Sim
