import VsaIris.Interp.HelperRun
import VsaIris.Interp.BinArm
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.DivSpec3

/-!
# libgcc's multiply and divide, inline in a run (lane E2)

`eval_binary`'s `*`, `/`, `%` call libgcc (`__muldi3` `0x80004640`,
`__divdi3` `0x800046a4`, `__moddi3` `0x80004728`; RV64I has no `M`
extension here). None touches memory or the stack, so a run FOLLOWS the call
(`iw_jal`) instead of lending a helper its registers: each routine is one
lemma in continuation form over the interpreter's symbolic run `IW`, stated
for any data view, owned bytes and end condition, with the result in `a0` at
the return address and every register outside the routine's scratch kept.
`__divdi3` and `__moddi3` overwrite `ra` with their inner call's link, which
a `helperSpec` (it returns `ra = r`) could not state.

* `mul_iw`: the shift-add loop, invariant `a0 + a2 * a1 = x * y` (VSA's
  `invmul_bv`), strong induction on the shrinking multiplier (`shr_lt`).
* `udiv_iw` (`__hidden___udivdi3`): the normalize loop (`udiv_loop1`, strong
  induction on `n - a2`) and the restoring divide loop (`udiv_loop2`,
  induction on the bit position, invariant VSA's `DivK`), quotient and
  remainder as `n / d`, `n % d`.
* `divdi3_iw`, `moddi3_iw`: the four sign cases, each one `udiv_iw` on the
  magnitudes; the results are the source's `wrap64 (a.tdiv b)` and
  `wrap64 (a.tmod b)` (VSA's `res_div_same`/`res_div_mixed`/`res_pos`/
  `res_neg`; `INT64_MIN / -1` wraps, `wrap64_tdiv_min`).

Loops by fuel induction, not Löb: xv6iris `ProofMemset.v:1-9`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr

/-- The shift-add step keeps `acc + a2 * a1`. -/
theorem mul_step (acc a2 a1 : BitVec 64) :
    acc + a2 * a1 = (if a1 &&& 1#64 = 0#64 then acc else acc + a2) + (a2 <<< 1) * (a1 >>> 1) := by
  rw [Vsa.Sim.invmul_bv a2 a1]
  split
  · rename_i h; rw [h]; simp
  · rename_i h
    have hm : (a1 &&& 1#64).toNat = a1.toNat % 2 := by
      rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.and_one_is_mod]
    have : a1 &&& 1#64 = 1#64 := by
      apply BitVec.eq_of_toNat_eq
      have h3 : (a1 &&& 1#64).toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq (by simpa using h0))
      rw [hm] at h3 ⊢; show a1.toNat % 2 = 1; omega
    rw [this]; simp; rw [BitVec.add_assoc, BitVec.add_comm a2]

/-- Registers `__muldi3` keeps: all but `a0`–`a3`. -/
abbrev MulKeep (R R0 : Nat → BitVec 64) : Prop := ∀ z, z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → R z = R0 z

/-- **The shift-add loop** (`0x80004648`), continuation form. -/
theorem mul_loop {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (x y r : BitVec 64) (R0 : Nat → BitVec 64)
    (Mt : Mem) (hal : r.toNat % 4 = 0) (hr : R0 1 = r)
    (hk : ∀ R', R' 10 = x * y → MulKeep R' R0 → IW live Dt DA S Q r R' Mt) :
    ∀ n (R : Nat → BitVec 64), (R 11).toNat = n → R 10 + R 12 * R 11 = x * y → MulKeep R R0 →
      IW live Dt DA S Q 0x80004648#64 R Mt := by
  intro n
  refine Nat.strongRecOn n ?_
  intro n ih R hn hinv hkp
  have h1 : R 1 = r := (hkp 1 (by decide) (by decide) (by decide) (by decide)).trans hr
  apply it_80004648 hlive
  ix_run hlive at 0x80004648
  all_goals first
    | (simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h1]; exact hal)
    | skip
  case hT.hT hb hz =>
    refine ih _ ?_ _ rfl ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hz ⊢
      rw [← hn]; exact Vsa.Sim.shr_lt _ (fun h0 => hz (by rw [h0]; rfl))
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [← hinv, mul_step (R 10) (R 12) (R 11)]; simp [hb]
    · intro z h10 h11 h12 h13
      simp only [upd_apply, h11, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13
  case hF.hT hb hz =>
    refine ih _ ?_ _ rfl ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hz ⊢
      rw [← hn]; exact Vsa.Sim.shr_lt _ (fun h0 => hz (by rw [h0]; rfl))
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [← hinv, mul_step (R 10) (R 12) (R 11)]; simp [hb]
    · intro z h10 h11 h12 h13
      simp only [upd_apply, h10, h11, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13
  case hT.hF.hk hb hz =>
    rw [h1]
    refine hk _ ?_ (fun z h10 h11 h12 h13 => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      have hz0 : R 11 >>> 1 = 0#64 := by simpa using hz
      rw [← hinv, mul_step (R 10) (R 12) (R 11), hz0]; simp [hb]
    · simp only [upd_apply, h11, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13
  case hF.hF.hk hb hz =>
    rw [h1]
    refine hk _ ?_ (fun z h10 h11 h12 h13 => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      have hz0 : R 11 >>> 1 = 0#64 := by simpa using hz
      rw [← hinv, mul_step (R 10) (R 12) (R 11), hz0]; simp [hb]
    · simp only [upd_apply, h10, h11, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13

/-- **`__muldi3`** (`0x80004640`) in continuation form: the wrapping product
in `a0` at the return to `r`. -/
theorem mul_iw {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (x y r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (h10 : R 10 = x) (h11 : R 11 = y) (hr : R 1 = r) (hal : r.toNat % 4 = 0)
    (hk : ∀ R', R' 10 = x * y → MulKeep R' R → IW live Dt DA S Q r R' Mt) :
    IW live Dt DA S Q 0x80004640#64 R Mt := by
  apply it_80004640 hlive
  apply it_80004644 hlive
  refine mul_loop hlive x y r R Mt hal hr hk _ _ rfl ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h10, h11]; simp
  · intro z h10' h11' h12 h13
    simp only [upd_apply, h10', h12, ite_false]

/-- Long division's result from its invariant at the last step. -/
theorem div_of_inv {n d q r : Nat} (hd : 0 < d) (h : n = d * q + r) (hr : r < d) :
    q = n / d ∧ r = n % d := by
  subst h
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- Registers other than the division's scratch `a0`–`a3` keep their values. -/
abbrev DivKeep (R R0 : Nat → BitVec 64) : Prop := ∀ z, z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → R z = R0 z

theorem shr1_toNat' (x : BitVec 64) : (x >>> 1).toNat = x.toNat / 2 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

/-- **The divide loop** (`0x800046d8`, restoring long division), by induction
on the bit position `j`, in continuation form: at the return the quotient
and remainder are in `a0`/`a1`. -/
theorem udiv_loop2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (n d r : BitVec 64) (R0 : Nat → BitVec 64)
    (Mt : Mem) (hal : r.toNat % 4 = 0) (hr : R0 1 = r)
    (hk : ∀ R', (R' 10).toNat = n.toNat / d.toNat → (R' 11).toNat = n.toNat % d.toNat →
      DivKeep R' R0 → IW live Dt DA S Q r R' Mt) :
    ∀ j (R : Nat → BitVec 64), Vsa.Sim.DivK d (R 12) (R 13) j → (R 10).toNat % 2 ^ (j + 1) = 0 →
      n.toNat = d.toNat * (R 10).toNat + (R 11).toNat → (R 11).toNat < 2 * (R 12).toNat →
      DivKeep R R0 → IW live Dt DA S Q 0x800046d8#64 R Mt := by
  intro j
  induction j with
  | zero =>
    intro R hK hq hn hlt hkp
    obtain ⟨hk2, hk3, hov⟩ := hK
    simp only [Nat.pow_zero, Nat.mul_one] at hk2 hk3 hov
    have hd0 : 0 < d.toNat := by
      rcases Nat.eq_zero_or_pos d.toNat with h | h
      · rw [h] at hk2; omega
      · exact h
    have hR1 : R 1 = r := (hkp 1 (by decide) (by decide) (by decide) (by decide)).trans hr
    have h3z : R 13 >>> 1 = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [shr1_toNat', hk3]; rfl
    refine it_800046d8 hlive ?_ ?_
    all_goals (intro hc; ix_run hlive at 0x800046d8)
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
    case refine_1.hF.hal => rw [hR1]; exact hal
    case refine_2.hF.hal => rw [hR1]; exact hal
    case refine_1.hF.hk =>
      rw [hR1]
      have := div_of_inv hd0 (n := n.toNat) (q := (R 10).toNat) (r := (R 11).toNat) hn (by omega)
      apply hk
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact this.1
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact this.2
      · intro z h10 h11 h12 h13
        simp only [upd_apply, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13
    case refine_2.hF.hk =>
      rw [hR1]
      have hsub : (R 11 - R 12).toNat = (R 11).toNat - (R 12).toNat :=
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
      have hor : (R 10 ||| R 13).toNat = (R 10).toNat + 1 := by
        have := Vsa.Sim.or_a3_toNat (R 10) (R 13) 0 (by simpa using hk3) (by simpa using hq)
        simpa using this
      have := div_of_inv hd0 (n := n.toNat) (q := (R 10).toNat + 1) (r := (R 11).toNat - (R 12).toNat)
        (by rw [hn, hk2, Nat.mul_add]; omega) (by omega)
      apply hk
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hor]; exact this.1
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hsub]; exact this.2
      · intro z h10 h11 h12 h13
        simp only [upd_apply, h10, h11, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13
  | succ j ih =>
    intro R hK hq hn hlt hkp
    obtain ⟨hk2, hk3, hov⟩ := hK
    have hR1 : R 1 = r := (hkp 1 (by decide) (by decide) (by decide) (by decide)).trans hr
    have hpow : (2 : Nat) ^ (j + 1) = 2 * 2 ^ j := by rw [Nat.pow_succ]; omega
    have h3 : (R 13 >>> 1).toNat = 2 ^ j := by rw [shr1_toNat', hk3, hpow]; omega
    have h2 : (R 12 >>> 1).toNat = d.toNat * 2 ^ j := by
      rw [shr1_toNat', hk2, hpow]; rw [Nat.mul_left_comm]; omega
    have h3nz : R 13 >>> 1 ≠ 0#64 := fun h0 => by
      have := congrArg BitVec.toNat h0; rw [h3] at this; simp at this
    have hK' : Vsa.Sim.DivK d (R 12 >>> 1) (R 13 >>> 1) j :=
      ⟨h2, h3, by rw [hpow] at hov; omega⟩
    refine it_800046d8 hlive ?_ ?_
    all_goals (intro hc; ix_run hlive at 0x800046d8)
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
    case refine_1.hT hz =>
      refine ih _ ?_ ?_ ?_ ?_ ?_
      · simpa [upd_apply] using hK'
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        exact Vsa.Sim.mod_drop_pow _ _ hq
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hn
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h2]
        have e1 : (R 12).toNat = 2 * (d.toNat * 2 ^ j) := by rw [hk2, hpow, Nat.mul_left_comm]
        omega
      · intro z h10 h11 h12 h13
        simp only [upd_apply, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13
    case refine_2.hT hz =>
      have hsub : (R 11 - R 12).toNat = (R 11).toNat - (R 12).toNat :=
        BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
      have hor : (R 10 ||| R 13).toNat = (R 10).toNat + 2 ^ (j + 1) :=
        Vsa.Sim.or_a3_toNat (R 10) (R 13) (j + 1) hk3 hq
      refine ih _ ?_ ?_ ?_ ?_ ?_
      · simpa [upd_apply] using hK'
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hor]
        exact Vsa.Sim.mod_add_pow _ _ hq
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hor, hsub, hn, hk2]
        rw [Nat.mul_add]; omega
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h2, hsub]
        have e1 : (R 12).toNat = 2 * (d.toNat * 2 ^ j) := by rw [hk2, hpow, Nat.mul_left_comm]
        omega
      · intro z h10 h11 h12 h13
        simp only [upd_apply, h10, h11, h12, h13, ite_false]; exact hkp z h10 h11 h12 h13

theorem toNat_of_toInt_nonpos {a : BitVec 64} (h : a.toInt ≤ 0) (hne : a.toNat ≠ 0) : 2 ^ 63 ≤ a.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at h; split at h <;> omega

theorem toNat_of_toInt_pos {a : BitVec 64} (h : ¬ a.toInt ≤ 0) : a.toNat < 2 ^ 63 := by
  rw [BitVec.toInt_eq_toNat_cond] at h; split at h <;> omega

theorem shl1_toNat {a : BitVec 64} (h : a.toNat < 2 ^ 63) : (a <<< 1).toNat = 2 * a.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one]; omega

/-- **The normalize loop** (`0x800046c4`): the divisor doubles until it
reaches the dividend or its top bit; strong induction on `n - a2`. -/
theorem udiv_loop1 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (n d r : BitVec 64) (R0 : Nat → BitVec 64)
    (Mt : Mem) (hal : r.toNat % 4 = 0) (hr : R0 1 = r)
    (hk : ∀ R', (R' 10).toNat = n.toNat / d.toNat → (R' 11).toNat = n.toNat % d.toNat →
      DivKeep R' R0 → IW live Dt DA S Q r R' Mt) (hd0 : 0 < d.toNat) :
    ∀ m (R : Nat → BitVec 64), n.toNat - (R 12).toNat = m → R 11 = n →
      (∃ k, Vsa.Sim.DivK d (R 12) (R 13) k) → (R 12).toNat < n.toNat → DivKeep R R0 →
      IW live Dt DA S Q 0x800046c4#64 R Mt := by
  intro m
  refine Nat.strongRecOn m ?_
  intro m ih R hm h11 ⟨k, hk2, hk3, hov⟩ hlt hkp
  have hpk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have ha2 : d.toNat ≤ (R 12).toNat := by rw [hk2]; exact Nat.le_mul_of_pos_right _ (by omega)
  refine it_800046c4 hlive ?_ ?_
  all_goals (intro hc; ix_run hlive at 0x800046c4 0x800046d8)
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
  case refine_1 =>
    have htop := toNat_of_toInt_nonpos (by simpa using hc) (by omega)
    refine udiv_loop2 hlive n d r R0 Mt hal hr hk k _ ?_ ?_ ?_ ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact ⟨hk2, hk3, hov⟩
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h11]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h11]
      have := n.isLt; omega
    · intro z h10 h11' h12 h13
      simp only [upd_apply, h10, ite_false]; exact hkp z h10 h11' h12 h13
  case refine_2.hT hb =>
    have hsm := toNat_of_toInt_pos (by simpa using hc)
    have e2 := shl1_toNat hsm
    have h2k : 2 ^ k ≤ (R 12).toNat := by rw [hk2]; exact Nat.le_mul_of_pos_left _ hd0
    have e3 : (R 13 <<< 1).toNat = 2 * (R 13).toNat := shl1_toNat (by rw [hk3]; omega)
    refine ih _ ?_ _ rfl ?_ ⟨k + 1, ?_, ?_, ?_⟩ ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [← hm, e2]; omega
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h11
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [e2, hk2, Nat.pow_succ]
      rw [Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc, Nat.mul_comm 2 d.toNat, Nat.mul_assoc]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [e3, hk3, Nat.pow_succ]
      rw [Nat.mul_comm]
    · rw [Nat.pow_succ]; have := (R 12 <<< 1).isLt
      rw [e2, hk2] at this; rw [Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc, Nat.mul_comm d.toNat 2,
        Nat.mul_assoc]; omega
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [← h11]; exact hb
    · intro z h10 h11' h12 h13
      simp only [upd_apply, h12, h13, ite_false]; exact hkp z h10 h11' h12 h13
  case refine_2.hF hb =>
    have hsm := toNat_of_toInt_pos (by simpa using hc)
    have e2 := shl1_toNat hsm
    have h2k : 2 ^ k ≤ (R 12).toNat := by rw [hk2]; exact Nat.le_mul_of_pos_left _ hd0
    have e3 : (R 13 <<< 1).toNat = 2 * (R 13).toNat := shl1_toNat (by rw [hk3]; omega)
    refine udiv_loop2 hlive n d r R0 Mt hal hr hk (k + 1) _ ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [e2, hk2, Nat.pow_succ]
      rw [Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc, Nat.mul_comm 2 d.toNat, Nat.mul_assoc]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [e3, hk3, Nat.pow_succ]
      rw [Nat.mul_comm]
    · rw [Nat.pow_succ]; have := (R 12 <<< 1).isLt
      rw [e2, hk2] at this; rw [Nat.mul_comm (2 ^ k) 2, ← Nat.mul_assoc, Nat.mul_comm d.toNat 2,
        Nat.mul_assoc]; omega
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h11]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h11]
      rw [h11] at hb; omega
    · intro z h10 h11' h12 h13
      simp only [upd_apply, h10, h12, h13, ite_false]; exact hkp z h10 h11' h12 h13

/-- **`__hidden___udivdi3`** (`0x800046ac`) in continuation form: at the
return (`ret` to `r`), `a0 = n / d`, `a1 = n % d`, and every register but
`a0`–`a3` as at the entry. -/
theorem udiv_iw {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (n d r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (hd : d ≠ 0#64) (h10 : R 10 = n) (h11 : R 11 = d) (hr : R 1 = r)
    (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toNat = n.toNat / d.toNat → (R' 11).toNat = n.toNat % d.toNat →
      DivKeep R' R → IW live Dt DA S Q r R' Mt) :
    IW live Dt DA S Q 0x800046ac#64 R Mt := by
  have hd0 : 0 < d.toNat := by
    rcases Nat.eq_zero_or_pos d.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hd
    · exact h
  ix_run hlive using [h11] at 0x800046c4 0x800046d8
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
  case hF.hT hb =>
    refine udiv_loop2 hlive n d r R Mt hal hr hk 0 _ ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp; exact d.isLt
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h10]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h10] at hb ⊢; omega
    · intro z h10' h11' h12 h13
      simp only [upd_apply, h10', h11', h12, h13, ite_false]
  case hF.hF hb =>
    refine udiv_loop1 hlive n d r R Mt hal hr hk hd0 _ _ rfl ?_ ⟨0, ?_, ?_, ?_⟩ ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp; exact d.isLt
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h10] at hb; omega
    · intro z h10' h11' h12 h13
      simp only [upd_apply, h10', h11', h12, h13, ite_false]

/-- A linking `jal` inside a symbolic run (a call the run follows into). -/
theorem iw_jal {live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem} (i : Nat) (code : List (BitVec 8)) (tgt : BitVec 64)
    (hexec : JalExec (vsaModel live) i code tgt)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText) (hpc : pc = BitVec.ofNat 64 i)
    (hk : IW live Dt DA S Q tgt (upd R 1 (BitVec.ofNat 64 (i + 4))) Mt) :
    IW live Dt DA S Q pc R Mt :=
  swp_jal i code tgt hexec (fun p hp => List.mem_append_left _ (hcode p hp)) (by decide) (by decide)
    hpc hk

theorem toNat_lt_of_toInt_nonneg {x : BitVec 64} (h : 0 ≤ x.toInt) : x.toNat < 2 ^ 63 := by
  rw [BitVec.toInt_eq_toNat_cond] at h; split at h <;> omega
theorem toNat_ge_of_toInt_neg {x : BitVec 64} (h : x.toInt < 0) : 2 ^ 63 ≤ x.toNat := by
  rw [BitVec.toInt_eq_toNat_cond] at h; split at h <;> omega

/-- The wrapped quotient from an exact one. -/
theorem wrap_of_eq' {q : BitVec 64} {z : Int} (h : q.toInt = z) : q.toInt = Vsa.While.wrap64 z := by
  rw [← h, Vsa.While.wrap64_toInt]

theorem sdiv_nn (x y : BitVec 64) (hx : 0 ≤ x.toInt) (hy : 0 < y.toInt) :
    (x / y).toInt = Vsa.While.wrap64 (x.toInt.tdiv y.toInt) := by
  have hA := Vsa.Sim.mag_notop x (toNat_lt_of_toInt_nonneg hx)
  have hB := Vsa.Sim.mag_notop y (toNat_lt_of_toInt_nonneg (by omega))
  exact wrap_of_eq' (Vsa.Sim.res_div_same x y x y hA hB (by omega) (by omega)
    (Vsa.Sim.udiv_lt_of_not_overflow x y x y hA hB (by omega) (by omega) (by omega)))

theorem sdiv_mn (x y : BitVec 64) (hx : x.toInt < 0) (hy : 0 < y.toInt) :
    (0#64 - (0#64 - x) / y).toInt = Vsa.While.wrap64 (x.toInt.tdiv y.toInt) := by
  have hA := Vsa.Sim.mag_neg_top x (toNat_ge_of_toInt_neg hx)
  have hB := Vsa.Sim.mag_notop y (toNat_lt_of_toInt_nonneg (by omega))
  exact wrap_of_eq' (Vsa.Sim.res_div_mixed x y (0#64 - x) y hA hB (by omega) (by omega))

theorem sdiv_nm (x y : BitVec 64) (hx : 0 ≤ x.toInt) (hy : y.toInt < 0) :
    (0#64 - x / (0#64 - y)).toInt = Vsa.While.wrap64 (x.toInt.tdiv y.toInt) := by
  have hA := Vsa.Sim.mag_notop x (toNat_lt_of_toInt_nonneg hx)
  have hB := Vsa.Sim.mag_neg_top y (toNat_ge_of_toInt_neg hy)
  exact wrap_of_eq' (Vsa.Sim.res_div_mixed x y x (0#64 - y) hA hB (by omega) (by omega))

theorem sdiv_mm (x y : BitVec 64) (hx : x.toInt < 0) (hy : y.toInt < 0) :
    ((0#64 - x) / (0#64 - y)).toInt = Vsa.While.wrap64 (x.toInt.tdiv y.toInt) := by
  have hA := Vsa.Sim.mag_neg_top x (toNat_ge_of_toInt_neg hx)
  have hB := Vsa.Sim.mag_neg_top y (toNat_ge_of_toInt_neg hy)
  by_cases hov : x.toInt = -2^63 ∧ y.toInt = -1
  · obtain ⟨h1, h2⟩ := hov
    have ex : x = 0x8000000000000000#64 := BitVec.eq_of_toInt_eq (by rw [h1]; decide)
    have ey : y = 0xffffffffffffffff#64 := BitVec.eq_of_toInt_eq (by rw [h2]; decide)
    rw [h1, h2, Vsa.While.wrap64_tdiv_min, ex, ey]; decide
  · exact wrap_of_eq' (Vsa.Sim.res_div_same x y (0#64 - x) (0#64 - y) hA hB (by omega) (by omega)
      (Vsa.Sim.udiv_lt_of_not_overflow x y _ _ hA hB (by omega) (by omega) hov))

/-- A remainder is in range: `Vsa.While.wrap64` does nothing to it. -/
theorem smod_pos (x y B : BitVec 64) (hx : 0 ≤ x.toInt) (hB : B.toNat = y.toInt.natAbs) (hy : y.toInt ≠ 0) :
    (x % B).toInt = Vsa.While.wrap64 (x.toInt.tmod y.toInt) :=
  wrap_of_eq' (Vsa.Sim.res_pos x y x B (Vsa.Sim.mag_notop x (toNat_lt_of_toInt_nonneg hx)) hB hx hy)

theorem smod_neg (x y B : BitVec 64) (hx : x.toInt < 0) (hB : B.toNat = y.toInt.natAbs) (hy : y.toInt ≠ 0) :
    (0#64 - (0#64 - x) % B).toInt = Vsa.While.wrap64 (x.toInt.tmod y.toInt) :=
  wrap_of_eq' (Vsa.Sim.res_neg x y (0#64 - x) B (Vsa.Sim.mag_neg_top x (toNat_ge_of_toInt_neg hx)) hB hx hy)

/-- Registers `__divdi3`/`__moddi3` keep: all but `ra`, `t0`, `a0`–`a3`. -/
abbrev SDivKeep (R R0 : Nat → BitVec 64) : Prop :=
  ∀ z, z ≠ 1 → z ≠ 5 → z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → R z = R0 z

theorem udiv_word {n d q : BitVec 64} (h : q.toNat = n.toNat / d.toNat) : q = n / d :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_udiv])

theorem umod_word {n d q : BitVec 64} (h : q.toNat = n.toNat % d.toNat) : q = n % d :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_umod])

/-- **`__divdi3`** (`0x800046a4`) in continuation form: the wrapped quotient
(`INT64_MIN / -1` included) in `a0` at the return to `r`. -/
theorem divdi3_iw {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (x y r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (hy : y ≠ 0#64) (h10 : R 10 = x) (h11 : R 11 = y) (hr : R 1 = r)
    (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toInt = Vsa.While.wrap64 (x.toInt.tdiv y.toInt) → SDivKeep R' R →
      IW live Dt DA S Q r R' Mt) :
    IW live Dt DA S Q 0x800046a4#64 R Mt := by
  have hy0 : y.toInt ≠ 0 := fun h => hy (BitVec.eq_of_toInt_eq (by simpa using h))
  ix_run hlive using [h10, h11] at 0x800046ac
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
  case hT.hT hx hyp =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x8000471c _ _ (jalx_8000471c live (fun p hp => hlive _ (interp_code_8000471c p hp)))
      interp_code_8000471c rfl ?_
    refine udiv_iw hlive (0#64 - x) y 0x80004720#64 _ Mt hy ?_ ?_ ?_ (by decide) (fun R' hq _ hkp => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h11
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    ix_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [udiv_word hq]; exact sdiv_mn x y (by simpa using hx) (by simpa using hyp)
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h10', ite_false]
  case hT.hF hx hyp =>
    rw [h10] at hx; rw [h11] at hyp
    refine udiv_iw hlive (0#64 - x) (0#64 - y) r _ Mt ?_ ?_ ?_ ?_ hal (fun R' hq _ hkp => ?_)
    · intro h0; apply hy; have := congrArg (0#64 - ·) h0; simpa using this
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    · refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · rw [udiv_word hq]
        exact sdiv_mm x y (by simpa using hx) (by have := hy0; simp at hyp; omega)
      · rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h10', h11', ite_false]
  case hF.hT hx hyp =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x8000471c _ _ (jalx_8000471c live (fun p hp => hlive _ (interp_code_8000471c p hp)))
      interp_code_8000471c rfl ?_
    refine udiv_iw hlive x (0#64 - y) 0x80004720#64 _ Mt ?_ ?_ ?_ ?_ (by decide) (fun R' hq _ hkp => ?_)
    · intro h0; apply hy; have := congrArg (0#64 - ·) h0; simpa using this
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    ix_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [udiv_word hq]; exact sdiv_nm x y (by simpa using hx) (by simpa using hyp)
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h11', ite_false]
  case hF.hF hx hyp =>
    rw [h10] at hx; rw [h11] at hyp
    refine udiv_iw hlive x y r _ Mt hy h10 h11 hr hal (fun R' hq _ hkp => ?_)
    refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => hkp z h10' h11' h12 h13)
    rw [udiv_word hq]
    exact sdiv_nn x y (by simpa using hx) (by have := hy0; simp at hyp; omega)

/-- **`__moddi3`** (`0x80004728`) in continuation form: the remainder with
the dividend's sign (`Int.tmod`) in `a0` at the return to `r`. -/
theorem moddi3_iw {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (x y r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (hy : y ≠ 0#64) (h10 : R 10 = x) (h11 : R 11 = y) (hr : R 1 = r)
    (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toInt = Vsa.While.wrap64 (x.toInt.tmod y.toInt) → SDivKeep R' R →
      IW live Dt DA S Q r R' Mt) :
    IW live Dt DA S Q 0x80004728#64 R Mt := by
  have hy0 : y.toInt ≠ 0 := fun h => hy (BitVec.eq_of_toInt_eq (by simpa using h))
  ix_run hlive using [h10, h11] at 0x800046ac
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
  case hT.hT hyp hx =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x80004734 _ _ (jalx_80004734 live (fun p hp => hlive _ (interp_code_80004734 p hp)))
      interp_code_80004734 rfl ?_
    refine udiv_iw hlive (x) (0#64 - y) 0x80004738#64 _ Mt ?_ ?_ ?_ ?_ (by decide) (fun R' _ hm hkp => ?_)
    · intro h0; apply hy; have := congrArg (0#64 - ·) h0; simpa using this
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    ix_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [umod_word hm]
        exact smod_pos x y (0#64 - y) (by simpa using hx) (Vsa.Sim.mag_neg_top y (toNat_ge_of_toInt_neg (by simpa using hyp))) hy0
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h10', h11', ite_false]
  case hT.hF hyp hx =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x8000474c _ _ (jalx_8000474c live (fun p hp => hlive _ (interp_code_8000474c p hp)))
      interp_code_8000474c rfl ?_
    refine udiv_iw hlive (0#64 - x) (0#64 - y) 0x80004750#64 _ Mt ?_ ?_ ?_ ?_ (by decide) (fun R' _ hm hkp => ?_)
    · intro h0; apply hy; have := congrArg (0#64 - ·) h0; simpa using this
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    ix_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [umod_word hm]
        exact smod_neg x y (0#64 - y) (by simpa using hx) (Vsa.Sim.mag_neg_top y (toNat_ge_of_toInt_neg (by simpa using hyp))) hy0
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h10', h11', ite_false]
  case hF.hT hyp hx =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x8000474c _ _ (jalx_8000474c live (fun p hp => hlive _ (interp_code_8000474c p hp)))
      interp_code_8000474c rfl ?_
    refine udiv_iw hlive (0#64 - x) (y) 0x80004750#64 _ Mt ?_ ?_ ?_ ?_ (by decide) (fun R' _ hm hkp => ?_)
    · exact hy
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h11
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    ix_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [umod_word hm]
        exact smod_neg x y (y) (by simpa using hx) (Vsa.Sim.mag_notop y (toNat_lt_of_toInt_nonneg (by simpa using hyp))) hy0
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h10', h11', ite_false]
  case hF.hF hyp hx =>
    rw [h10] at hx; rw [h11] at hyp
    refine iw_jal 0x80004734 _ _ (jalx_80004734 live (fun p hp => hlive _ (interp_code_80004734 p hp)))
      interp_code_80004734 rfl ?_
    refine udiv_iw hlive (x) (y) 0x80004738#64 _ Mt ?_ ?_ ?_ ?_ (by decide) (fun R' _ hm hkp => ?_)
    · exact hy
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h11
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    have h5 : R' 5 = r := by
      rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
    ix_run hlive at 0x0
    all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · rw [h5]; exact hal
    · rw [h5]; refine hk _ ?_ (fun z h1 h5' h10' h11' h12 h13 => ?_)
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [umod_word hm]
        exact smod_pos x y (y) (by simpa using hx) (Vsa.Sim.mag_notop y (toNat_lt_of_toInt_nonneg (by simpa using hyp))) hy0
      · simp only [upd_apply, h10', ite_false]
        rw [hkp z h10' h11' h12 h13]; simp only [upd_apply, h1, h5', h10', h11', ite_false]


end VsaIris.Interp
