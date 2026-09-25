import VsaIris.Vsa.SnpTac
import VsaIris.Interp.ProofArith

/-!
# `__hidden___udivdi3` in a `snprintf` run

`_svfprintf_r`'s decimal loop calls `__umoddi3`/`__hidden___udivdi3` by ten.
Lane E2 proved the division in the interpreter's run (`ProofArith.udiv_iw`);
a symbolic run is one table's instance of `SWP`, so the proof is replayed
here over `NW` with the `snprintf` table's step lemmas (`nt_<pc>`, `nx_run`).
The arithmetic lemmas are E2's (`div_of_inv`, `DivKeep`, VSA's `DivK`).
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr

/-- **The divide loop** (`0x800046d8`, restoring long division), by induction
on the bit position `j`, in continuation form: at the return the quotient
and remainder are in `a0`/`a1`. -/
theorem udiv_loop2N {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (n d r : BitVec 64) (R0 : Nat → BitVec 64)
    (Mt : Mem) (hal : r.toNat % 4 = 0) (hr : R0 1 = r)
    (hk : ∀ R', (R' 10).toNat = n.toNat / d.toNat → (R' 11).toNat = n.toNat % d.toNat →
      DivKeep R' R0 → NW live Dt DA S Q r R' Mt) :
    ∀ j (R : Nat → BitVec 64), Vsa.Sim.DivK d (R 12) (R 13) j → (R 10).toNat % 2 ^ (j + 1) = 0 →
      n.toNat = d.toNat * (R 10).toNat + (R 11).toNat → (R 11).toNat < 2 * (R 12).toNat →
      DivKeep R R0 → NW live Dt DA S Q 0x800046d8#64 R Mt := by
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
    refine nt_800046d8 hlive ?_ ?_
    all_goals (intro hc; nx_run hlive at 0x800046d8)
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
    refine nt_800046d8 hlive ?_ ?_
    all_goals (intro hc; nx_run hlive at 0x800046d8)
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

/-- **The normalize loop** (`0x800046c4`): the divisor doubles until it
reaches the dividend or its top bit; strong induction on `n - a2`. -/
theorem udiv_loop1N {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (n d r : BitVec 64) (R0 : Nat → BitVec 64)
    (Mt : Mem) (hal : r.toNat % 4 = 0) (hr : R0 1 = r)
    (hk : ∀ R', (R' 10).toNat = n.toNat / d.toNat → (R' 11).toNat = n.toNat % d.toNat →
      DivKeep R' R0 → NW live Dt DA S Q r R' Mt) (hd0 : 0 < d.toNat) :
    ∀ m (R : Nat → BitVec 64), n.toNat - (R 12).toNat = m → R 11 = n →
      (∃ k, Vsa.Sim.DivK d (R 12) (R 13) k) → (R 12).toNat < n.toNat → DivKeep R R0 →
      NW live Dt DA S Q 0x800046c4#64 R Mt := by
  intro m
  refine Nat.strongRecOn m ?_
  intro m ih R hm h11 ⟨k, hk2, hk3, hov⟩ hlt hkp
  have hpk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have ha2 : d.toNat ≤ (R 12).toNat := by rw [hk2]; exact Nat.le_mul_of_pos_right _ (by omega)
  refine nt_800046c4 hlive ?_ ?_
  all_goals (intro hc; nx_run hlive at 0x800046c4 0x800046d8)
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
  case refine_1 =>
    have htop := toNat_of_toInt_nonpos (by simpa using hc) (by omega)
    refine udiv_loop2N hlive n d r R0 Mt hal hr hk k _ ?_ ?_ ?_ ?_ ?_
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
    refine udiv_loop2N hlive n d r R0 Mt hal hr hk (k + 1) _ ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
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
theorem udiv_nw {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (n d r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (hd : d ≠ 0#64) (h10 : R 10 = n) (h11 : R 11 = d) (hr : R 1 = r)
    (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toNat = n.toNat / d.toNat → (R' 11).toNat = n.toNat % d.toNat →
      DivKeep R' R → NW live Dt DA S Q r R' Mt) :
    NW live Dt DA S Q 0x800046ac#64 R Mt := by
  have hd0 : 0 < d.toNat := by
    rcases Nat.eq_zero_or_pos d.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) hd
    · exact h
  nx_run hlive using [h11] at 0x800046c4 0x800046d8
  all_goals (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *)
  case hF.hT hb =>
    refine udiv_loop2N hlive n d r R Mt hal hr hk 0 _ ⟨?_, ?_, ?_⟩ ?_ ?_ ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp; exact d.isLt
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h10]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h10] at hb ⊢; omega
    · intro z h10' h11' h12 h13
      simp only [upd_apply, h10', h11', h12, h13, ite_false]
  case hF.hF hb =>
    refine udiv_loop1N hlive n d r R Mt hal hr hk hd0 _ _ rfl ?_ ⟨0, ?_, ?_, ?_⟩ ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; simp
    · simp; exact d.isLt
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [h10] at hb; omega
    · intro z h10' h11' h12 h13
      simp only [upd_apply, h10', h11', h12, h13, ite_false]

/-- **`__umoddi3`** (`0x800046f4`): `udivdi3` through `t0`, then `a0 = a1`;
at the return (`jr t0` to `r`) `a0 = n % d`, every register but `a0`–`a3`,
`t0` and `ra` as at the entry. -/
theorem umod_nw {live : Nat → Prop} (hlive : ∀ p ∈ snpText, live p.1)
    {Dt : Mem} {DA : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} (n d r : BitVec 64) (R : Nat → BitVec 64)
    (Mt : Mem) (hd : d ≠ 0#64) (h10 : R 10 = n) (h11 : R 11 = d) (hr : R 1 = r)
    (hal : r.toNat % 4 = 0)
    (hk : ∀ R', (R' 10).toNat = n.toNat % d.toNat →
      (∀ z, z ≠ 1 → z ≠ 5 → z ≠ 10 → z ≠ 11 → z ≠ 12 → z ≠ 13 → R' z = R z) →
      NW live Dt DA S Q r R' Mt) :
    NW live Dt DA S Q 0x800046f4#64 R Mt := by
  nx_run hlive using [h10, h11] at 0x800046ac
  refine udiv_nw hlive n d 0x800046fc#64 _ Mt hd ?_ ?_ ?_ (by decide) fun R' hq hm hkp => ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h11
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have h5 : R' 5 = r := by
    rw [hkp 5 (by decide) (by decide) (by decide) (by decide)]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hr
  nx_run hlive using [h5]
  refine hk _ ?_ fun z h1 h5' h10' h11' h12 h13 => ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hm
  · simp only [upd_apply, h10', ite_false]
    rw [hkp z h10' h11' h12 h13]
    simp only [upd_apply, h1, h5', ite_false]

end VsaIris.Interp

