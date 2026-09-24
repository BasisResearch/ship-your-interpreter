import VsaIris.Vsa.ReallocTop

/-!
# `_realloc_r` into a free predecessor

A free chunk `P` before the old one is unlinked and absorbs it
(`PHeapAt.coalPrev`); the payload moves down to `P + 16` (a forward copy:
the destination lies below the source) and the block restarts there. With
the successor free too it is absorbed as well; with the top after it the
merged chunk grows into the top. The copies are the unrolled words of
`mal_inline`'s kind, at each path's own code, or `memmove_fwd`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section Copy

variable {live : Nat → Prop} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- The registers the predecessor copies keep: `sp`, `s1-s3`, `t1` (the
predecessor), `a3`, `a5`, `a6`, `a7`. -/
structure PVKeep (R R' : Nat → BitVec 64) : Prop where
  sp : R' 2 = R 2
  t1 : R' 6 = R 6
  s1 : R' 9 = R 9
  a3 : R' 13 = R 13
  a5 : R' 15 = R 15
  a6 : R' 16 = R 16
  a7 : R' 17 = R 17
  s2 : R' 18 = R 18
  s3 : R' 19 = R 19

theorem PVKeep.refl (R : Nat → BitVec 64) : PVKeep R R :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `PVKeep` through writes to other registers. -/
macro "pv_keep" h:term : tactic => `(tactic| (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;>
  first | exact ($h).sp | exact ($h).t1 | exact ($h).s1 | exact ($h).a3 | exact ($h).a5 |
    exact ($h).a6 | exact ($h).a7 | exact ($h).s2 | exact ($h).s3))

theorem PVKeep.upd {R R' : Nat → BitVec 64} (K : PVKeep R R') {k : Nat} (v : BitVec 64)
    (h2 : k ≠ 2) (h6 : k ≠ 6) (h9 : k ≠ 9) (h13 : k ≠ 13) (h15 : k ≠ 15)
    (h16 : k ≠ 16) (h17 : k ≠ 17) (h18 : k ≠ 18) (h19 : k ≠ 19) : PVKeep R (upd R' k v) :=
  ⟨by rw [upd_other _ _ (Ne.symm h2)]; exact K.sp, by rw [upd_other _ _ (Ne.symm h6)]; exact K.t1,
    by rw [upd_other _ _ (Ne.symm h9)]; exact K.s1, by rw [upd_other _ _ (Ne.symm h13)]; exact K.a3,
    by rw [upd_other _ _ (Ne.symm h15)]; exact K.a5, by rw [upd_other _ _ (Ne.symm h16)]; exact K.a6,
    by rw [upd_other _ _ (Ne.symm h17)]; exact K.a7, by rw [upd_other _ _ (Ne.symm h18)]; exact K.s2,
    by rw [upd_other _ _ (Ne.symm h19)]; exact K.s3⟩

/-- The three-word tail of the predecessor copy (`0x80005630`): words
`j … j+2` from `s0` to `a4`. -/
theorem pvA_tail3 {M0 : Mem} {d s L : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    {R0 R : Nat → BitVec 64} {j : Nat} (h8 : (R 8).toNat = s + 8 * j) (h14 : (R 14).toNat = d + 8 * j)
    (hj : 8 * j + 24 ≤ L) (K : PVKeep R0 R)
    (hk : ∀ R', PVKeep R0 R' → AW live S Q 0x80005648#64 R' (copyW M0 d s (j + 3))) :
    AW live S Q 0x80005630#64 R (copyW M0 d s j) := by
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
  have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * j) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * j) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 8) (rD := 14) (by decide) (st_80005630 hlive) (st_80005634 hlive)
    (by rw [n0, addr_add h8 0 (by omega)]; omega) (by rw [n0, addr_add h14 0 (by omega)]; omega)
    l1 l2 s1 s2 ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * (j + 1)) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * (j + 1)) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 8) (rD := 14) (by decide) (st_80005638 hlive) (st_8000563c hlive)
    (by rw [upd_other _ _ (by decide), n8, addr_add h8 8 (by omega)]; omega)
    (by rw [upd_other _ _ (by decide), n8, addr_add h14 8 (by omega)]; omega) l1 l2 s1 s2 ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * (j + 2)) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * (j + 2)) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 8) (rD := 14) (by decide) (st_80005640 hlive) (st_80005644 hlive)
    (by rw [upd_other _ _ (by decide), upd_other _ _ (by decide), n16, addr_add h8 16 (by omega)]; omega)
    (by rw [upd_other _ _ (by decide), upd_other _ _ (by decide), n16, addr_add h14 16 (by omega)]; omega)
    l1 l2 s1 s2 ?_
  exact hk _ (by pv_keep K)

/-- The first predecessor path's inline copy (`0x80005604`, a payload of 24,
40, 56 or 72 bytes, from `s0` to `t1 + 16`). -/
theorem pvA_inline {M0 : Mem} {d s L P : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    (hL : L = 24 ∨ L = 40 ∨ L = 56 ∨ L = 72) (hP : P + 16 = d)
    {R : Nat → BitVec 64} (h8 : (R 8).toNat = s) (h6 : (R 6).toNat = P) (h13 : (R 13).toNat = d)
    (h12 : (R 12).toNat = L) (h10 : (R 10).toNat = 72)
    (hk : ∀ R', PVKeep R R' → AW live S Q 0x80005648#64 R' (copyW M0 d s (L / 8))) :
    AW live S Q 0x80005604#64 R (copyW M0 d s 0) := by
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  have e : ∀ (x : BitVec 64) (a c : Nat), x.toNat = a → a + c < 2 ^ 64 →
      (x + BitVec.ofNat 64 c).toNat = a + c := fun x a c hx hc => addr_add hx c hc
  have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
  have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have n24 : (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 := rfl
  have n32 : (sign_extend (m := 64) (0x020#12) : BitVec 64) = BitVec.ofNat 64 32 := rfl
  have n40 : (sign_extend (m := 64) (0x028#12) : BitVec 64) = BitVec.ofNat 64 40 := rfl
  have n48 : (sign_extend (m := 64) (0x030#12) : BitVec 64) = BitVec.ofNat 64 48 := rfl
  have n56 : (sign_extend (m := 64) (0x038#12) : BitVec 64) = BitVec.ofNat 64 56 := rfl
  have n64 : (sign_extend (m := 64) (0x040#12) : BitVec 64) = BitVec.ofNat 64 64 := rfl
  have nm8 : (sign_extend (m := 64) (0xff8#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 8) := rfl
  -- the tail from word `j`
  have tail : ∀ j (R' : Nat → BitVec 64), j + 3 = L / 8 → (R' 8).toNat = s + 8 * j →
      (R' 14).toNat = d + 8 * j → PVKeep R R' → AW live S Q 0x80005630#64 R' (copyW M0 d s j) :=
    fun j R' hj g8 g14 K => pvA_tail3 A hlive g8 g14 (by omega) K fun R'' K' => by rw [hj]; exact hk R'' K'
  -- a word from `s0 + 8 j` to `t1 + 16 + 8 j`, while `s0 = s`
  have pair : ∀ (j : Nat) {pcL pcS pcN : BitVec 64} {offL offS : BitVec 12} (rT : Nat)
      (R1 : Nat → BitVec 64), rT ≠ 2 → rT ≠ 6 → rT ≠ 8 → rT ≠ 9 → rT ≠ 13 → rT ≠ 15 → rT ≠ 16 →
      rT ≠ 17 → rT ≠ 18 → rT ≠ 19 →
      (sign_extend (m := 64) offL : BitVec 64) = BitVec.ofNat 64 (8 * j) →
      (sign_extend (m := 64) offS : BitVec 64) = BitVec.ofNat 64 (16 + 8 * j) → 8 * j + 8 ≤ L →
      (∀ {R : Nat → BitVec 64} {Mt : Mem},
        LdOK ((R 8) + sign_extend (m := 64) offL).toNat 8 →
        (∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) offL).toNat 8, S b) →
        AW live S Q pcS (upd R rT (ldv .ld Mt ((R 8) + sign_extend (m := 64) offL).toNat)) Mt →
        AW live S Q pcL R Mt) →
      (∀ {R : Nat → BitVec 64} {Mt : Mem},
        StOK ((R 6) + sign_extend (m := 64) offS).toNat 8 →
        (∀ b ∈ accAddrs ((R 6) + sign_extend (m := 64) offS).toNat 8, S b) →
        AW live S Q pcN R (writeLog Mt [(((R 6) + sign_extend (m := 64) offS).toNat, 8, (R rT))]) →
        AW live S Q pcS R Mt) →
      PVKeep R R1 → (R1 8).toNat = s →
      (∀ v, AW live S Q pcN (upd R1 rT v) (copyW M0 d s (j + 1))) →
      AW live S Q pcL R1 (copyW M0 d s j) := by
    intro j pcL pcS pcN offL offS rT R1 t2 t6 t8 t9 t13 t15 t16 t17 t18 t19 hL hS hj stL stS K g8 k
    obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * j) (by omega) (by omega)
    obtain ⟨s1, s2⟩ := A.st (a := d + 8 * j) (by omega) (by omega) (by omega)
    exact cp_pair (rT := rT) (rS := 8) (rD := 6) (Ne.symm t6) stL stS
      (by rw [hL, e _ _ _ g8 (by omega)]) (by rw [K.t1, hS, e _ _ _ h6 (by omega)]; omega)
      l1 l2 s1 s2 (k _)
  refine st_80005604 hlive ?_
  refine st_80005608 hlive ?_
  refine st_8000560c hlive (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x027#12) : BitVec 64).toNat = 39 from rfl] at hc
  · -- 24 bytes: the tail alone
    refine tail 0 _ (by omega) ?_ ?_ (by pv_keep (PVKeep.refl R)) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [h8]; rfl
    · rw [n0, e _ _ _ h13 (by omega)]
  -- 40, 56 or 72 bytes: word 0, with `li a4,55` before its store
  refine aw_forget (fun R0 => PVKeep R R0 ∧ (R0 8).toNat = s ∧ (R0 12).toNat = L ∧ (R0 10).toNat = 72)
    ⟨by pv_keep (PVKeep.refl R), by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h8,
      by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h12,
      by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h10⟩ fun R0 ⟨K0, g8, g12, g10⟩ => ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 0) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 0) (by omega) (by omega) (by omega)
  have e0 : (R0 8 + sign_extend (m := 64) (0x000#12)).toNat = s + 8 * 0 := by rw [n0, e _ _ _ g8 (by omega)]
  refine st_80005610 hlive (by rw [e0]; exact l1) (by rw [e0]; exact l2) ?_
  rw [e0]
  refine st_80005614 hlive ?_
  have f0 : ((upd (upd R0 11 (ldv .ld (copyW M0 d s 0) (s + 8 * 0))) 14
      (0#64 + sign_extend (m := 64) (0x037#12))) 6 + sign_extend (m := 64) (0x010#12)).toNat =
      d + 8 * 0 := by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K0.t1, n16, e _ _ _ h6 (by omega)]; omega
  refine st_80005618 hlive (by rw [f0]; exact s1) (by rw [f0]; exact s2) ?_
  rw [f0]
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [← copyW_succ]
  refine aw_forget (fun R1 => PVKeep R R1 ∧ (R1 8).toNat = s ∧ (R1 14).toNat = 55 ∧ (R1 12).toNat = L ∧
      (R1 10).toNat = 72) ⟨by pv_keep K0, by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact g8,
        by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; rfl,
        by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact g12,
        by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact g10⟩
    fun R1 ⟨K1, g8, g14, g12, g10⟩ => ?_
  -- word 1
  refine pair 1 (offL := 0x008#12) (offS := 0x018#12) 11 R1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n8 n24 (by omega)
    (st_8000561c hlive) (st_80005620 hlive) K1 g8 fun v => ?_
  refine st_80005624 hlive (fun hc' => ?_) (fun hc' => ?_) <;>
    rw [upd_other _ _ (by decide), upd_other _ _ (by decide), g14, g12] at hc'
  · -- 56 or 72 bytes: words 2 and 3
    have K2 := K1.upd v (k := 11) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    refine pair 2 (offL := 0x010#12) (offS := 0x020#12) 14 _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n16 n32 (by omega)
      (st_800057a8 hlive) (st_800057ac hlive) K2 (by rw [upd_other _ _ (by decide)]; exact g8) fun v2 => ?_
    have K3 := K2.upd v2 (k := 14) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    refine pair 3 (offL := 0x018#12) (offS := 0x028#12) 14 _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n24 n40 (by omega)
      (st_800057b0 hlive) (st_800057b4 hlive) K3
      (by rw [upd_other _ _ (by decide), upd_other _ _ (by decide)]; exact g8) fun v3 => ?_
    refine st_800057b8 hlive (fun hc'' => ?_) (fun hc'' => ?_)
    · -- 72 bytes: words 4 and 5, then the tail
      have hL72 : L = 72 := by
        have := congrArg BitVec.toNat hc''
        simp only [upd_apply, Nat.reduceEqDiff, ite_false] at this; rw [g12, g10] at this; exact this
      refine aw_forget (fun R2 => PVKeep R R2 ∧ (R2 8).toNat = s)
        ⟨by pv_keep K1, by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact g8⟩
        fun R2 ⟨K4, h8'⟩ => ?_
      obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 4) (by omega) (by omega)
      obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 4) (by omega) (by omega) (by omega)
      have e4 : (R2 8 + sign_extend (m := 64) (0x020#12)).toNat = s + 8 * 4 := by
        rw [n32, e _ _ _ h8' (by omega)]
      refine st_80005848 hlive (by rw [e4]; exact l1) (by rw [e4]; exact l2) ?_
      rw [e4]
      refine st_8000584c hlive ?_
      refine st_80005850 hlive ?_
      have f4 : ((upd (upd (upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 14
          ((upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 6 + sign_extend (m := 64) (0x040#12))) 8
          ((upd (upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 14
            ((upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 6 + sign_extend (m := 64) (0x040#12))) 8 +
            sign_extend (m := 64) (0x030#12))) 6 + sign_extend (m := 64) (0x030#12)).toNat = d + 8 * 4 := by
        simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K4.t1, n48, e _ _ _ h6 (by omega)]; omega
      refine st_80005854 hlive (by rw [f4]; exact s1) (by rw [f4]; exact s2) ?_
      rw [f4]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [← copyW_succ]
      obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 5) (by omega) (by omega)
      obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 5) (by omega) (by omega) (by omega)
      have g8' : (R2 8 + sign_extend (m := 64) (0x030#12)).toNat = s + 48 := by
        rw [n48, e _ _ _ h8' (by omega)]
      refine cp_pair (rT := 12) (rS := 8) (rD := 6) (by decide) (st_80005858 hlive) (st_8000585c hlive)
        ?_ ?_ l1 l2 s1 s2 ?_
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [nm8, addr_sub g8' 8 (by omega) (by omega)]; omega
      · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K4.t1, n56, e _ _ _ h6 (by omega)]; omega
      refine st_80005860 hlive ?_
      refine tail 6 _ (by omega) ?_ ?_ (by pv_keep K4) <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [g8']
      · rw [K4.t1, n64, e _ _ _ h6 (by omega)]; omega
    · -- 56 bytes: the tail from word 4
      have hL56 : L = 56 := by
        have : L ≠ 72 := fun h => hc'' (BitVec.eq_of_toNat_eq (by
          simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [g12, g10, h]))
        omega
      refine st_800057bc hlive ?_
      refine st_800057c0 hlive ?_
      refine st_800057c4 hlive ?_
      refine tail 4 _ (by omega) ?_ ?_ (by pv_keep K1) <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [n32, e _ _ _ g8 (by omega)]
      · rw [K1.t1, n48, e _ _ _ h6 (by omega)]; omega
  · -- 40 bytes: the tail from word 2
    refine st_80005628 hlive ?_
    refine st_8000562c hlive ?_
    refine tail 2 _ (by omega) ?_ ?_ (by pv_keep K1) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [n16, e _ _ _ g8 (by omega)]
    · rw [K1.t1, n32, e _ _ _ h6 (by omega)]; omega

end Copy

end VsaIris.VsaHeap
