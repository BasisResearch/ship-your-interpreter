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

/-- A bin node's link words lie outside every in-use chunk and the next
chunk's first word. -/
theorem node_off_inuse {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (h : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) {i x : Nat} (hi : i < numBins)
    (hx : x = binAt i ∨ ∃ cx ∈ chunks, cx.addr = x ∧ cx.inuse = false ∧ x ∈ bins i)
    {c : Chunk} (hc : c ∈ chunks) (hu : c.inuse = true) :
    ∀ a, c.addr ≤ a → a < c.addr + c.size + 8 → a < x + 16 ∨ x + 32 ≤ a := by
  intro a h1 h2
  have hcb := (h.walk.chunk_bounds c hc).1
  unfold heapStart at hcb
  rcases hx with rfl | ⟨cx, hcx, rfl, hf, _⟩
  · have := binAt_geo i hi; omega
  · rcases h.walk.chunk_sep cx hcx c hc with rfl | h3 | h3
    · rw [hu] at hf; cases hf
    all_goals have := (walk_sizes h.walk cx hcx).2; omega

/-- **Word copies over two memories** that agree on a set the source lies in
agree on it after the copy. -/
theorem copyW_agreeOn {m1 m2 : Mem} {d s : Nat} {Pr : Nat → Prop}
    (h : ∀ a, Pr a → m1[a]? = m2[a]?) :
    ∀ {k : Nat}, (∀ i, i < 8 * k → Pr (s + i)) →
      ∀ a, Pr a → (copyW m1 d s k)[a]? = (copyW m2 d s k)[a]?
  | 0, _, a, ha => h a ha
  | k + 1, hs, a, ha => by
    have IH := copyW_agreeOn (m1 := m1) (m2 := m2) (d := d) (s := s) h (k := k)
      (fun i hi => hs i (by omega))
    rw [copyW_succ, copyW_succ, ldv_congr (m1 := copyW m1 d s k) (m2 := copyW m2 d s k) fun j hj =>
      IH _ (by have := hs (8 * k + j) (by omega); rwa [show s + (8 * k + j) = s + 8 * k + j by omega] at this)]
    exact wl1_congr fun hout => IH a ha

/-- The virtual heap after the free predecessor `P` absorbed the old chunk
(`PHeapAt.coalPrev` over `W`): `P` unlinked, its header `ps + S' + 1`, the
old chunk's header the machine's `hdr0`. -/
abbrev coalW (W : Mem) (P ps S' hxv hdr0 predP succP : Nat) : Mem :=
  writeLog (writeLog (writeLog (writeLog (writeLog W
    [(predP + 16, 8, BitVec.ofNat 64 succP)]) [(succP + 24, 8, BitVec.ofNat 64 predP)])
    [(P + ps + 8, 8, BitVec.ofNat 64 (hxv ||| 1))]) [(P + 8, 8, BitVec.ofNat 64 (ps + S' + 1))])
    [(P + ps + 8, 8, BitVec.ofNat 64 hdr0)]

/-- The machine memory after unlinking the free predecessor `P` agrees with
the coalesced virtual heap `coalW` off `P`'s header and the header after the
merged chunk. -/
theorem pv_agreeW {C : MCtx} {Mt W : Mem} {P ps S' hxv hdr0 predP succP : Nat}
    (G : PvGeo C P ps S' predP succP) (hxM : read64 Mt (P + ps + 8) = some hdr0)
    (hag : ∀ a, ¬ (P + ps + 8 ≤ a ∧ a < P + ps + 16) →
      ¬ (P + ps + S' + 8 ≤ a ∧ a < P + ps + S' + 16) → Mt[a]? = W[a]?)
    {v1 v2 : BitVec 64} (h1 : v1.toNat = predP) (h2 : v2.toNat = succP) :
    ∀ w0, ¬ (P + 8 ≤ w0 ∧ w0 < P + 16) → ¬ (P + ps + S' + 8 ≤ w0 ∧ w0 < P + ps + S' + 16) →
      (writeLog (writeLog Mt [(succP + 24, 8, v1)]) [(predP + 16, 8, v2)])[w0]? =
      (coalW W P ps S' hxv hdr0 predP succP)[w0]? := by
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have hdlt := Vsa.Sim.read64_lt _ _ _ hxM
  intro w0 h1' h2'
  refine agree_of_words (P := fun x => ¬ (P + 8 ≤ x ∧ x < P + 16) ∧
      ¬ (P + ps + S' + 8 ≤ x ∧ x < P + ps + S' + 16))
    [succP + 24, predP + 16, P + ps + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 ⟨h1', h2'⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl | rfl
    · refine ⟨predP, ?_, ?_⟩
      · rw [rd_miss (by omega), read64_store_hit, h1]
      · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), read64_store_hit,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨succP, ?_, ?_⟩
      · rw [read64_store_hit, h2]
      · rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
          read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    · refine ⟨hdr0, ?_, ?_⟩
      · rw [rd_miss (by omega), rd_miss (by omega)]; exact hxM
      · rw [read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out]
    · exact hag x (by omega) (by omega)
    all_goals simp only [OutL, and_true]; omega

/-- The state the predecessor paths hand the tail: the machine memory `Mt`
before `P`'s unlink, a virtual memory `W` holding the heap with `P` free
before the old chunk of `S'` bytes (equal to `Mt` off that chunk's header and
the next one), and the copy length `L`. -/
structure PvIn (C : MCtx) (B : RB) (Mt W : Mem) (brkv : Nat) (cs₀ rest : List Chunk)
    (bins : Nat → List Nat) (P ps S' L hdr0 hxv hn nb i : Nat) (pre post : List Nat)
    (predP succP : Nat) : Prop where
  heap : PHeapAt W ((B.p, B.nOld) :: C.H) C.top0 brkv
    ((cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S', true⟩ :: rest) bins
  starts : Starts ((B.p, B.nOld) :: C.H)
  addr : P + ps + 16 = B.p
  pv : FPv W (cs₀ ++ [⟨P, ps, false⟩]) bins (P + ps) cs₀ P ps i pre post predP succP
  xW : read64 W (P + ps + 8) = some hxv
  xM : read64 Mt (P + ps + 8) = some hdr0
  nM : read64 Mt (P + ps + S' + 8) = some hn
  nW : read64 W (P + ps + S' + 8) = some (hn / 2 * 2 + 1)
  agree : ∀ a, ¬ (P + ps + 8 ≤ a ∧ a < P + ps + 16) →
    ¬ (P + ps + S' + 8 ≤ a ∧ a < P + ps + S' + 16) → Mt[a]? = W[a]?
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  disjD : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  data : ∀ k, k < B.nOld → Mt[B.p + k]? = some (B.old (B.p + k))
  grow : B.nOld < C.n.toNat
  nbok : NbOK C.n nb
  fit : nb ≤ ps + S'
  L8 : L % 8 = 0
  Lold : B.nOld ≤ L
  Lle : L + 8 ≤ S'

/-- **The tail after absorbing into the predecessor** (`0x80005414`): the
machine memory is `P`'s unlink and the payload's copy to `P + 16` (off
`_realloc_r`'s spill words); the virtual heap is `coalPrev`'s over `W`, with
the copied payload in a block at `P + 16`. -/
theorem pvG_rt {C : MCtx} {B : RB} (O : ROK C B) {Mt W : Mem} {brkv : Nat}
    {cs₀ rest : List Chunk} {bins : Nat → List Nat} {P ps S' L hdr0 hxv hn nb i : Nat}
    {pre post : List Nat} {predP succP : Nat}
    (I : PvIn C B Mt W brkv cs₀ rest bins P ps S' L hdr0 hxv hn nb i pre post predP succP)
    {R' : Nat → BitVec 64} {Mc : Mem} (F : RFrame C R' Mc)
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (P + ps + 16) (L / 8))[a]?)
    (h8 : (R' 8).toNat = P + 16) (h9 : R' 9 = reentV) (h12 : (R' 12).toNat = P)
    (h14 : (R' 14).toNat = ps + S') (h15 : (R' 15).toNat = nb) :
    AW C.live C.S C.Q 0x80005414#64 R' Mc := by
  have H0 := I.heap
  have HH := H0.heap.heap
  have PV := I.pv
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  have G : PvGeo C' P ps S' predP succP := PvGeo.of_heap (C := C') H0 PV
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hs16 := G.sz16; have hs32 := G.sz32
  have hxend : P + ps + S' ≤ C.top0 := G.xend; have htop : C.top0 + 16 ≤ 0x87800000 := G.top
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have hpphi : predP + 32 ≤ C.top0 := G.pphi; have hsphi : succP + 32 ≤ C.top0 := G.sphi
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have haddr := I.addr
  have hnb := I.nbok.eq
  have hnbv : C.n.toNat + 8 ≤ nb := by rw [hnb]; unfold physSize; omega
  have hL8 := I.L8; have hLo := I.Lold; have hLe := I.Lle; have hfit := I.fit
  -- the boundary after the old chunk is no bin node's link word
  have hXm : (⟨P + ps, S', true⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S', true⟩ :: rest := by
    simp
  have hbE : P + ps + S' = C.top0 ∨ ∃ c ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S', true⟩ :: rest,
      c.addr = P + ps + S' := by have := HH.end_bnd hXm; simpa using this
  have hpm : predP = binAt i ∨ predP ∈ bins i := by
    have := List.mem_of_getLast? PV.hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [PV.bin]; exact List.mem_append_left _ h1)
  have hsm : succP = binAt i ∨ succP ∈ bins i := by
    have := List.mem_of_head? PV.hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [PV.bin]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  obtain ⟨_, hpnode⟩ := HH.node PV.i0 PV.i1 hpm
  obtain ⟨_, hsnode⟩ := HH.node PV.i0 PV.i1 hsm
  have nE8 := HH.bnd_ne_node PV.i1 hpnode hbE 8 (by omega) (by omega)
  have nE16 := HH.bnd_ne_node PV.i1 hsnode hbE 16 (by omega) (by omega)
  -- the virtual heap: `P` absorbs the old chunk, a block over its payload, the copy, resized
  have Hd := H0.drop
  simp only [List.append_assoc, List.singleton_append] at Hd
  have hst := I.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have hnoX : ∀ e ∈ C.H, e.1 ≠ P + ps + 16 := fun e he heq =>
    hst.1 (List.mem_map.2 ⟨e, he, by rw [heq]; exact haddr⟩)
  obtain ⟨hP, hPr⟩ : ∃ hP, read64 W (P + 8) = some hP := by
    obtain ⟨hh, hhr, _, _⟩ := walk_header HH.walk ⟨P, ps, false⟩ (by simp)
    exact ⟨hh, hhr⟩
  have hPodd := PV.prev hP hPr
  have hPM : read64 Mt (P + 8) = some hP := by
    rw [read64_keep (m := W) fun k hk => I.agree _ (by omega) (by omega)]; exact hPr
  have Hc := Hd.coalPrev (cs₂ := rest) (b := S') hnoX PV.i0 PV.i1 PV.bin PV.hpred PV.hsucc I.xW
    (h' := ps + S' + 1) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      have := PV.prev h0 hr; unfold prevInuse; rw [show (ps + S' + 1) % 2 = 1 by omega, this])
    (BitVec.ofNat 64 hdr0)
  have hPm : (⟨P, ps + S', true⟩ : Chunk) ∈ cs₀ ++ ⟨P, ps + S', true⟩ :: rest := by simp
  have Ha := Hc.addBlock (q := P + 16) (n := ps + S' - 8) hPm rfl rfl (by simp only; omega)
  generalize hV : copyW (coalW W P ps S' hxv hdr0 predP succP) (P + 16) (P + ps + 16) (L / 8) = V
  have hLw : 8 * (L / 8) = L := by omega
  have HV : PHeapAt V ((P + 16, ps + S' - 8) :: C.H) C.top0 brkv (cs₀ ++ ⟨P, ps + S', true⟩ :: rest)
      (updBins bins i (pre ++ post)) := by
    refine Ha.transport_read fun a ha => ?_
    rw [← hV]
    refine (copyW_out ?_).symm
    rcases ha.1 with hg | ⟨_, _, h3⟩
    · have := allocGlobal_off_arena _ hg; unfold heapStart heapEnd at this; omega
    · have := h3 _ List.mem_cons_self; unfold InExt at this; simp only at this; omega
  have Hr := HV.reblock (c := ⟨P, ps + S', true⟩) hPm rfl rfl (n' := C.n.toNat) (by simp only; omega)
  -- the machine memory
  have hpl := Vsa.Sim.read64_lt _ _ _ PV.bk
  have hsl := Vsa.Sim.read64_lt _ _ _ PV.fd
  have hv1 : (BitVec.ofNat 64 predP).toNat = predP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hv2 : (BitVec.ofNat 64 succP).toNat = succP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
  generalize hM1 : writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
    [(predP + 16, 8, BitVec.ofNat 64 succP)] = M1 at hMc
  have hag1 : ∀ w, ¬ (P + 8 ≤ w ∧ w < P + 16) → ¬ (P + ps + S' + 8 ≤ w ∧ w < P + ps + S' + 16) →
      M1[w]? = (coalW W P ps S' hxv hdr0 predP succP)[w]? :=
    fun w h1 h2 => by rw [← hM1]; exact pv_agreeW G I.xM I.agree hv1 hv2 w h1 h2
  have hM1o : ∀ a, ¬ (succP + 24 ≤ a ∧ a < succP + 32) → ¬ (predP + 16 ≤ a ∧ a < predP + 24) →
      M1[a]? = Mt[a]? := fun a h1 h2 => by
    rw [← hM1, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  have hstk : ∀ a, vsaFoot C.H a → a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a := fun a ha => by
    have hlo := O.spA.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
    have := Classical.byContradiction fun hc : ¬ (a < C.s.toNat - allocHeadroom ∨ C.s.toNat ≤ a) =>
      I.disjD a (by omega) (by omega) ha
    unfold allocHeadroom at this; omega
  have HdX : PHeapAt W C.H C.top0 brkv ((cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S', true⟩ :: rest) bins :=
    H0.drop
  have hsrcF : ∀ k, k < S' - 8 → vsaFoot C.H (P + ps + 16 + k) := fun k hk =>
    HdX.payload_foot hXm hnoX _ (by simp only; omega) (by simp only; omega)
  have hpresM1 : ∀ a, vsaFoot C.H a → (M1[a]?).isSome := fun a ha => by
    rw [← hM1]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (I.pres a ha))
  have hMcF : ∀ a, vsaFoot C.H a →
      Mc[a]? = (copyW M1 (P + 16) (P + ps + 16) (L / 8))[a]? := fun a ha => hMc a (hstk a ha)
  have hcpy : ∀ a, ¬ (P + 8 ≤ a ∧ a < P + 16) → ¬ (P + ps + S' + 8 ≤ a ∧ a < P + ps + S' + 16) →
      (copyW M1 (P + 16) (P + ps + 16) (L / 8))[a]? = V[a]? := fun a h1 h2 => by
    rw [← hV]
    exact copyW_agreeOn (Pr := fun a => ¬ (P + 8 ≤ a ∧ a < P + 16) ∧
        ¬ (P + ps + S' + 8 ≤ a ∧ a < P + ps + S' + 16)) (fun a ha => hag1 a ha.1 ha.2)
      (fun i hi => ⟨by omega, by omega⟩) a ⟨h1, h2⟩
  -- the payload's bytes are no node word
  have hnd : ∀ a, P + ps ≤ a → a < P + ps + S' + 8 → M1[a]? = Mt[a]? := fun a h1 h2 =>
    hM1o a (by have := node_off_inuse HH PV.i1 hsnode hXm rfl a h1 h2; omega)
      (by have := node_off_inuse HH PV.i1 hpnode hXm rfl a h1 h2; omega)
  have hnh : ∀ k, k < 8 → vsaFoot C.H (P + ps + S' + 8 + k) := foot_header HdX.heap hbE
  clear hbE hpnode hsnode hpm hsm
  have hStarts : Starts ((P + 16, C.n.toNat) :: C.H) := by
    refine Starts.cons hst.2 fun e he heq => ?_
    have he' : e ∈ (B.p, B.nOld) :: C.H := List.mem_cons_of_mem _ he
    obtain ⟨c0, hc0, hu, hc0a, _⟩ := HH.exact e he' he'
    have := HH.chunk_eq hc0 (show (⟨P, ps, false⟩ : Chunk) ∈
      (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S', true⟩ :: rest by simp) (by simp only; omega)
    rw [this] at hu; cases hu
  have hPspan : ∀ a, P + 8 ≤ a → a < P + ps + S' + 8 → vsaFoot C.H a := fun a h1 h2 => by
    by_cases ha : a < P + ps + 16
    · exact foot_free_span HdX.heap (c := ⟨P, ps, false⟩) (by simp) rfl a h1 ha
    · exact hsrcF (a - (P + ps + 16)) (by omega) |> fun h => by
        rwa [show P + ps + 16 + (a - (P + ps + 16)) = a by omega] at h
  have hMcV : ∀ a, vsaFoot C.H a → ¬ (P + 8 ≤ a ∧ a < P + 16) →
      ¬ (P + ps + S' + 8 ≤ a ∧ a < P + ps + S' + 16) → Mc[a]? = V[a]? :=
    fun a h1 h2 h3 => (hMcF a h1).trans (hcpy a h2 h3)
  have hVn : read64 V (P + ps + S' + 8) = some (hn / 2 * 2 + 1) := by
    rw [← hV, read64_keep (m := coalW W P ps S' hxv hdr0 predP succP) fun k hk => copyW_out (by omega)]
    rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega)]
    exact I.nW
  have hMn : read64 Mc (P + ps + S' + 8) = some hn := by
    rw [read64_keep (m := Mt) fun k hk => by
      rw [hMcF _ (hnh k hk), copyW_out (by omega), hM1o _ (by omega) (by omega)]]
    exact I.nM
  refine realloc_tail O (V := V) (X := P) (S := ps + S') (nb := nb) (cs₁ := cs₀) (cs₂ := rest)
    ⟨F, Hr, hStarts, by omega, I.nbok, I.fit, ⟨hP, ?_, ?_⟩, ⟨hn, ?_, ?_⟩, fun w hw h1 h2 => ?_,
      fun a ha => ?_, I.disj, I.disjD, fun k hk => ?_, by have := I.grow; omega, h8, h9, h12, h14, h15⟩
  · rw [read64_keep (m := Mt) fun k hk => ?_]
    · exact hPM
    rw [hMcF _ (hPspan _ (by omega) (by omega)), copyW_out (by omega), hM1o _ (by omega) (by omega)]
  · rw [← hV, read64_keep (m := coalW W P ps S' hxv hdr0 predP succP) fun k hk => copyW_out (by omega)]
    rw [rd_miss (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hPodd]
  · rw [show P + (ps + S') + 8 = P + ps + S' + 8 by omega]; exact hMn
  · rw [show P + (ps + S') + 8 = P + ps + S' + 8 by omega]; exact hVn
  · exact hMcV w (vsaFoot_of_cons hw) h1 (by omega)
  · rw [hMcF a ha]; exact copyW_present (hpresM1 a ha)
  · rw [hMcF _ (hPspan _ (by omega) (by omega)),
      copyW_spec (.inl (by omega)) (fun i hi => hpresM1 _ (hsrcF i (by omega))) k (by omega),
      hnd _ (by omega) (by omega), show P + ps + 16 + k = B.p + k by omega]
    exact I.data k hk

/-- **The tail after absorbing into the predecessor** (`0x80005414`), the
successor in use: `pvG_rt` over the machine memory itself. -/
theorem pvX_rt {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ rest : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest)
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hfit : nb ≤ ps + S)
    {R' : Nat → BitVec 64} {Mc : Mem} (F : RFrame C R' Mc)
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (X + 16) ((S - 8) / 8))[a]?)
    (h8 : (R' 8).toNat = P + 16) (h9 : R' 9 = reentV) (h12 : (R' 12).toNat = P)
    (h14 : (R' 14).toNat = ps + S) (h15 : (R' 15).toNat = nb) :
    AW C.live C.S C.Q 0x80005414#64 R' Mc := by
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  have HH := H0.heap.heap
  have hpend := PV.pend
  subst hpend
  have hXm : (⟨P + ps, S, true⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S, true⟩ :: rest := by
    simp
  have hS := walk_sizes HH.walk _ hXm
  simp only at hS
  obtain ⟨⟨hn, hnr, hnp⟩, _⟩ := walk_next_of (cs₁ := cs₀ ++ [⟨P, ps, false⟩]) HH.walk
  simp only at hnr hnp
  have hnodd : hn % 2 = 1 := by unfold prevInuse at hnp; simpa using hnp
  have hsz8 : B.nOld + 8 ≤ S := by
    obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
    have := HH.chunk_eq hc0 hXm (by have := D.addr; simp only at hc0a ⊢; omega)
    subst this; simpa using hc0n
  exact pvG_rt O (W := Mt) (hxv := hdr0)
    { heap := H0, starts := Hp.starts, addr := D.addr, pv := PV, xW := D.hdr, xM := D.hdr,
      nM := hnr, nW := by rw [hnr]; congr 1; omega, agree := fun _ _ _ => rfl, pres := Hp.pres,
      disj := Hp.disj, disjD := Hp.disjD, data := Hp.data, grow := Hp.grow, nbok := D.nbok,
      fit := hfit, L8 := by omega, Lold := by omega, Lle := by omega }
    F hMc h8 h9 h12 h14 h15

/-- The frame through a memory that agrees on the saved words. -/
theorem RFrame.agree {C : MCtx} {R : Nat → BitVec 64} {M M' : Mem} (F : RFrame C R M)
    (h : ∀ a, C.s.toNat - 64 + 40 ≤ a → a < C.s.toNat - 64 + 64 → M'[a]? = M[a]?) :
    RFrame C R M' where
  sp := F.sp
  s0 := by rw [read64_keep fun k hk => h _ (by omega) (by omega)]; exact F.s0
  s1 := by rw [read64_keep fun k hk => h _ (by omega) (by omega)]; exact F.s1
  ra := by rw [read64_keep fun k hk => h _ (by omega) (by omega)]; exact F.ra
  s2 := F.s2
  s3 := F.s3

/-- **The predecessor paths' join** (`0x80005648`): `s0 := a3`, `a4 := a7`,
`a2 := t1`, then the tail. -/
theorem pvX_join {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ rest : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest)
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hfit : nb ≤ ps + S)
    {R' : Nat → BitVec 64} {Mc : Mem} (F : RFrame C R' Mc)
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (X + 16) ((S - 8) / 8))[a]?)
    (h13 : (R' 13).toNat = P + 16) (h9 : R' 9 = reentV) (h6 : (R' 6).toNat = P)
    (h17 : (R' 17).toNat = ps + S) (h15 : (R' 15).toNat = nb) :
    AW C.live C.S C.Q 0x80005648#64 R' Mc := by
  have z : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := rfl
  refine st_80005648 O.live (st_8000564c O.live (st_80005650 O.live (st_80005654 O.live ?_)))
  refine pvX_rt O D hsp PV hfit (F.of_regs ?_ ?_ ?_) hMc ?_ ?_ ?_ ?_ ?_ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, z, BitVec.add_zero] <;> assumption

/-- **The prev+X copy through `memmove`** (`0x80005710`): spill `t1`, `a5`,
`a7`, `a3` at `sp`, `memmove(a3, s0, a2)`, reload them and join at
`0x80005648`. -/
theorem pv_mm {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {M1 : Mem} {d s n : Nat}
    (A : MMArgs C.S d s n) (F : RFrame C R M1)
    (hslotD : d + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ d)
    (hslotS : s + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ s)
    (h13 : (R 13).toNat = d) (h8 : (R 8).toNat = s) (h12 : (R 12).toNat = n)
    (hk : ∀ R' Mc, RFrame C R' Mc →
      (∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → Mc[a]? = (copyW M1 d s (n / 8))[a]?) →
      (R' 13).toNat = (R 13).toNat → (R' 6).toNat = (R 6).toNat → (R' 15).toNat = (R 15).toNat →
      (R' 17).toNat = (R 17).toNat → R' 9 = R 9 → AW C.live C.S C.Q 0x80005648#64 R' Mc) :
    AW C.live C.S C.Q 0x80005710#64 R M1 := by
  have hs64 := sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hn := A.n32; have hn8 := A.n8
  have e : ∀ c, c < 32 → (R 2 + BitVec.ofNat 64 c).toNat = C.s.toNat - 64 + c := fun c hc => by
    rw [F.sp, addr_add hs64 c (by omega)]
  have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
  have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have n24 : (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 := rfl
  have st : ∀ c, c ≤ 24 → c % 8 = 0 → StOK (C.s.toNat - 64 + c) 8 ∧ ∀ b ∈ accAddrs (C.s.toNat - 64 + c) 8, C.S b :=
    fun c hc hc8 => ⟨by unfold StOK Vsa.Sim.tohostAddr; omega, O.stack (by unfold mHead; omega) (by omega)⟩
  have ld : ∀ c, c ≤ 24 → c % 8 = 0 → LdOK (C.s.toNat - 64 + c) 8 ∧ ∀ b ∈ accAddrs (C.s.toNat - 64 + c) 8, C.S b :=
    fun c hc hc8 => ⟨by unfold LdOK Vsa.Sim.tohostAddr; omega, O.stack (by unfold mHead; omega) (by omega)⟩
  refine st_80005710 O.live (st_80005714 O.live ?_)
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  refine st_80005718 O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n24]; rw [e 24 (by omega)]; exact (st 24 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n24]; rw [e 24 (by omega)]; exact (st 24 (by omega) (by omega)).2) ?_
  refine st_8000571c O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e 16 (by omega)]; exact (st 16 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e 16 (by omega)]; exact (st 16 (by omega) (by omega)).2) ?_
  refine st_80005720 O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e 8 (by omega)]; exact (st 8 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e 8 (by omega)]; exact (st 8 (by omega) (by omega)).2) ?_
  refine st_80005724 O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]; rw [e 0 (by omega)]; exact (st 0 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]; rw [e 0 (by omega)]; exact (st 0 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, n24, n16, n8, n0]
  rw [e 24 (by omega), e 16 (by omega), e 8 (by omega), e 0 (by omega)]
  refine st_80005728 O.live ?_
  simp only [VsaIris.ra]
  generalize hW : writeLog (writeLog (writeLog (writeLog M1 [(C.s.toNat - 64 + 24, 8, R 6)])
    [(C.s.toNat - 64 + 16, 8, R 15)]) [(C.s.toNat - 64 + 8, 8, R 17)]) [(C.s.toNat - 64 + 0, 8, R 13)] = W
  have hWo : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → W[a]? = M1[a]? := fun a ha => by
    rw [← hW, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      simp only [OutL, and_true] <;> omega
  refine memmove_fwd A O.live ?_ ?_ ?_ (by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; decide)
    fun R' hK => ?_ <;> try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [BitVec.add_zero]; exact h13
  · rw [BitVec.add_zero]; exact h8
  · exact h12
  rw [show (BitVec.ofNat 64 (2147505960 + 4) : BitVec 64) = 0x8000572c#64 from rfl]
  have hR2 : R' 2 = R 2 := by rw [hK.sp]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  have e' : ∀ c, c < 32 → (R' 2 + BitVec.ofNat 64 c).toNat = C.s.toNat - 64 + c := fun c hc => by
    rw [hR2]; exact e c hc
  have hcpO : ∀ a, C.s.toNat - 64 ≤ a → a < C.s.toNat →
      (copyW W d s (n / 8))[a]? = W[a]? := fun a h1 h2 => copyW_out (by omega)
  have rd : ∀ c (v : BitVec 64), c ≤ 24 → W = writeLog (writeLog (writeLog (writeLog M1
        [(C.s.toNat - 64 + 24, 8, R 6)]) [(C.s.toNat - 64 + 16, 8, R 15)])
        [(C.s.toNat - 64 + 8, 8, R 17)]) [(C.s.toNat - 64 + 0, 8, R 13)] →
      read64 W (C.s.toNat - 64 + c) = some v.toNat →
      ldv .ld (copyW W d s (n / 8)) (C.s.toNat - 64 + c) = v := fun c v hc _ hr =>
    ldv_ld (by rw [read64_keep (m := W) fun k hk => hcpO _ (by omega) (by omega)]; exact hr)
  have r24 : read64 W (C.s.toNat - 64 + 24) = some (R 6).toNat := by
    rw [← hW, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), read64_store_hit]
  have r16 : read64 W (C.s.toNat - 64 + 16) = some (R 15).toNat := by
    rw [← hW, rd_miss (by omega), rd_miss (by omega), read64_store_hit]
  have r8 : read64 W (C.s.toNat - 64 + 8) = some (R 17).toNat := by
    rw [← hW, rd_miss (by omega), read64_store_hit]
  have r0 : read64 W (C.s.toNat - 64 + 0) = some (R 13).toNat := by
    rw [← hW, read64_store_hit]
  refine st_8000572c O.live (by rw [n24, e' 24 (by omega)]; exact (ld 24 (by omega) (by omega)).1)
    (by rw [n24, e' 24 (by omega)]; exact (ld 24 (by omega) (by omega)).2) ?_
  rw [n24, e' 24 (by omega), rd 24 _ (by omega) hW.symm r24]
  refine st_80005730 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e' 16 (by omega)]
        exact (ld 16 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e' 16 (by omega)]
        exact (ld 16 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]
  rw [e' 16 (by omega), rd 16 _ (by omega) hW.symm r16]
  refine st_80005734 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e' 8 (by omega)]
        exact (ld 8 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e' 8 (by omega)]
        exact (ld 8 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]
  rw [e' 8 (by omega), rd 8 _ (by omega) hW.symm r8]
  refine st_80005738 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]; rw [e' 0 (by omega)]
        exact (ld 0 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]; rw [e' 0 (by omega)]
        exact (ld 0 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]
  rw [e' 0 (by omega), rd 0 _ (by omega) hW.symm r0]
  refine st_8000573c O.live ?_
  refine hk _ _ ((F.of_regs ?_ ?_ ?_).agree fun a h1 h2 => ?_) (fun a ha => ?_) ?_ ?_ ?_ ?_ ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hR2
  · rw [hK.s2]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  · rw [hK.s3]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  · rw [hcpO a (by omega) (by omega), hWo a (by omega)]
  · exact copyW_agreeOn (Pr := fun a => a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) hWo
      (fun i hi => by omega) a ha
  · rw [hK.s1]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]

/-- The bytes from the free predecessor's header up to the old chunk's end
are allocator footprint. -/
theorem pv_span {C : MCtx} {B : RB} {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₀ rest : List Chunk} {P ps : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest) (hX : X = P + ps) :
    ∀ a, P + 8 ≤ a → a < X + S + 8 → vsaFoot C.H a := by
  subst hX
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  have HdX : PHeapAt Mt C.H C.top0 brkv ((cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S, true⟩ :: rest) bins :=
    H0.drop
  have hst := Hp.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have hnoX : ∀ e ∈ C.H, e.1 ≠ P + ps + 16 := fun e he heq =>
    hst.1 (List.mem_map.2 ⟨e, he, by rw [heq]; exact D.addr⟩)
  intro a h1 h2
  by_cases ha : a < P + ps + 16
  · exact foot_free_span HdX.heap (c := ⟨P, ps, false⟩) (by simp) rfl a h1 ha
  · exact HdX.payload_foot (c := ⟨P + ps, S, true⟩) (by simp) hnoX a (by simp only; omega)
      (by simp only; omega)

/-- **Into the free predecessor** (`0x800055e4`): unlink `P`, copy the
payload down to `P + 16` (inline up to 72 bytes, else `memmove`), and join
the tail with the chunk `P` of `ps + S` bytes. -/
theorem realloc_pvX {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ rest : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: rest)
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hfit : nb ≤ ps + S) (h6 : (R 6).toNat = P) (h17 : (R 17).toNat = ps + S) :
    AW C.live C.S C.Q 0x800055e4#64 R Mt := by
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  have G : PvGeo C' P ps S predP succP := PvGeo.of_heap (C := C') H0 PV
  have hpend : X = P + ps := PV.pend.symm
  have hspan := pv_span D hsp hpend
  subst hpend
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hs16 := G.sz16; have hs32 := G.sz32
  have hxend : P + ps + S ≤ C.top0 := G.xend; have htop : C.top0 + 16 ≤ 0x87800000 := G.top
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have hpphi : predP + 32 ≤ C.top0 := G.pphi; have hsphi : succP + 32 ≤ C.top0 := G.sphi
  have hlo := O.spA.lo; have hhi := O.spA.hi
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hdisj := Hp.disjD
  unfold allocHeadroom at hdisj
  -- the link words
  have hPf := (foot_free H0.heap (c' := ⟨P, ps, false⟩) (by simp) rfl).1
  simp only at hPf
  have fB : ∀ k, k < 8 → vsaFoot C.H (P + 24 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := hPf (8 + k) (by omega); rwa [show P + 16 + (8 + k) = P + 24 + k by omega] at this)
  have fF : ∀ k, k < 8 → vsaFoot C.H (P + 16 + k) := fun k hk => vsaFoot_cons_sub _ (hPf k (by omega))
  have fS : ∀ k, k < 8 → vsaFoot C.H (succP + 24 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := G.spfoot (24 + k) (by omega) (by omega)
    rwa [show succP + (24 + k) = succP + 24 + k by omega] at this)
  have fP : ∀ k, k < 8 → vsaFoot C.H (predP + 16 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := G.ppfoot (16 + k) (by omega) (by omega)
    rwa [show predP + (16 + k) = predP + 16 + k by omega] at this)
  have hpl := Vsa.Sim.read64_lt _ _ _ PV.bk
  have hsl := Vsa.Sim.read64_lt _ _ _ PV.fd
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have n24 : (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 := rfl
  have eB : (R 6 + sign_extend (m := 64) (0x018#12)).toNat = P + 24 := by rw [n24, addr_add h6 24 (by omega)]
  have eF : (R 6 + sign_extend (m := 64) (0x010#12)).toNat = P + 16 := by rw [n16, addr_add h6 16 (by omega)]
  refine st_800055e4 O.live (by rw [eB]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [eB]; exact O.foot fB) ?_
  rw [eB, ldv_at PV.bk _ rfl]
  refine st_800055e8 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eF]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eF]; exact O.foot fF) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [eF, ldv_at PV.fd _ rfl]
  refine st_800055ec O.live (st_800055f0 O.live ?_)
  have hvP : (BitVec.ofNat 64 predP).toNat = predP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hvS : (BitVec.ofNat 64 succP).toNat = succP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
  have eS : (BitVec.ofNat 64 succP + sign_extend (m := 64) (0x018#12)).toNat = succP + 24 := by
    rw [n24, addr_add hvS 24 (by omega)]
  have eP : (BitVec.ofNat 64 predP + sign_extend (m := 64) (0x010#12)).toNat = predP + 16 := by
    rw [n16, addr_add hvP 16 (by omega)]
  refine st_800055f4 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eS]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eS]; exact O.foot fS) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eS]
  refine st_800055f8 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eP]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eP]; exact O.foot fP) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eP]
  have eL : (R 14 + sign_extend (m := 64) (0xff8#12)).toNat = S - 8 := by
    rw [show (sign_extend (m := 64) (0xff8#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl,
      addr_sub D.a4 8 (by omega) (by omega)]
  have e72 : (0#64 + sign_extend (m := 64) (0x048#12)).toNat = 72 := rfl
  -- the unlinked memory, the frame, the copy's arguments
  have oS := off_stack_of Hp.disj fS
  have oP := off_stack_of Hp.disj fP
  have F1 : RFrame C R (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
      [(predP + 16, 8, BitVec.ofNat 64 succP)]) :=
    (D.frame.store (by omega)).store (by omega)
  have hstk : ∀ a, vsaFoot C.H a → a < C.s.toNat - 512 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => hdisj a (by omega) (by omega) ha
  have hdst : P + 16 + (S - 8) ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ P + 16 := by
    rcases hstk _ (hspan (P + 16) (by omega) (by omega)) with h | h
    · rcases hstk _ (hspan (P + 16 + (S - 9)) (by omega) (by omega)) with h' | h'
      · exact .inl (by omega)
      · exfalso
        have := hstk (C.s.toNat - 64) (hspan _ (by omega) (by omega)); omega
    · exact .inr h
  have hsrc : P + ps + 16 + (S - 8) ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ P + ps + 16 := by
    rcases hdst with h | h
    · rcases hstk _ (hspan (P + ps + 16 + (S - 9)) (by omega) (by omega)) with h' | h'
      · exact .inl (by omega)
      · exfalso
        have := hstk (C.s.toNat - 64) (hspan _ (by omega) (by omega)); omega
    · exact .inr (by omega)
  have A : CPArgs C.S (P + 16) (P + ps + 16) (S - 8) :=
    { n8 := by omega, d8 := by omega, s8 := by omega, ov := .inl (by omega),
      dlo := by unfold Vsa.Sim.tohostAddr; omega, dhi := by omega,
      slo := by unfold Vsa.Sim.tohostAddr; omega, shi := by omega,
      sS := fun k hk => O.own _ (.inl (hspan _ (by omega) (by omega))),
      dS := fun k hk => O.own _ (.inl (hspan _ (by omega) (by omega))) }
  have z : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := rfl
  have h13' : (R 6 + sign_extend (m := 64) (0x010#12)).toNat = P + 16 := eF
  refine st_800055fc O.live (st_80005600 O.live (fun hc => ?_) (fun hc => ?_)) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, eL, e72] at hc ⊢
  · -- over 72 bytes: `memmove`
    refine pv_mm O { A with n32 := by omega } (F1.of_regs ?_ ?_ ?_) hdst hsrc ?_ ?_ ?_
      (fun R' Mc F' hMc g13 g6 g15 g17 g9 => pvX_join O D hsp PV hfit F' hMc ?_ ?_ ?_ ?_ ?_) <;>
      (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · exact eF
    · exact D.s0
    · exact eL
    · rw [g13]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact eF
    · rw [g9]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact D.s1
    · rw [g6]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h6
    · rw [g17]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h17
    · rw [g15]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact D.a5
  · -- up to 72 bytes: inline
    have hLs : S - 8 = 24 ∨ S - 8 = 40 ∨ S - 8 = 56 ∨ S - 8 = 72 := by omega
    refine pvA_inline A O.live hLs rfl ?_ ?_ ?_ ?_ ?_ fun R' K => pvX_join O D hsp PV hfit
      ((F1.of_regs ?_ ?_ ?_).agree fun a h1 h2 => ?_) (fun a _ => rfl) ?_ ?_ ?_ ?_ ?_ <;>
      (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · exact D.s0
    · exact h6
    · exact eF
    · exact eL
    · rfl
    · rw [K.sp]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [K.s2]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [K.s3]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact copyW_out (by omega)
    · rw [K.a3]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact eF
    · rw [K.s1]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact D.s1
    · rw [K.t1]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h6
    · rw [K.a7]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h17
    · rw [K.a5]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact D.a5
