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

/-- The machine memory after unlinking the free predecessor `p` agrees with
the coalesced virtual heap `b2Mem` everywhere but `p`'s header. -/
theorem pv_agree_all {C : MCtx} {Mt : Mem} {p psz sz hdr0 predP succP : Nat}
    (G : PvGeo C p psz sz predP succP) (hdr : read64 Mt (p + psz + 8) = some hdr0)
    {v1 v2 : BitVec 64} (h1 : v1.toNat = predP) (h2 : v2.toNat = succP) :
    ∀ w0, ¬ (p + 8 ≤ w0 ∧ w0 < p + 16) →
      (writeLog (writeLog Mt [(succP + 24, 8, v1)]) [(predP + 16, 8, v2)])[w0]? =
      (b2Mem Mt p psz sz hdr0 predP succP)[w0]? := by
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  intro w0 h1'
  refine agree_of_words (P := fun x => ¬ (p + 8 ≤ x ∧ x < p + 16))
    [succP + 24, predP + 16, p + psz + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 h1'
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
      · rw [rd_miss (by omega), rd_miss (by omega)]; exact hdr
      · rw [read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hout
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out] <;> simp only [OutL, and_true] <;> omega

/-- **The tail after absorbing into the predecessor** (`0x80005414`): the
machine memory is the unlink and the payload's copy to `P + 16` (off
`_realloc_r`'s spill words); the virtual heap is `coalPrev`'s, with the
copied payload in a block at `P + 16`. -/
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
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  have G : PvGeo C' P ps S predP succP := PvGeo.of_heap (C := C') H0 PV
  have hpend := PV.pend
  subst hpend
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hs16 := G.sz16; have hs32 := G.sz32
  have hxend : P + ps + S ≤ C.top0 := G.xend; have htop : C.top0 + 16 ≤ 0x87800000 := G.top
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have hpphi : predP + 32 ≤ C.top0 := G.pphi; have hsphi : succP + 32 ≤ C.top0 := G.sphi
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have haddr := D.addr
  have hnb := D.nbok.eq
  have hnbv : C.n.toNat + 8 ≤ nb := by rw [hnb]; unfold physSize; omega
  -- the boundary after `X` is no bin node's link word
  have hXm : (⟨P + ps, S, true⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S, true⟩ :: rest := by simp
  have hbE : P + ps + S = C.top0 ∨ ∃ c ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S, true⟩ :: rest,
      c.addr = P + ps + S := by have := HH.end_bnd hXm; simpa using this
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
  -- the header after `X`, marked in use
  have hw := HH.walk
  obtain ⟨⟨hn, hnr, hnp⟩, _⟩ := walk_next_of (cs₁ := cs₀ ++ [⟨P, ps, false⟩]) hw
  simp only at hnr hnp
  have hnodd : hn % 2 = 1 := by unfold prevInuse at hnp; simpa using hnp
  -- the virtual heap: `P` absorbs `X`, a block over its payload, the copy, the block resized
  have Hd := H0.drop
  simp only [List.append_assoc, List.singleton_append] at Hd
  have hst := Hp.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have hnoX : ∀ e ∈ C.H, e.1 ≠ P + ps + 16 := fun e he heq =>
    hst.1 (List.mem_map.2 ⟨e, he, by rw [heq]; exact haddr⟩)
  obtain ⟨hP, hPr⟩ : ∃ hP, read64 Mt (P + 8) = some hP := by
    obtain ⟨hh, hhr, _, _⟩ := walk_header HH.walk ⟨P, ps, false⟩ (by simp)
    exact ⟨hh, hhr⟩
  have hPodd := PV.prev hP hPr
  have Hc := Hd.coalPrev (cs₂ := rest) (b := S) hnoX PV.i0 PV.i1 PV.bin PV.hpred PV.hsucc D.hdr
    (h' := ps + S + 1) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      have := PV.prev h0 hr; unfold prevInuse; rw [show (ps + S + 1) % 2 = 1 by omega, this])
    (BitVec.ofNat 64 hdr0)
  have hPm : (⟨P, ps + S, true⟩ : Chunk) ∈ cs₀ ++ ⟨P, ps + S, true⟩ :: rest := by simp
  have Ha := Hc.addBlock (q := P + 16) (n := ps + S - 8) hPm rfl rfl (by simp only; omega)
  generalize hV : copyW (b2Mem Mt P ps S hdr0 predP succP) (P + 16) (P + ps + 16) ((S - 8) / 8) = V
  have hL8 : 8 * ((S - 8) / 8) = S - 8 := by omega
  have HV : PHeapAt V ((P + 16, ps + S - 8) :: C.H) C.top0 brkv (cs₀ ++ ⟨P, ps + S, true⟩ :: rest)
      (updBins bins i (pre ++ post)) := by
    refine Ha.transport_read fun a ha => ?_
    rw [← hV]
    refine (copyW_out ?_).symm
    rcases ha.1 with hg | ⟨_, _, h3⟩
    · have := allocGlobal_off_arena _ hg; unfold heapStart heapEnd at this; omega
    · have := h3 _ List.mem_cons_self; unfold InExt at this; simp only at this; omega
  have Hr := HV.reblock (c := ⟨P, ps + S, true⟩) hPm rfl rfl (n' := C.n.toNat) (by simp only; omega)
  -- the machine memory
  have hpl := Vsa.Sim.read64_lt _ _ _ PV.bk
  have hsl := Vsa.Sim.read64_lt _ _ _ PV.fd
  have hv1 : (BitVec.ofNat 64 predP).toNat = predP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hv2 : (BitVec.ofNat 64 succP).toNat = succP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
  generalize hM1 : writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
    [(predP + 16, 8, BitVec.ofNat 64 succP)] = M1 at hMc
  have hag1 : ∀ w, ¬ (P + 8 ≤ w ∧ w < P + 16) → M1[w]? = (b2Mem Mt P ps S hdr0 predP succP)[w]? :=
    fun w hw => by rw [← hM1]; exact pv_agree_all G D.hdr hv1 hv2 w hw
  have hM1o : ∀ a, ¬ (succP + 24 ≤ a ∧ a < succP + 32) → ¬ (predP + 16 ≤ a ∧ a < predP + 24) →
      M1[a]? = Mt[a]? := fun a h1 h2 => by
    rw [← hM1, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  have hstk : ∀ a, vsaFoot C.H a → a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a := fun a ha => by
    have hlo := O.spA.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
    have := Classical.byContradiction fun hc : ¬ (a < C.s.toNat - allocHeadroom ∨ C.s.toNat ≤ a) =>
      Hp.disjD a (by omega) (by omega) ha
    unfold allocHeadroom at this; omega
  -- the payload of `X` and the block's bytes
  have HdX : PHeapAt Mt C.H C.top0 brkv ((cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S, true⟩ :: rest) bins :=
    H0.drop
  have hsrcF : ∀ k, k < S - 8 → vsaFoot C.H (P + ps + 16 + k) := fun k hk =>
    HdX.payload_foot hXm hnoX _ (by simp only; omega) (by simp only; omega)
  have hpresM1 : ∀ a, vsaFoot C.H a → (M1[a]?).isSome := fun a ha => by
    rw [← hM1]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (Hp.pres a ha))
  have hMcF : ∀ a, vsaFoot C.H a →
      Mc[a]? = (copyW M1 (P + 16) (P + ps + 16) ((S - 8) / 8))[a]? := fun a ha => hMc a (hstk a ha)
  have hcpy : ∀ a, ¬ (P + 8 ≤ a ∧ a < P + 16) →
      (copyW M1 (P + 16) (P + ps + 16) ((S - 8) / 8))[a]? = V[a]? := fun a ha => by
    rw [← hV]; exact copyW_agree (t := P + 8) (fun a h => hag1 a (by omega)) (by omega) a (by omega)
  -- the payload's bytes are no node word
  have hnd : ∀ a, P + ps ≤ a → a < P + ps + S + 8 → M1[a]? = Mt[a]? := fun a h1 h2 =>
    hM1o a (by have := node_off_inuse HH PV.i1 hsnode hXm rfl a h1 h2; omega)
      (by have := node_off_inuse HH PV.i1 hpnode hXm rfl a h1 h2; omega)
  have hnh : ∀ k, k < 8 → vsaFoot C.H (P + ps + S + 8 + k) := foot_header HdX.heap hbE
  clear hbE hpnode hsnode hpm hsm
  have hStarts : Starts ((P + 16, C.n.toNat) :: C.H) := by
    refine Starts.cons hst.2 fun e he heq => ?_
    have he' : e ∈ (B.p, B.nOld) :: C.H := List.mem_cons_of_mem _ he
    obtain ⟨c0, hc0, hu, hc0a, _⟩ := HH.exact e he' he'
    have := HH.chunk_eq hc0 (show (⟨P, ps, false⟩ : Chunk) ∈
      (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨P + ps, S, true⟩ :: rest by simp) (by simp only; omega)
    rw [this] at hu; cases hu
  have hPno : ∀ e ∈ C.H, e.1 ≠ P + 16 := fun e he heq => by
    have := hStarts; unfold Starts at this
    rw [List.map_cons, List.nodup_cons] at this
    exact this.1 (List.mem_map.2 ⟨e, he, heq⟩)
  have hPspan : ∀ a, P + 8 ≤ a → a < P + ps + S + 8 → vsaFoot C.H a := fun a h1 h2 => by
    by_cases ha : a < P + ps + 16
    · exact foot_free_span HdX.heap (c := ⟨P, ps, false⟩) (by simp) rfl a h1 ha
    · exact hsrcF (a - (P + ps + 16)) (by omega) |> fun h => by
        rwa [show P + ps + 16 + (a - (P + ps + 16)) = a by omega] at h
  have hMcV : ∀ a, vsaFoot C.H a → ¬ (P + 8 ≤ a ∧ a < P + 16) → Mc[a]? = V[a]? :=
    fun a h1 h2 => (hMcF a h1).trans (hcpy a h2)
  have hVn : read64 V (P + ps + S + 8) = some hn := by
    rw [← hV, read64_keep (m := b2Mem Mt P ps S hdr0 predP succP) fun k hk => copyW_out (by omega)]
    rw [rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), rd_miss (by omega),
      rd_miss (by omega)]
    exact hnr
  refine realloc_tail O (V := V) (X := P) (S := ps + S) (nb := nb) (cs₁ := cs₀) (cs₂ := rest)
    ⟨F, Hr, hStarts, by omega, D.nbok, hfit, ⟨hP, ?_, ?_⟩, ⟨hn, ?_, ?_⟩, fun w hw h1 h2 => ?_,
      fun a ha => ?_, Hp.disj, Hp.disjD, fun k hk => ?_, by have := Hp.grow; omega, h8, h9, h12, h14, h15⟩
  · rw [read64_keep (m := Mt) fun k hk => ?_]
    · exact hPr
    rw [hMcF _ (hPspan _ (by omega) (by omega)), copyW_out (by omega), hM1o _ (by omega) (by omega)]
  · rw [← hV, read64_keep (m := b2Mem Mt P ps S hdr0 predP succP) fun k hk => copyW_out (by omega)]
    rw [rd_miss (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      PV.prev hP hPr]
  · rw [show P + (ps + S) + 8 = P + ps + S + 8 by omega]
    rw [read64_keep (m := V) fun k hk => hMcV _ (hnh k hk) (by omega)]
    exact hVn
  · rw [show P + (ps + S) + 8 = P + ps + S + 8 by omega, hVn]; congr 1; omega
  · exact hMcV w (vsaFoot_of_cons hw) h1
  · rw [hMcF a ha]; exact copyW_present (hpresM1 a ha)
  · have hsz8 : B.nOld + 8 ≤ S := by
      obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
      have := HH.chunk_eq hc0 hXm (by simp only at hc0a ⊢; omega)
      subst this; simpa using hc0n
    rw [hMcF _ (hPspan _ (by omega) (by omega)),
      copyW_spec (.inl (by omega)) (fun i hi => hpresM1 _ (hsrcF i (by omega))) k (by omega),
      hnd _ (by omega) (by omega), show P + ps + 16 + k = B.p + k by omega]
    exact Hp.data k hk
