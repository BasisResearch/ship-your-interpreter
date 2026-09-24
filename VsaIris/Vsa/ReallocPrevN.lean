import VsaIris.Vsa.ReallocPrev

/-!
# `_realloc_r` into a free predecessor and a free successor

Both neighbours of the old chunk are free: the successor is absorbed first
(`next_absorb`), then the predecessor unlinked and the payload copied down
(`pvG_rt` over the absorbed virtual heap). The copy is `pvN_inline` (the
unrolled words at this path's code) or `memmove_fwd`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section Copy

variable {live : Nat → Prop} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- The three-word tail of the prev+X+next copy (`0x800056c8`): words
`j … j+2` from `s0` to `a4`. -/
theorem pvN_tail3 {M0 : Mem} {d s L : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    {R0 R : Nat → BitVec 64} {j : Nat} (h8 : (R 8).toNat = s + 8 * j) (h14 : (R 14).toNat = d + 8 * j)
    (hj : 8 * j + 24 ≤ L) (K : PVKeep R0 R)
    (hk : ∀ R', PVKeep R0 R' → AW live S Q 0x800056e0#64 R' (copyW M0 d s (j + 3))) :
    AW live S Q 0x800056c8#64 R (copyW M0 d s j) := by
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
  have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * j) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * j) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 8) (rD := 14) (by decide) (st_800056c8 hlive) (st_800056cc hlive)
    (by rw [n0, addr_add h8 0 (by omega)]; omega) (by rw [n0, addr_add h14 0 (by omega)]; omega)
    l1 l2 s1 s2 ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * (j + 1)) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * (j + 1)) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 8) (rD := 14) (by decide) (st_800056d0 hlive) (st_800056d4 hlive)
    (by rw [upd_other _ _ (by decide), n8, addr_add h8 8 (by omega)]; omega)
    (by rw [upd_other _ _ (by decide), n8, addr_add h14 8 (by omega)]; omega) l1 l2 s1 s2 ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * (j + 2)) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * (j + 2)) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 8) (rD := 14) (by decide) (st_800056d8 hlive) (st_800056dc hlive)
    (by rw [upd_other _ _ (by decide), upd_other _ _ (by decide), n16, addr_add h8 16 (by omega)]; omega)
    (by rw [upd_other _ _ (by decide), upd_other _ _ (by decide), n16, addr_add h14 16 (by omega)]; omega)
    l1 l2 s1 s2 ?_
  exact hk _ (by pv_keep K)

/-- The prev+X+next path's inline copy (`0x8000569c`, a payload of 24,
40, 56 or 72 bytes, from `s0` to `t1 + 16`). -/
theorem pvN_inline {M0 : Mem} {d s L P : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    (hL : L = 24 ∨ L = 40 ∨ L = 56 ∨ L = 72) (hP : P + 16 = d)
    {R : Nat → BitVec 64} (h8 : (R 8).toNat = s) (h6 : (R 6).toNat = P) (h16 : (R 16).toNat = d)
    (h12 : (R 12).toNat = L)
    (hk : ∀ R', PVKeep R R' → AW live S Q 0x800056e0#64 R' (copyW M0 d s (L / 8))) :
    AW live S Q 0x8000569c#64 R (copyW M0 d s 0) := by
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
      (R' 14).toNat = d + 8 * j → PVKeep R R' → AW live S Q 0x800056c8#64 R' (copyW M0 d s j) :=
    fun j R' hj g8 g14 K => pvN_tail3 A hlive g8 g14 (by omega) K fun R'' K' => by rw [hj]; exact hk R'' K'
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
  refine st_8000569c hlive ?_
  refine st_800056a0 hlive ?_
  refine st_800056a4 hlive (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x027#12) : BitVec 64).toNat = 39 from rfl] at hc
  · -- 24 bytes: the tail alone
    refine tail 0 _ (by omega) ?_ ?_ (by pv_keep (PVKeep.refl R)) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [h8]; rfl
    · rw [n0, e _ _ _ h16 (by omega)]
  -- 40, 56 or 72 bytes: word 0, with `li a4,55` before its store
  refine aw_forget (fun R0 => PVKeep R R0 ∧ (R0 8).toNat = s ∧ (R0 12).toNat = L)
    ⟨by pv_keep (PVKeep.refl R), by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h8,
      by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h12⟩ fun R0 ⟨K0, g8, g12⟩ => ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 0) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 0) (by omega) (by omega) (by omega)
  have e0 : (R0 8 + sign_extend (m := 64) (0x000#12)).toNat = s + 8 * 0 := by rw [n0, e _ _ _ g8 (by omega)]
  refine st_800056a8 hlive (by rw [e0]; exact l1) (by rw [e0]; exact l2) ?_
  rw [e0]
  refine st_800056ac hlive ?_
  have f0 : ((upd (upd R0 11 (ldv .ld (copyW M0 d s 0) (s + 8 * 0))) 14
      (0#64 + sign_extend (m := 64) (0x037#12))) 6 + sign_extend (m := 64) (0x010#12)).toNat =
      d + 8 * 0 := by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K0.t1, n16, e _ _ _ h6 (by omega)]; omega
  refine st_800056b0 hlive (by rw [f0]; exact s1) (by rw [f0]; exact s2) ?_
  rw [f0]
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [← copyW_succ]
  refine aw_forget (fun R1 => PVKeep R R1 ∧ (R1 8).toNat = s ∧ (R1 14).toNat = 55 ∧ (R1 12).toNat = L)
      ⟨by pv_keep K0, by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact g8,
        by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; rfl,
        by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact g12⟩
    fun R1 ⟨K1, g8, g14, g12⟩ => ?_
  -- word 1
  refine pair 1 (offL := 0x008#12) (offS := 0x018#12) 11 R1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n8 n24 (by omega)
    (st_800056b4 hlive) (st_800056b8 hlive) K1 g8 fun v => ?_
  refine st_800056bc hlive (fun hc' => ?_) (fun hc' => ?_) <;>
    rw [upd_other _ _ (by decide), upd_other _ _ (by decide), g14, g12] at hc'
  · -- 56 or 72 bytes: word 2, with `li a4,72` before its store, and word 3
    have K2 := K1.upd v (k := 11) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 2) (by omega) (by omega)
    obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 2) (by omega) (by omega) (by omega)
    have e2 : (upd R1 11 v 8 + sign_extend (m := 64) (0x010#12)).toNat = s + 8 * 2 := by
      rw [upd_other _ _ (by decide), n16, e _ _ _ g8 (by omega)]
    refine st_800057f4 hlive (by rw [e2]; exact l1) (by rw [e2]; exact l2) ?_
    rw [e2]
    refine st_800057f8 hlive ?_
    have f2 : ((upd (upd (upd R1 11 v) 11 (ldv .ld (copyW M0 d s 2) (s + 8 * 2))) 14
        (0#64 + sign_extend (m := 64) (0x048#12))) 6 + sign_extend (m := 64) (0x020#12)).toNat =
        d + 8 * 2 := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K1.t1, n32, e _ _ _ h6 (by omega)]; omega
    refine st_800057fc hlive (by rw [f2]; exact s1) (by rw [f2]; exact s2) ?_
    rw [f2]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [← copyW_succ]
    refine aw_forget (fun R3 => PVKeep R R3 ∧ (R3 8).toNat = s ∧ (R3 14).toNat = 72 ∧ (R3 12).toNat = L)
        ⟨by pv_keep K2, by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact g8,
          by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; rfl,
          by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact g12⟩
      fun R3 ⟨K3, g8', g14', g12'⟩ => ?_
    refine pair 3 (offL := 0x018#12) (offS := 0x028#12) 11 R3 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) n24 n40 (by omega)
      (st_80005800 hlive) (st_80005804 hlive) K3 g8' fun v3 => ?_
    refine st_80005808 hlive (fun hc'' => ?_) (fun hc'' => ?_)
    · -- 72 bytes: words 4 and 5, then the tail
      have hL72 : L = 72 := by
        have := congrArg BitVec.toNat hc''
        simp only [upd_apply, Nat.reduceEqDiff, ite_false] at this; rw [g12', g14'] at this; exact this
      refine aw_forget (fun R2 => PVKeep R R2 ∧ (R2 8).toNat = s)
        ⟨by pv_keep K3, by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact g8'⟩
        fun R2 ⟨K4, h8'⟩ => ?_
      obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 4) (by omega) (by omega)
      obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 4) (by omega) (by omega) (by omega)
      have e4 : (R2 8 + sign_extend (m := 64) (0x020#12)).toNat = s + 8 * 4 := by
        rw [n32, e _ _ _ h8' (by omega)]
      refine st_80005888 hlive (by rw [e4]; exact l1) (by rw [e4]; exact l2) ?_
      rw [e4]
      refine st_8000588c hlive ?_
      refine st_80005890 hlive ?_
      have f4 : ((upd (upd (upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 14
          ((upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 6 + sign_extend (m := 64) (0x040#12))) 8
          ((upd (upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 14
            ((upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 6 + sign_extend (m := 64) (0x040#12))) 8 +
            sign_extend (m := 64) (0x030#12))) 6 + sign_extend (m := 64) (0x030#12)).toNat = d + 8 * 4 := by
        simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K4.t1, n48, e _ _ _ h6 (by omega)]; omega
      refine st_80005894 hlive (by rw [f4]; exact s1) (by rw [f4]; exact s2) ?_
      rw [f4]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [← copyW_succ]
      obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 5) (by omega) (by omega)
      obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 5) (by omega) (by omega) (by omega)
      have g8' : (R2 8 + sign_extend (m := 64) (0x030#12)).toNat = s + 48 := by
        rw [n48, e _ _ _ h8' (by omega)]
      refine cp_pair (rT := 12) (rS := 8) (rD := 6) (by decide) (st_80005898 hlive) (st_8000589c hlive)
        ?_ ?_ l1 l2 s1 s2 ?_
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [nm8, addr_sub g8' 8 (by omega) (by omega)]; omega
      · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K4.t1, n56, e _ _ _ h6 (by omega)]; omega
      refine st_800058a0 hlive ?_
      refine tail 6 _ (by omega) ?_ ?_ (by pv_keep K4) <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [g8']
      · rw [K4.t1, n64, e _ _ _ h6 (by omega)]; omega
    · -- 56 bytes: the tail from word 4
      have hL56 : L = 56 := by
        have : L ≠ 72 := fun h => hc'' (BitVec.eq_of_toNat_eq (by
          simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [g12', g14', h]))
        omega
      refine st_8000580c hlive ?_
      refine st_80005810 hlive ?_
      refine st_80005814 hlive ?_
      refine tail 4 _ (by omega) ?_ ?_ (by pv_keep K3) <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [n32, e _ _ _ g8' (by omega)]
      · rw [K3.t1, n48, e _ _ _ h6 (by omega)]; omega
  · -- 40 bytes: the tail from word 2
    refine st_800056c0 hlive ?_
    refine st_800056c4 hlive ?_
    refine tail 2 _ (by omega) ?_ ?_ (by pv_keep K1) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [n16, e _ _ _ g8 (by omega)]
    · rw [K1.t1, n32, e _ _ _ h6 (by omega)]; omega

end Copy

/-- **The prev+X+next copy through `memmove`** (`0x80005778`): spill `t1`,
`a5`, `a3`, `a6` at `sp`, `memmove(a6, s0, a2)`, reload them and join at
`0x800056e0`. -/
theorem pvN_mm {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {M1 : Mem} {d s n : Nat}
    (A : MMArgs C.S d s n) (F : RFrame C R M1)
    (hslotD : d + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ d)
    (hslotS : s + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ s)
    (h16 : (R 16).toNat = d) (h8 : (R 8).toNat = s) (h12 : (R 12).toNat = n)
    (hk : ∀ R' Mc, RFrame C R' Mc →
      (∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → Mc[a]? = (copyW M1 d s (n / 8))[a]?) →
      (R' 13).toNat = (R 13).toNat → (R' 6).toNat = (R 6).toNat → (R' 15).toNat = (R 15).toNat →
      (R' 16).toNat = (R 16).toNat → R' 9 = R 9 → AW C.live C.S C.Q 0x800056e0#64 R' Mc) :
    AW C.live C.S C.Q 0x80005778#64 R M1 := by
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
  refine st_80005778 O.live (st_8000577c O.live ?_)
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  refine st_80005780 O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n24]; rw [e 24 (by omega)]; exact (st 24 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n24]; rw [e 24 (by omega)]; exact (st 24 (by omega) (by omega)).2) ?_
  refine st_80005784 O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e 16 (by omega)]; exact (st 16 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e 16 (by omega)]; exact (st 16 (by omega) (by omega)).2) ?_
  refine st_80005788 O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e 8 (by omega)]; exact (st 8 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e 8 (by omega)]; exact (st 8 (by omega) (by omega)).2) ?_
  refine st_8000578c O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]; rw [e 0 (by omega)]; exact (st 0 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]; rw [e 0 (by omega)]; exact (st 0 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, n24, n16, n8, n0]
  rw [e 24 (by omega), e 16 (by omega), e 8 (by omega), e 0 (by omega)]
  refine st_80005790 O.live ?_
  simp only [VsaIris.ra]
  generalize hW : writeLog (writeLog (writeLog (writeLog M1 [(C.s.toNat - 64 + 24, 8, R 6)])
    [(C.s.toNat - 64 + 16, 8, R 15)]) [(C.s.toNat - 64 + 8, 8, R 13)]) [(C.s.toNat - 64 + 0, 8, R 16)] = W
  have hWo : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → W[a]? = M1[a]? := fun a ha => by
    rw [← hW, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      simp only [OutL, and_true] <;> omega
  refine memmove_fwd A O.live ?_ ?_ ?_ (by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; decide)
    fun R' hK => ?_ <;> try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [BitVec.add_zero]; exact h16
  · rw [BitVec.add_zero]; exact h8
  · exact h12
  rw [show (BitVec.ofNat 64 (2147506064 + 4) : BitVec 64) = 0x80005794#64 from rfl]
  have hR2 : R' 2 = R 2 := by rw [hK.sp]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  have e' : ∀ c, c < 32 → (R' 2 + BitVec.ofNat 64 c).toNat = C.s.toNat - 64 + c := fun c hc => by
    rw [hR2]; exact e c hc
  have hcpO : ∀ a, C.s.toNat - 64 ≤ a → a < C.s.toNat →
      (copyW W d s (n / 8))[a]? = W[a]? := fun a h1 h2 => copyW_out (by omega)
  have rd : ∀ c (v : BitVec 64), c ≤ 24 → W = writeLog (writeLog (writeLog (writeLog M1
        [(C.s.toNat - 64 + 24, 8, R 6)]) [(C.s.toNat - 64 + 16, 8, R 15)])
        [(C.s.toNat - 64 + 8, 8, R 13)]) [(C.s.toNat - 64 + 0, 8, R 16)] →
      read64 W (C.s.toNat - 64 + c) = some v.toNat →
      ldv .ld (copyW W d s (n / 8)) (C.s.toNat - 64 + c) = v := fun c v hc _ hr =>
    ldv_ld (by rw [read64_keep (m := W) fun k hk => hcpO _ (by omega) (by omega)]; exact hr)
  have r24 : read64 W (C.s.toNat - 64 + 24) = some (R 6).toNat := by
    rw [← hW, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), read64_store_hit]
  have r16 : read64 W (C.s.toNat - 64 + 16) = some (R 15).toNat := by
    rw [← hW, rd_miss (by omega), rd_miss (by omega), read64_store_hit]
  have r8 : read64 W (C.s.toNat - 64 + 8) = some (R 13).toNat := by
    rw [← hW, rd_miss (by omega), read64_store_hit]
  have r0 : read64 W (C.s.toNat - 64 + 0) = some (R 16).toNat := by
    rw [← hW, read64_store_hit]
  refine st_80005794 O.live (by rw [n0, e' 0 (by omega)]; exact (ld 0 (by omega) (by omega)).1)
    (by rw [n0, e' 0 (by omega)]; exact (ld 0 (by omega) (by omega)).2) ?_
  rw [n0, e' 0 (by omega), rd 0 _ (by omega) hW.symm r0]
  refine st_80005798 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e' 8 (by omega)]
        exact (ld 8 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e' 8 (by omega)]
        exact (ld 8 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]
  rw [e' 8 (by omega), rd 8 _ (by omega) hW.symm r8]
  refine st_8000579c O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e' 16 (by omega)]
        exact (ld 16 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e' 16 (by omega)]
        exact (ld 16 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]
  rw [e' 16 (by omega), rd 16 _ (by omega) hW.symm r16]
  refine st_800057a0 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n24]; rw [e' 24 (by omega)]
        exact (ld 24 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n24]; rw [e' 24 (by omega)]
        exact (ld 24 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false, n24]
  rw [e' 24 (by omega), rd 24 _ (by omega) hW.symm r24]
  refine st_800057a4 O.live ?_
  refine hk _ _ ((F.of_regs ?_ ?_ ?_).agree fun a h1 h2 => ?_) (fun a ha => ?_) ?_ ?_ ?_ ?_ ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hR2
  · rw [hK.s2]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  · rw [hK.s3]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  · rw [hcpO a (by omega) (by omega), hWo a (by omega)]
  · exact copyW_agreeOn (Pr := fun a => a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) hWo
      (fun i hi => by omega) a ha
  · rw [hK.s1]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]

/-- **The prev+X+next join** (`0x800056e0`): `s0 := a6`, `a4 := a3`,
`a2 := t1`, then the tail over `pvG_rt`. -/
theorem pvN_join {C : MCtx} {B : RB} (O : ROK C B) {Mt W : Mem} {brkv : Nat}
    {cs₀ rest : List Chunk} {bins : Nat → List Nat} {P ps S' L hdr0 hxv hn nb i : Nat}
    {pre post : List Nat} {predP succP : Nat}
    (I : PvIn C B Mt W brkv cs₀ rest bins P ps S' L hdr0 hxv hn nb i pre post predP succP)
    {R' : Nat → BitVec 64} {Mc : Mem} (F : RFrame C R' Mc)
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (P + ps + 16) (L / 8))[a]?)
    (h16 : (R' 16).toNat = P + 16) (h9 : R' 9 = reentV) (h6 : (R' 6).toNat = P)
    (h13 : (R' 13).toNat = ps + S') (h15 : (R' 15).toNat = nb) :
    AW C.live C.S C.Q 0x800056e0#64 R' Mc := by
  have z : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := rfl
  refine st_800056e0 O.live (st_800056e4 O.live (st_800056e8 O.live (st_800056ec O.live ?_)))
  refine pvG_rt O I (F.of_regs ?_ ?_ ?_) hMc ?_ ?_ ?_ ?_ ?_ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, z, BitVec.add_zero] <;> assumption

/-- **Both neighbours, the predecessor half** (`0x80005684`): with the
successor already unlinked (`NAbs`), unlink `P`, copy the payload down and
join the tail. -/
theorem pvXN_P {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb ns : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₀ cs₃ : List Chunk} {P ps : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: ⟨X + S, ns, false⟩ :: cs₃)
    (hpf : hdr0 % 2 = 0) {bins' : Nat → List Nat} {V : Mem} {hNN pred succ : Nat}
    (N : NAbs C B Mt V brkv (cs₀ ++ [⟨P, ps, false⟩]) cs₃ bins' X S ns hdr0 hNN pred succ)
    (hfit : nb ≤ ps + (S + ns)) {R' : Nat → BitVec 64} (F : RFrame C R' Mt)
    (h6 : (R' 6).toNat = P) (h8 : (R' 8).toNat = X + 16) (h9 : R' 9 = reentV)
    (h12 : (R' 12).toNat = S - 8) (h13 : (R' 13).toNat = ps + (S + ns)) (h15 : (R' 15).toNat = nb)
    (h17 : (R' 17).toNat = 72) :
    AW C.live C.S C.Q 0x80005684#64 R' (unlinkM Mt pred succ) := by
  have Hp := D.heap
  have HB := Hp.heap.heap
  have HH := HB.heap
  have hXm := D.mem
  have hN : (⟨X + S, ns, false⟩ : Chunk) ∈ chunks := by rw [hsp]; simp
  have hXb := HH.walk.chunk_bounds _ hXm
  have hx16 := HH.aligned.1 _ hXm; have hS16 := (walk_sizes HH.walk _ hXm).1
  have hns16 := (walk_sizes HH.walk _ hN).1
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := HB.top_room
  simp only at hXb hx16 hS16 hns16
  unfold heapStart heapEnd at *
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have n24 : (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 := rfl
  -- `P`'s links in the absorbed heap
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  obtain ⟨cs₀', p, psz, i, pre, post, predP, succP, PV⟩ :=
    pv_of_heap (C := C') (cs₁ := cs₀ ++ [⟨P, ps, false⟩]) (rest := cs₃) N.heap N.xW (by omega)
  obtain ⟨hc0, hcP⟩ := List.append_inj' PV.split (by rfl)
  simp only [List.cons.injEq, Chunk.mk.injEq, and_true] at hcP
  obtain ⟨rfl, rfl⟩ := hcP
  subst hc0
  have hpend : X = P + ps := PV.pend.symm
  have hspan := pv_span D hsp hpend
  subst hpend
  have G : PvGeo C' P ps (S + ns) predP succP := PvGeo.of_heap (C := C') N.heap PV
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hxend : P + ps + (S + ns) ≤ C.top0 := G.xend; have htop : C.top0 + 16 ≤ 0x87800000 := G.top
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have hpphi : predP + 32 ≤ C.top0 := G.pphi; have hsphi : succP + 32 ≤ C.top0 := G.sphi
  have hdisj := Hp.disjD
  unfold allocHeadroom at hdisj
  have hPf := (foot_free N.heap.heap (c' := ⟨P, ps, false⟩) (by simp) rfl).1
  simp only at hPf
  have gB : ∀ k, k < 8 → vsaFoot C.H (P + 24 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := hPf (8 + k) (by omega); rwa [show P + 16 + (8 + k) = P + 24 + k by omega] at this)
  have gF : ∀ k, k < 8 → vsaFoot C.H (P + 16 + k) := fun k hk => vsaFoot_cons_sub _ (hPf k (by omega))
  have gS : ∀ k, k < 8 → vsaFoot C.H (succP + 24 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := G.spfoot (24 + k) (by omega) (by omega)
    rwa [show succP + (24 + k) = succP + 24 + k by omega] at this)
  have gP : ∀ k, k < 8 → vsaFoot C.H (predP + 16 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := G.ppfoot (16 + k) (by omega) (by omega)
    rwa [show predP + (16 + k) = predP + 16 + k by omega] at this)
  have hbk : read64 (unlinkM Mt pred succ) (P + 24) = some predP := by
    rw [read64_keep (m := V) fun k hk => N.agree _ (by omega) (by omega)]; exact PV.bk
  have hfd : read64 (unlinkM Mt pred succ) (P + 16) = some succP := by
    rw [read64_keep (m := V) fun k hk => N.agree _ (by omega) (by omega)]; exact PV.fd
  have hpl2 := Vsa.Sim.read64_lt _ _ _ PV.bk
  have hsl2 := Vsa.Sim.read64_lt _ _ _ PV.fd
  have hvP2 : (BitVec.ofNat 64 predP).toNat = predP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl2]
  have hvS2 : (BitVec.ofNat 64 succP).toNat = succP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl2]
  have eB : (R' 6 + sign_extend (m := 64) (0x018#12)).toNat = P + 24 := by rw [n24, addr_add h6 24 (by omega)]
  have eF : (R' 6 + sign_extend (m := 64) (0x010#12)).toNat = P + 16 := by rw [n16, addr_add h6 16 (by omega)]
  have eS2 : (BitVec.ofNat 64 succP + sign_extend (m := 64) (0x018#12)).toNat = succP + 24 := by
    rw [n24, addr_add hvS2 24 (by omega)]
  have eP2 : (BitVec.ofNat 64 predP + sign_extend (m := 64) (0x010#12)).toNat = predP + 16 := by
    rw [n16, addr_add hvP2 16 (by omega)]
  -- unlink `P`
  refine st_80005684 O.live (by rw [eB]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [eB]; exact O.foot gB) ?_
  rw [eB, ldv_at hbk _ rfl]
  refine st_80005688 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eF]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eF]; exact O.foot gF) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [eF, ldv_at hfd _ rfl]
  refine st_8000568c O.live ?_
  refine st_80005690 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eS2]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eS2]; exact O.foot gS) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eS2]
  refine st_80005694 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eP2]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eP2]; exact O.foot gP) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eP2]
  -- the tail's state, the frame, the copy's arguments
  have hsz8 : B.nOld + 8 ≤ S := by
    obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
    have := HH.chunk_eq hc0 hXm (by have := D.addr; simp only at hc0a ⊢; omega)
    subst this; simpa using hc0n
  have I : PvIn C B (unlinkM Mt pred succ) V brkv cs₀ cs₃ bins' P ps (S + ns)
      (S - 8) hdr0 (S + ns + hdr0 % 2) hNN nb i pre post predP succP :=
    { heap := N.heap, starts := Hp.starts, addr := D.addr, pv := PV, xW := N.xW, xM := N.xM,
      nM := by rw [show P + ps + (S + ns) + 8 = P + ps + S + ns + 8 by omega]; exact N.nM,
      nW := by rw [show P + ps + (S + ns) + 8 = P + ps + S + ns + 8 by omega]; exact N.nW,
      agree := fun a h1 h2 => N.agree a h1 (by omega), pres := N.pres, disj := Hp.disj,
      disjD := Hp.disjD, data := N.data, grow := Hp.grow, nbok := D.nbok, fit := hfit,
      L8 := by omega, Lold := by omega, Lle := by omega }
  have oS := off_stack_of Hp.disj gS
  have oP := off_stack_of Hp.disj gP
  have F1 : RFrame C R' (unlinkM (unlinkM Mt pred succ) predP succP) :=
    ((N.frame R' F).store (by omega)).store (by omega)
  have hstk : ∀ a, vsaFoot C.H a → a < C.s.toNat - 512 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => hdisj a (by omega) (by omega) ha
  have hlo2 := O.spA.lo
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo2
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
  refine st_80005698 O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc ⊢ <;> rw [h17, h12] at hc
  · -- over 72 bytes: `memmove`
    refine pvN_mm O { A with n32 := by omega } (F1.of_regs ?_ ?_ ?_) hdst hsrc ?_ ?_ ?_
      (fun R'' Mc F' hMc g13 g6 g15 g16 g9 => pvN_join O I F' hMc ?_ ?_ ?_ ?_ ?_) <;>
      (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · exact eF
    · exact h8
    · exact h12
    · rw [g16]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact eF
    · rw [g9]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h9
    · rw [g6]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h6
    · rw [g13]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h13
    · rw [g15]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h15
  · -- up to 72 bytes: inline
    have hLs : S - 8 = 24 ∨ S - 8 = 40 ∨ S - 8 = 56 ∨ S - 8 = 72 := by omega
    refine pvN_inline A O.live hLs rfl ?_ ?_ ?_ ?_ fun R'' K => pvN_join O I
      ((F1.of_regs ?_ ?_ ?_).agree fun a h1 h2 => ?_) (fun a _ => rfl) ?_ ?_ ?_ ?_ ?_ <;>
      (try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false])
    · exact h8
    · exact h6
    · exact eF
    · exact h12
    · rw [K.sp]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [K.s2]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [K.s3]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact copyW_out (by omega)
    · rw [K.a6]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact eF
    · rw [K.s1]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h9
    · rw [K.t1]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h6
    · rw [K.a3]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h13
    · rw [K.a5]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h15

/-- **Into both free neighbours** (`0x8000566c`): unlink the successor `N`
(`next_absorb`) and the predecessor `P`, copy the payload down to `P + 16`
(inline up to 72 bytes, else `memmove`), and join the tail with the chunk
`P` of `ps + S + ns` bytes. -/
theorem realloc_pvXN {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb ns : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) {cs₀ cs₃ : List Chunk} {P ps : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ ⟨X, S, true⟩ :: ⟨X + S, ns, false⟩ :: cs₃)
    (hpf : hdr0 % 2 = 0) {iN : Nat} {preN postN : List Nat} {pred succ : Nat}
    (FB : FreeBinAt Mt bins (X + S) iN preN postN pred succ)
    (hfit : nb ≤ ps + (S + ns)) (h6 : (R 6).toNat = P) (h13 : (R 13).toNat = ps + (S + ns))
    (h16 : (R 16).toNat = X + S) :
    AW C.live C.S C.Q 0x8000566c#64 R Mt := by
  have Hp := D.heap
  have HB := Hp.heap.heap
  have HH := HB.heap
  have hXm := D.mem
  have hN : (⟨X + S, ns, false⟩ : Chunk) ∈ chunks := by rw [hsp]; simp
  have hXb := HH.walk.chunk_bounds _ hXm; have hNb := HH.walk.chunk_bounds _ hN
  have hx16 := HH.aligned.1 _ hXm; have hS16 := (walk_sizes HH.walk _ hXm).1
  have hns16 := (walk_sizes HH.walk _ hN).1
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := HB.top_room
  simp only at hXb hNb hx16 hS16 hns16
  unfold heapStart heapEnd at *
  -- `N`'s links
  have hpn := FB.pred_node; have hsn := FB.succ_node
  obtain ⟨hp16, hpnode⟩ := HH.node FB.i0 FB.i1 hpn
  obtain ⟨hs16, hsnode⟩ := HH.node FB.i0 FB.i1 hsn
  have hpf' := Hp.heap.heap.node_foot FB.i0 FB.i1 hpn
  have hsf' := Hp.heap.heap.node_foot FB.i0 FB.i1 hsn
  have hloc : ∀ z, (z = binAt iN ∨ ∃ cx ∈ chunks, cx.addr = z ∧ cx.inuse = false ∧ z ∈ bins iN) →
      0x8001ad20 ≤ z ∧ z + 32 ≤ C.top0 := by
    rintro z (rfl | ⟨cx, hcx, rfl, _, _⟩)
    · have := binAt_geo iN FB.i1; have := HH.walk.le; have := FB.i0
      unfold binAt avAddr heapStart at *; omega
    · have := HH.walk.chunk_bounds cx hcx; unfold heapStart at this; omega
  obtain ⟨hplo, hphi⟩ := hloc _ hpnode
  obtain ⟨hslo, hshi⟩ := hloc _ hsnode
  have fS : ∀ k, k < 8 → vsaFoot C.H (succ + 24 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := hsf' (24 + k) (by omega) (by omega); rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
  have fP : ∀ k, k < 8 → vsaFoot C.H (pred + 16 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := hpf' (16 + k) (by omega) (by omega); rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
  have hNf := (foot_free HB hN rfl).1
  simp only at hNf
  have fNB : ∀ k, k < 8 → vsaFoot C.H (X + S + 24 + k) := fun k hk => vsaFoot_cons_sub _ (by
    have := hNf (8 + k) (by omega); rwa [show X + S + 16 + (8 + k) = X + S + 24 + k by omega] at this)
  have fNF : ∀ k, k < 8 → vsaFoot C.H (X + S + 16 + k) := fun k hk => vsaFoot_cons_sub _ (hNf k (by omega))
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hpl := Vsa.Sim.read64_lt _ _ _ FB.bk
  have hsl := Vsa.Sim.read64_lt _ _ _ FB.fd
  have hvP : (BitVec.ofNat 64 pred).toNat = pred := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hvS : (BitVec.ofNat 64 succ).toNat = succ := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have n24 : (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 := rfl
  have eNB : (R 16 + sign_extend (m := 64) (0x018#12)).toNat = X + S + 24 := by
    rw [n24, addr_add h16 24 (by omega)]
  have eNF : (R 16 + sign_extend (m := 64) (0x010#12)).toNat = X + S + 16 := by
    rw [n16, addr_add h16 16 (by omega)]
  have eS : (BitVec.ofNat 64 succ + sign_extend (m := 64) (0x018#12)).toNat = succ + 24 := by
    rw [n24, addr_add hvS 24 (by omega)]
  have eP : (BitVec.ofNat 64 pred + sign_extend (m := 64) (0x010#12)).toNat = pred + 16 := by
    rw [n16, addr_add hvP 16 (by omega)]
  -- unlink `N`
  refine st_8000566c O.live (by rw [eNB]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [eNB]; exact O.foot fNB) ?_
  rw [eNB, ldv_at FB.bk _ rfl]
  refine st_80005670 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eNF]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eNF]; exact O.foot fNF) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [eNF, ldv_at FB.fd _ rfl]
  have eL : (R 14 + sign_extend (m := 64) (0xff8#12)).toNat = S - 8 := by
    rw [show (sign_extend (m := 64) (0xff8#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl,
      addr_sub D.a4 8 (by omega) (by omega)]
  refine st_80005674 O.live (st_80005678 O.live ?_)
  refine st_8000567c O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eS]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eS]; exact O.foot fS) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eS]
  refine st_80005680 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eP]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eP]; exact O.foot fP) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eP]
  obtain ⟨V, hNN, N⟩ := next_absorb O D hsp FB
  refine pvXN_P O D hsp hpf N hfit (D.frame.of_regs ?_ ?_ ?_) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact h6
  · exact D.s0
  · exact D.s1
  · exact eL
  · exact h13
  · exact D.a5
  · rfl

end VsaIris.VsaHeap
