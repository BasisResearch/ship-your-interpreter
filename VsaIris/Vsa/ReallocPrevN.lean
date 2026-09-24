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

end VsaIris.VsaHeap
