import VsaIris.Vsa.ReallocPrevN

/-!
# `_realloc_r` into a free predecessor and the top

The old chunk ends at the top and its free predecessor, with the top, holds
the request and `MINSIZE` more: unlink `P`, copy the payload down to `P + 16`
(`pvT_inline` or `memmove_fwd`), and move the top to `P + nb`
(`PHeapAt.setTop`, growing or shrinking `P`'s merged chunk).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section Copy

variable {live : Nat → Prop} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- The three-word tail of the prev+X+top copy (`0x8000555c`): words
`j … j+2` from `s0` to `a4`. -/
theorem pvT_tail3 {M0 : Mem} {d s L : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    {R0 R : Nat → BitVec 64} {j : Nat} (h8 : (R 8).toNat = s + 8 * j) (h14 : (R 14).toNat = d + 8 * j)
    (hj : 8 * j + 24 ≤ L) (K : PVKeep R0 R)
    (hk : ∀ R', PVKeep R0 R' → AW live S Q 0x80005574#64 R' (copyW M0 d s (j + 3))) :
    AW live S Q 0x8000555c#64 R (copyW M0 d s j) := by
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
  have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * j) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * j) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 8) (rD := 14) (by decide) (st_8000555c hlive) (st_80005560 hlive)
    (by rw [n0, addr_add h8 0 (by omega)]; omega) (by rw [n0, addr_add h14 0 (by omega)]; omega)
    l1 l2 s1 s2 ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * (j + 1)) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * (j + 1)) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 8) (rD := 14) (by decide) (st_80005564 hlive) (st_80005568 hlive)
    (by rw [upd_other _ _ (by decide), n8, addr_add h8 8 (by omega)]; omega)
    (by rw [upd_other _ _ (by decide), n8, addr_add h14 8 (by omega)]; omega) l1 l2 s1 s2 ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * (j + 2)) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * (j + 2)) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 8) (rD := 14) (by decide) (st_8000556c hlive) (st_80005570 hlive)
    (by rw [upd_other _ _ (by decide), upd_other _ _ (by decide), n16, addr_add h8 16 (by omega)]; omega)
    (by rw [upd_other _ _ (by decide), upd_other _ _ (by decide), n16, addr_add h14 16 (by omega)]; omega)
    l1 l2 s1 s2 ?_
  exact hk _ (by pv_keep K)

/-- The prev+X+top path's inline copy (`0x80005530`, a payload of 24,
40, 56 or 72 bytes, from `s0` to `t1 + 16`). -/
theorem pvT_inline {M0 : Mem} {d s L P : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    (hL : L = 24 ∨ L = 40 ∨ L = 56 ∨ L = 72) (hP : P + 16 = d)
    {R : Nat → BitVec 64} (h8 : (R 8).toNat = s) (h6 : (R 6).toNat = P) (h13 : (R 13).toNat = d)
    (h12 : (R 12).toNat = L)
    (hk : ∀ R', PVKeep R R' → AW live S Q 0x80005574#64 R' (copyW M0 d s (L / 8))) :
    AW live S Q 0x80005530#64 R (copyW M0 d s 0) := by
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
      (R' 14).toNat = d + 8 * j → PVKeep R R' → AW live S Q 0x8000555c#64 R' (copyW M0 d s j) :=
    fun j R' hj g8 g14 K => pvT_tail3 A hlive g8 g14 (by omega) K fun R'' K' => by rw [hj]; exact hk R'' K'
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
  refine st_80005530 hlive ?_
  refine st_80005534 hlive ?_
  refine st_80005538 hlive (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x027#12) : BitVec 64).toNat = 39 from rfl] at hc
  · -- 24 bytes: the tail alone
    refine tail 0 _ (by omega) ?_ ?_ (by pv_keep (PVKeep.refl R)) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [h8]; rfl
    · rw [n0, e _ _ _ h13 (by omega)]
  -- 40, 56 or 72 bytes: word 0, with `li a4,55` before its store
  refine aw_forget (fun R0 => PVKeep R R0 ∧ (R0 8).toNat = s ∧ (R0 12).toNat = L)
    ⟨by pv_keep (PVKeep.refl R), by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h8,
      by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h12⟩ fun R0 ⟨K0, g8, g12⟩ => ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 0) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 0) (by omega) (by omega) (by omega)
  have e0 : (R0 8 + sign_extend (m := 64) (0x000#12)).toNat = s + 8 * 0 := by rw [n0, e _ _ _ g8 (by omega)]
  refine st_8000553c hlive (by rw [e0]; exact l1) (by rw [e0]; exact l2) ?_
  rw [e0]
  refine st_80005540 hlive ?_
  have f0 : ((upd (upd R0 11 (ldv .ld (copyW M0 d s 0) (s + 8 * 0))) 14
      (0#64 + sign_extend (m := 64) (0x037#12))) 6 + sign_extend (m := 64) (0x010#12)).toNat =
      d + 8 * 0 := by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K0.t1, n16, e _ _ _ h6 (by omega)]; omega
  refine st_80005544 hlive (by rw [f0]; exact s1) (by rw [f0]; exact s2) ?_
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
    (st_80005548 hlive) (st_8000554c hlive) K1 g8 fun v => ?_
  refine st_80005550 hlive (fun hc' => ?_) (fun hc' => ?_) <;>
    rw [upd_other _ _ (by decide), upd_other _ _ (by decide), g14, g12] at hc'
  · -- 56 or 72 bytes: word 2, with `li a4,72` before its store, and word 3
    have K2 := K1.upd v (k := 11) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 2) (by omega) (by omega)
    obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 2) (by omega) (by omega) (by omega)
    have e2 : (upd R1 11 v 8 + sign_extend (m := 64) (0x010#12)).toNat = s + 8 * 2 := by
      rw [upd_other _ _ (by decide), n16, e _ _ _ g8 (by omega)]
    refine st_80005864 hlive (by rw [e2]; exact l1) (by rw [e2]; exact l2) ?_
    rw [e2]
    refine st_80005868 hlive ?_
    have f2 : ((upd (upd (upd R1 11 v) 11 (ldv .ld (copyW M0 d s 2) (s + 8 * 2))) 14
        (0#64 + sign_extend (m := 64) (0x048#12))) 6 + sign_extend (m := 64) (0x020#12)).toNat =
        d + 8 * 2 := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K1.t1, n32, e _ _ _ h6 (by omega)]; omega
    refine st_8000586c hlive (by rw [f2]; exact s1) (by rw [f2]; exact s2) ?_
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
      (st_80005870 hlive) (st_80005874 hlive) K3 g8' fun v3 => ?_
    refine st_80005878 hlive (fun hc'' => ?_) (fun hc'' => ?_)
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
      refine st_800058a4 hlive (by rw [e4]; exact l1) (by rw [e4]; exact l2) ?_
      rw [e4]
      refine st_800058a8 hlive ?_
      refine st_800058ac hlive ?_
      have f4 : ((upd (upd (upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 14
          ((upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 6 + sign_extend (m := 64) (0x040#12))) 8
          ((upd (upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 14
            ((upd R2 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 6 + sign_extend (m := 64) (0x040#12))) 8 +
            sign_extend (m := 64) (0x030#12))) 6 + sign_extend (m := 64) (0x030#12)).toNat = d + 8 * 4 := by
        simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K4.t1, n48, e _ _ _ h6 (by omega)]; omega
      refine st_800058b0 hlive (by rw [f4]; exact s1) (by rw [f4]; exact s2) ?_
      rw [f4]
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [← copyW_succ]
      obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 5) (by omega) (by omega)
      obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 5) (by omega) (by omega) (by omega)
      have g8' : (R2 8 + sign_extend (m := 64) (0x030#12)).toNat = s + 48 := by
        rw [n48, e _ _ _ h8' (by omega)]
      refine cp_pair (rT := 12) (rS := 8) (rD := 6) (by decide) (st_800058b4 hlive) (st_800058b8 hlive)
        ?_ ?_ l1 l2 s1 s2 ?_
      · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [nm8, addr_sub g8' 8 (by omega) (by omega)]; omega
      · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K4.t1, n56, e _ _ _ h6 (by omega)]; omega
      refine st_800058bc hlive ?_
      refine tail 6 _ (by omega) ?_ ?_ (by pv_keep K4) <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [g8']
      · rw [K4.t1, n64, e _ _ _ h6 (by omega)]; omega
    · -- 56 bytes: the tail from word 4
      have hL56 : L = 56 := by
        have : L ≠ 72 := fun h => hc'' (BitVec.eq_of_toNat_eq (by
          simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [g12', g14', h]))
        omega
      refine st_8000587c hlive ?_
      refine st_80005880 hlive ?_
      refine st_80005884 hlive ?_
      refine tail 4 _ (by omega) ?_ ?_ (by pv_keep K3) <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [n32, e _ _ _ g8' (by omega)]
      · rw [K3.t1, n48, e _ _ _ h6 (by omega)]; omega
  · -- 40 bytes: the tail from word 2
    refine st_80005554 hlive ?_
    refine st_80005558 hlive ?_
    refine tail 2 _ (by omega) ?_ ?_ (by pv_keep K1) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [n16, e _ _ _ g8 (by omega)]
    · rw [K1.t1, n32, e _ _ _ h6 (by omega)]; omega

end Copy

/-- **The prev+X+top copy through `memmove`** (`0x80005818`): spill `t1`,
`a5`, `a6`, `a3` at `sp`, `memmove(a3, s0, a2)`, reload them and join at
`0x80005574`. -/
theorem pvT_mm {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {M1 : Mem} {d s n : Nat}
    (A : MMArgs C.S d s n) (F : RFrame C R M1)
    (hslotD : d + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ d)
    (hslotS : s + n ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ s)
    (h13 : (R 13).toNat = d) (h8 : (R 8).toNat = s) (h12 : (R 12).toNat = n)
    (hk : ∀ R' Mc, RFrame C R' Mc →
      (∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → Mc[a]? = (copyW M1 d s (n / 8))[a]?) →
      (R' 13).toNat = (R 13).toNat → (R' 6).toNat = (R 6).toNat → (R' 15).toNat = (R 15).toNat →
      (R' 16).toNat = (R 16).toNat → R' 9 = R 9 → AW C.live C.S C.Q 0x80005574#64 R' Mc) :
    AW C.live C.S C.Q 0x80005818#64 R M1 := by
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
  refine st_80005818 O.live (st_8000581c O.live ?_)
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  refine st_80005820 O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n24]; rw [e 24 (by omega)]; exact (st 24 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n24]; rw [e 24 (by omega)]; exact (st 24 (by omega) (by omega)).2) ?_
  refine st_80005824 O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e 16 (by omega)]; exact (st 16 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e 16 (by omega)]; exact (st 16 (by omega) (by omega)).2) ?_
  refine st_80005828 O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e 8 (by omega)]; exact (st 8 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e 8 (by omega)]; exact (st 8 (by omega) (by omega)).2) ?_
  refine st_8000582c O.live (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]; rw [e 0 (by omega)]; exact (st 0 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]; rw [e 0 (by omega)]; exact (st 0 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, n24, n16, n8, n0]
  rw [e 24 (by omega), e 16 (by omega), e 8 (by omega), e 0 (by omega)]
  refine st_80005830 O.live ?_
  simp only [VsaIris.ra]
  generalize hW : writeLog (writeLog (writeLog (writeLog M1 [(C.s.toNat - 64 + 24, 8, R 6)])
    [(C.s.toNat - 64 + 16, 8, R 15)]) [(C.s.toNat - 64 + 8, 8, R 16)]) [(C.s.toNat - 64 + 0, 8, R 13)] = W
  have hWo : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) → W[a]? = M1[a]? := fun a ha => by
    rw [← hW, writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;>
      simp only [OutL, and_true] <;> omega
  refine memmove_fwd A O.live ?_ ?_ ?_ (by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; decide)
    fun R' hK => ?_ <;> try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [BitVec.add_zero]; exact h13
  · rw [BitVec.add_zero]; exact h8
  · exact h12
  rw [show (BitVec.ofNat 64 (2147506224 + 4) : BitVec 64) = 0x80005834#64 from rfl]
  have hR2 : R' 2 = R 2 := by rw [hK.sp]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  have e' : ∀ c, c < 32 → (R' 2 + BitVec.ofNat 64 c).toNat = C.s.toNat - 64 + c := fun c hc => by
    rw [hR2]; exact e c hc
  have hcpO : ∀ a, C.s.toNat - 64 ≤ a → a < C.s.toNat →
      (copyW W d s (n / 8))[a]? = W[a]? := fun a h1 h2 => copyW_out (by omega)
  have rd : ∀ c (v : BitVec 64), c ≤ 24 → W = writeLog (writeLog (writeLog (writeLog M1
        [(C.s.toNat - 64 + 24, 8, R 6)]) [(C.s.toNat - 64 + 16, 8, R 15)])
        [(C.s.toNat - 64 + 8, 8, R 16)]) [(C.s.toNat - 64 + 0, 8, R 13)] →
      read64 W (C.s.toNat - 64 + c) = some v.toNat →
      ldv .ld (copyW W d s (n / 8)) (C.s.toNat - 64 + c) = v := fun c v hc _ hr =>
    ldv_ld (by rw [read64_keep (m := W) fun k hk => hcpO _ (by omega) (by omega)]; exact hr)
  have r24 : read64 W (C.s.toNat - 64 + 24) = some (R 6).toNat := by
    rw [← hW, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega), read64_store_hit]
  have r16 : read64 W (C.s.toNat - 64 + 16) = some (R 15).toNat := by
    rw [← hW, rd_miss (by omega), rd_miss (by omega), read64_store_hit]
  have r8 : read64 W (C.s.toNat - 64 + 8) = some (R 16).toNat := by
    rw [← hW, rd_miss (by omega), read64_store_hit]
  have r0 : read64 W (C.s.toNat - 64 + 0) = some (R 13).toNat := by
    rw [← hW, read64_store_hit]
  refine st_80005834 O.live (by rw [n24, e' 24 (by omega)]; exact (ld 24 (by omega) (by omega)).1)
    (by rw [n24, e' 24 (by omega)]; exact (ld 24 (by omega) (by omega)).2) ?_
  rw [n24, e' 24 (by omega), rd 24 _ (by omega) hW.symm r24]
  refine st_80005838 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e' 16 (by omega)]
        exact (ld 16 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]; rw [e' 16 (by omega)]
        exact (ld 16 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false, n16]
  rw [e' 16 (by omega), rd 16 _ (by omega) hW.symm r16]
  refine st_8000583c O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e' 8 (by omega)]
        exact (ld 8 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]; rw [e' 8 (by omega)]
        exact (ld 8 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false, n8]
  rw [e' 8 (by omega), rd 8 _ (by omega) hW.symm r8]
  refine st_80005840 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]; rw [e' 0 (by omega)]
        exact (ld 0 (by omega) (by omega)).1)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]; rw [e' 0 (by omega)]
        exact (ld 0 (by omega) (by omega)).2) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false, n0]
  rw [e' 0 (by omega), rd 0 _ (by omega) hW.symm r0]
  refine st_80005844 O.live ?_
  refine hk _ _ ((F.of_regs ?_ ?_ ?_).agree fun a h1 h2 => ?_) (fun a ha => ?_) ?_ ?_ ?_ ?_ ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hR2
  · rw [hK.s2]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  · rw [hK.s3]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  · rw [hcpO a (by omega) (by omega), hWo a (by omega)]
  · exact copyW_agreeOn (Pr := fun a => a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) hWo
      (fun i hi => by omega) a ha
  · rw [hK.s1]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]

/-- The machine memory after unlinking the free predecessor `P` agrees with
the coalesced virtual heap `coalW` over the same memory off `P`'s header. -/
theorem pv_agree_self {C : MCtx} {Mt : Mem} {P ps S hdr0 predP succP : Nat}
    (G : PvGeo C P ps S predP succP) (hdr : read64 Mt (P + ps + 8) = some hdr0)
    {v1 v2 : BitVec 64} (h1 : v1.toNat = predP) (h2 : v2.toNat = succP) :
    ∀ w0, ¬ (P + 8 ≤ w0 ∧ w0 < P + 16) →
      (writeLog (writeLog Mt [(succP + 24, 8, v1)]) [(predP + 16, 8, v2)])[w0]? =
      (coalW Mt P ps S hdr0 hdr0 predP succP)[w0]? := by
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  intro w0 h1'
  refine agree_of_words (P := fun x => ¬ (P + 8 ≤ x ∧ x < P + 16))
    [succP + 24, predP + 16, P + ps + 8] (fun w' hw' => ?_) (fun x hx hout => ?_) w0 h1'
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

/-- What the prev+X+top path hands `_realloc_r`'s return: the heap with `P`
of `nb` bytes before the top at `P + nb`, the new block at `P + 16` holding
the old contents. -/
structure PvTRet (C : MCtx) (B : RB) (Mf : Mem) (P nb brkv : Nat) (cs₀ : List Chunk)
    (bins : Nat → List Nat) : Prop where
  heap : PHeapAt Mf ((P + 16, C.n.toNat) :: C.H) (P + nb) brkv (cs₀ ++ [⟨P, nb, true⟩]) bins
  starts : Starts ((P + 16, C.n.toNat) :: C.H)
  top_le : P + nb ≤ C.top0 + physSize C.n.toNat
  pres : ∀ a, vsaFoot C.H a → (Mf[a]?).isSome
  data : ∀ k, k < B.nOld → Mf[P + 16 + k]? = some (B.old (B.p + k))
  align : (P + 16) % 16 = 0

/-- **The heap of the prev+X+top path**: `P` absorbs the old chunk
(`coalPrev`), the payload is copied down, and `P` takes `nb` bytes with the top
right after it (`setTop`); the machine memory, with the stack spill at `sp`,
agrees with that heap on the footprint. -/
theorem pvT_heap {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨X, S, true⟩])
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hXt : X + S = C.top0) (hroom : nb + 32 ≤ ps + S + (brkv - C.top0))
    {Mc : Mem}
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (X + 16) ((S - 8) / 8))[a]?)
    {vT vH vS vP : BitVec 64} (hvT : vT.toNat = P + nb)
    (hvH : vH.toNat = ps + S + (brkv - C.top0) - nb + 1) (hvP : vP.toNat = nb + 1) :
    PvTRet C B (writeLog (writeLog (writeLog (writeLog Mc [(0x8001ad20, 8, vT)])
      [(P + nb + 8, 8, vH)]) [(C.s.toNat - 64, 8, vS)]) [(P + 8, 8, vP)]) P nb brkv cs₀
      (updBins bins i (pre ++ post)) := by
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  have HH := H0.heap.heap
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  have G : PvGeo C' P ps S predP succP := PvGeo.of_heap (C := C') (rest := []) H0 PV
  have hpend : X = P + ps := PV.pend.symm
  have hspan := pv_span D (rest := []) hsp hpend
  subst hpend
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hs16 := G.sz16; have hs32 := G.sz32
  have htop : C.top0 + 16 ≤ 0x87800000 := G.top
  have hpp16 := G.pp16; have hsp16 := G.sp16; have hpplo := G.pplo; have hsplo := G.splo
  have hpphi : predP + 32 ≤ C.top0 := G.pphi; have hsphi : succP + 32 ≤ C.top0 := G.sphi
  have sP := G.sP; have sX := G.sX; have pP := G.pP; have pX := G.pX
  have haddr := D.addr
  have hnb := D.nbok.eq
  have hnbv : C.n.toNat + 8 ≤ nb ∧ nb % 16 = 0 ∧ 32 ≤ nb := by rw [hnb]; unfold physSize; omega
  have hlt := D.lt
  have hbrk := HH.brk_le; have hroom0 := H0.heap.top_room
  unfold heapEnd at hbrk
  obtain ⟨ts, rfl⟩ : ∃ ts, brkv = C.top0 + ts := ⟨brkv - C.top0, by omega⟩
  rw [Nat.add_sub_cancel_left] at hroom hvH
  have hlo := O.spA.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hdisj := Hp.disjD
  unfold allocHeadroom at hdisj
  have hstk : ∀ a, vsaFoot C.H a → a < C.s.toNat - 512 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => hdisj a (by omega) (by omega) ha
  -- the bin nodes around `P`
  have hXm : (⟨P + ps, S, true⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨P + ps, S, true⟩] := by simp
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
  -- the old payload's bytes are no node word
  have hnd : ∀ a, P + ps ≤ a → a < P + ps + S + 8 →
      (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)])[a]? = Mt[a]? := fun a h1 h2 => by
    have n1 := node_off_inuse HH PV.i1 hsnode hXm rfl a h1 h2
    have n2 := node_off_inuse HH PV.i1 hpnode hXm rfl a h1 h2
    rw [writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  clear hpnode hsnode hpm hsm
  -- the virtual heap: coalesce, a block over the copy, the copy, `P` resized, the request's block
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
  have Hc := Hd.coalPrev (cs₂ := []) (b := S) hnoX PV.i0 PV.i1 PV.bin PV.hpred PV.hsucc D.hdr
    (h' := ps + S + 1) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      have := PV.prev h0 hr; unfold prevInuse; rw [show (ps + S + 1) % 2 = 1 by omega, this])
    (BitVec.ofNat 64 hdr0)
  have hPm : (⟨P, ps + S, true⟩ : Chunk) ∈ cs₀ ++ [⟨P, ps + S, true⟩] := by simp
  have Ha := Hc.addBlock (q := P + 16) (n := S - 8) hPm rfl rfl (by simp only; omega)
  generalize hV : copyW (coalW Mt P ps S hdr0 hdr0 predP succP) (P + 16) (P + ps + 16) ((S - 8) / 8) = V
  have hLw : 8 * ((S - 8) / 8) = S - 8 := by omega
  have HV : PHeapAt V ((P + 16, S - 8) :: C.H) C.top0 (C.top0 + ts) (cs₀ ++ [⟨P, ps + S, true⟩])
      (updBins bins i (pre ++ post)) := by
    refine Ha.transport_read fun a ha => ?_
    rw [← hV]
    refine (copyW_out ?_).symm
    rcases ha.1 with hg | ⟨_, _, h3⟩
    · have := allocGlobal_off_arena _ hg; unfold heapStart heapEnd at this; omega
    · have := h3 _ List.mem_cons_self; unfold InExt at this; simp only at this; omega
  have hVP : read64 V (P + 8) = some (ps + S + 1) := by
    rw [← hV, read64_keep (m := coalW Mt P ps S hdr0 hdr0 predP succP) fun k hk => copyW_out (by omega),
      rd_miss (by omega), read64_store_hit, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hPno : ∀ e ∈ C.H, e.1 ≠ P + 16 := fun e he heq => by
    have he' : e ∈ (B.p, B.nOld) :: C.H := List.mem_cons_of_mem _ he
    obtain ⟨c0, hc0, hu, hc0a, _⟩ := HH.exact e he' he'
    have := HH.chunk_eq hc0 (show (⟨P, ps, false⟩ : Chunk) ∈
      (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨P + ps, S, true⟩] by simp) (by simp only; omega)
    rw [this] at hu; cases hu
  have HcH := Hc.heap.heap
  have hfit : ∀ e ∈ (P + 16, S - 8) :: C.H, P + 16 ≤ e.1 → e.1 + e.2 ≤ P + (ps + S) + 8 →
      e.1 + e.2 ≤ P + nb + 8 := by
    intro e he h1 h2
    rcases List.mem_cons.mp he with rfl | he
    · simp only; omega
    obtain ⟨c, hc, _, hca, hcn⟩ := HcH.exact e he he
    rcases HcH.walk.chunk_sep c hc _ hPm with rfl | h3 | h3
    · exact absurd (by simp only at hca; omega) (hPno e he)
    · simp only at h3; omega
    · have := HcH.walk.chunk_bounds c hc; simp only at h3 this; omega
  generalize hV3 : writeLog (writeLog (writeLog V [(0x8001ad20, 8, vT)]) [(P + nb + 8, 8, vH)])
    [(P + 8, 8, vP)] = V3
  have HG := HV.setTop (m' := V3) (x := P) (a := ps + S) (a' := nb) hnbv.2.1 hnbv.2.2 (by omega)
    (h' := nb + 1) (by rw [← hV3, read64_store_hit, hvP]) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      rw [hVP] at hr; cases hr; unfold prevInuse
      rw [show (nb + 1) % 2 = 1 by omega, show (ps + S + 1) % 2 = 1 by omega])
    (by rw [← hV3]; unfold topAddr avAddr; rw [rd_miss (by omega), rd_miss (by omega), read64_store_hit, hvT])
    (by rw [← hV3, rd_miss (by omega), read64_store_hit, hvH]; congr 1; omega)
    (fun w hw h1 h2 h3 => by
      unfold topAddr avAddr at h2
      rw [← hV3, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega)
    hfit
  have Hr2 := HG.reblock (c := ⟨P, nb, true⟩) (by simp) rfl rfl (n' := C.n.toNat) (by simp only; omega)
  -- the machine memory
  have hpl := Vsa.Sim.read64_lt _ _ _ PV.bk
  have hsl := Vsa.Sim.read64_lt _ _ _ PV.fd
  have hv1 : (BitVec.ofNat 64 predP).toNat = predP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpl]
  have hv2 : (BitVec.ofNat 64 succP).toNat = succP := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsl]
  generalize hM1 : writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
    [(predP + 16, 8, BitVec.ofNat 64 succP)] = M1 at hMc hnd
  have hag1 : ∀ w, ¬ (P + 8 ≤ w ∧ w < P + 16) → M1[w]? = (coalW Mt P ps S hdr0 hdr0 predP succP)[w]? :=
    fun w h => by rw [← hM1]; exact pv_agree_self G D.hdr hv1 hv2 w h
  have hMV : ∀ a, vsaFoot C.H a → ¬ (P + 8 ≤ a ∧ a < P + 16) → Mc[a]? = V[a]? := fun a ha h => by
    rw [hMc a (by have := hstk a ha; omega), ← hV]
    exact copyW_agreeOn (Pr := fun a => ¬ (P + 8 ≤ a ∧ a < P + 16)) (fun a h => hag1 a h)
      (fun i hi => by omega) a h
  have hpres1 : ∀ a, vsaFoot C.H a → (M1[a]?).isSome := fun a ha => by
    rw [← hM1]; exact writeLog_present _ _ _ (writeLog_present _ _ _ (Hp.pres a ha))
  have hsz8 : B.nOld + 8 ≤ S := by
    obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
    have := HH.chunk_eq hc0 hXm (by simp only at hc0a ⊢; omega)
    subst this; simpa using hc0n
  refine ⟨Hr2.transport_read fun a ha => ?_, Starts.cons hst.2 hPno, by omega, fun a ha => ?_,
    fun k hk => ?_, by omega⟩
  · have hf : vsaFoot C.H a := vsaFoot_of_cons ha.1
    rw [← hV3]
    refine wl1_congr fun _ => ?_
    have ho : OutL [(C.s.toNat - 64, 8, vS)] a := ⟨by have := hstk a hf; simp only; omega, trivial⟩
    rw [writeLog_out _ _ _ ho]
    exact wl1_congr fun _ => wl1_congr fun _ => (hMV a hf (by omega)).symm
  · refine writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ ?_)))
    rw [hMc a (by have := hstk a ha; omega)]
    exact copyW_present (hpres1 a ha)
  · have hf := hspan (P + 16 + k) (by omega) (by omega)
    have := hstk _ hf
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out]
    · rw [hMc _ (by omega), copyW_spec (.inl (by omega))
        (fun i hi => hpres1 _ (hspan _ (by omega) (by omega))) k (by omega),
        hnd _ (by omega) (by omega), show P + ps + 16 + k = B.p + k by omega]
      exact Hp.data k hk
    all_goals simp only [OutL, and_true]; omega

/-- **The prev+X+top return** (`0x80005574`): the top moves to `P + nb` with
its header, `P`'s header records `nb`, unlock, and return `P + 16`. -/
theorem pvT_fin {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb)
    {cs₀ : List Chunk} {P ps i : Nat} {pre post : List Nat} {predP succP : Nat}
    (hsp : chunks = (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨X, S, true⟩])
    (PV : FPv Mt (cs₀ ++ [⟨P, ps, false⟩]) bins X cs₀ P ps i pre post predP succP)
    (hXt : X + S = C.top0) (hroom : nb + 32 ≤ ps + S + (brkv - C.top0))
    {R' : Nat → BitVec 64} {Mc : Mem} (F : RFrame C R' Mc)
    (hMc : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 32 ≤ a) →
      Mc[a]? = (copyW (writeLog (writeLog Mt [(succP + 24, 8, BitVec.ofNat 64 predP)])
        [(predP + 16, 8, BitVec.ofNat 64 succP)]) (P + 16) (X + 16) ((S - 8) / 8))[a]?)
    (h6 : (R' 6).toNat = P) (h15 : (R' 15).toNat = nb)
    (h16 : (R' 16).toNat = ps + S + (brkv - C.top0)) (h13 : (R' 13).toNat = P + 16) :
    AW C.live C.S C.Q 0x80005574#64 R' Mc := by
  have Hp := D.heap
  have H0 := Hp.heap
  rw [hsp] at H0
  have HH := H0.heap.heap
  let C' : MCtx := { C with H := (B.p, B.nOld) :: C.H }
  have G : PvGeo C' P ps S predP succP := PvGeo.of_heap (C := C') (rest := []) H0 PV
  have hpend : X = P + ps := PV.pend.symm
  have hspan := pv_span D (rest := []) hsp hpend
  subst hpend
  have hst := Hp.starts
  unfold Starts at hst
  rw [List.map_cons, List.nodup_cons] at hst
  have hnoX : ∀ e ∈ C.H, e.1 ≠ P + ps + 16 := fun e he heq =>
    hst.1 (List.mem_map.2 ⟨e, he, by rw [heq]; exact D.addr⟩)
  have hp16 := G.p16; have hplo := G.plo; have hps16 := G.psz16; have hps32 := G.psz32
  have hs16 := G.sz16; have hs32 := G.sz32
  have htop : C.top0 + 16 ≤ 0x87800000 := G.top
  have hpp16 := G.pp16; have hsp16 := G.sp16
  have sP := G.sP; have pP := G.pP
  have hnb := D.nbok.eq
  have hnbv : C.n.toNat + 8 ≤ nb ∧ nb % 16 = 0 ∧ 32 ≤ nb := by rw [hnb]; unfold physSize; omega
  have hbrk := HH.brk_le; have hroom0 := H0.heap.top_room
  unfold heapEnd at hbrk
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hs64 := sp64_toNat O.spA
  have hdisj := Hp.disjD
  unfold allocHeadroom at hdisj
  have hstk : ∀ a, vsaFoot C.H a → a < C.s.toNat - 512 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => hdisj a (by omega) (by omega) ha
  -- `P`'s header, unchanged in `Mc`
  obtain ⟨hP, hPr⟩ : ∃ hP, read64 Mt (P + 8) = some hP := by
    obtain ⟨hh, hhr, _, _⟩ := walk_header HH.walk ⟨P, ps, false⟩ (by simp)
    exact ⟨hh, hhr⟩
  have hPodd := PV.prev hP hPr
  have hPlt := Vsa.Sim.read64_lt _ _ _ hPr
  have hPc : read64 Mc (P + 8) = some hP := by
    rw [read64_keep (m := Mt) fun k hk => ?_]
    · exact hPr
    have := hstk _ (hspan (P + 8 + k) (by omega) (by omega))
    rw [hMc _ (by omega), copyW_out (by omega), writeLog_out, writeLog_out] <;>
      simp only [OutL, and_true] <;> omega
  -- the stores' addresses and values
  have hfN : ∀ k, k < 8 → vsaFoot C.H (P + nb + 8 + k) := fun k hk => by
    refine .inr ⟨by show heapStart ≤ _; unfold heapStart; omega,
      by show _ < heapEnd; unfold heapEnd; omega, fun e he hin => ?_⟩
    obtain ⟨c, hc, hu, hca, hcn⟩ := HH.exact e (List.mem_cons_of_mem _ he) (List.mem_cons_of_mem _ he)
    have hPm' : (⟨P, ps, false⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨P + ps, S, true⟩] := by simp
    have hXm' : (⟨P + ps, S, true⟩ : Chunk) ∈ (cs₀ ++ [⟨P, ps, false⟩]) ++ [⟨P + ps, S, true⟩] := by simp
    have hcb := HH.walk.chunk_bounds c hc
    unfold InExt at hin
    rcases HH.walk.chunk_sep c hc _ hXm' with rfl | h1 | h1
    · exact hnoX e he (by simp only at hca; omega)
    · rcases HH.walk.chunk_sep c hc _ hPm' with rfl | h2 | h2
      · cases hu
      · simp only at h2; omega
      · simp only at h1 h2; omega
    · simp only at h1 hcb; omega
  have hgT : ∀ k, k < 8 → vsaFoot C.H (0x8001ad20 + k) := fun k hk => .inl (by unfold allocGlobal InRange; omega)
  have hfP : ∀ k, k < 8 → vsaFoot C.H (P + 8 + k) := fun k hk => hspan _ (by omega) (by omega)
  have oT := off_stack_of Hp.disj hgT
  have oN := off_stack_of Hp.disj hfN
  have oP := off_stack_of Hp.disj hfP
  have hT : (R' 6 + R' 15).toNat = P + nb := by rw [BitVec.toNat_add, h6, h15]; omega
  have hsz' : (R' 16 - R' 15).toNat = ps + S + (brkv - C.top0) - nb := by
    rw [BitVec.toNat_sub, h16, h15]; omega
  refine st_80005574 O.live (st_80005578 O.live (st_8000557c O.live ?_))
  have eT : ((0x8000557c#64) + (sign_extend (m := 64) ((0x00015#20) +++ (0x000#12))) +
      sign_extend (m := 64) (0x7a4#12)).toNat = 0x8001ad20 := by decide
  refine st_80005580 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eT]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eT]; exact O.foot hgT) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eT]
  refine st_80005584 O.live ?_
  have eN : (R' 6 + R' 15 + sign_extend (m := 64) (0x008#12)).toNat = P + nb + 8 := by
    rw [BitVec.toNat_add, hT]; simp; omega
  have sN : StOK (P + nb + 8) 8 := by
    have h1 : (P + nb + 8) % 8 = 0 := by omega
    unfold StOK Vsa.Sim.tohostAddr
    exact ⟨by omega, by omega, by omega, h1⟩
  refine st_80005588 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eN]; exact sN)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [eN]; exact O.foot hfN) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eN]
  have eP8 : (R' 6 + sign_extend (m := 64) (0x008#12)).toNat = P + 8 := by
    rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 from rfl,
      addr_add h6 8 (by omega)]
  have hPc2 : read64 (writeLog (writeLog Mc [(0x8001ad20, 8, R' 6 + R' 15)])
      [(P + nb + 8, 8, R' 16 - R' 15 ||| sign_extend (m := 64) (0x001#12))]) (P + 8) = some hP := by
    rw [rd_miss (by omega), rd_miss (by omega)]; exact hPc
  refine st_8000558c O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eP8]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eP8]; exact O.foot hfP) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [eP8, ldv_at hPc2 _ rfl]
  refine st_80005590 O.live ?_
  have eS : (R' 2 + sign_extend (m := 64) (0x000#12)).toNat = C.s.toNat - 64 := by
    rw [F.sp, show (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 from rfl,
      addr_add hs64 0 (by omega)]; omega
  refine st_80005594 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eS]; unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eS]
        exact O.stack (by unfold mHead; omega) (by omega)) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eS]
  refine st_80005598 O.live (st_8000559c O.live ?_)
  refine st_800055a0 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eP8]; unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eP8]; exact O.foot hfP) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eP8]
  sx_run [12] O.live at 0x800055a8
  -- the returned heap
  have hvH : (R' 16 - R' 15 ||| 1#64).toNat = ps + S + (brkv - C.top0) - nb + 1 := by
    have ht16 := HH.aligned.2; have hbp := H0.brk_page
    rw [or1_toNat', hsz']; omega
  have hvP : (BitVec.ofNat 64 hP &&& 1#64 ||| R' 15).toNat = nb + 1 := by
    rw [BitVec.toNat_or, and1_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hPlt, hPodd, h15,
      Nat.or_comm, nat_or1]; omega
  have Rt := pvT_heap O D hsp PV hXt hroom hMc (vS := R' 13) hT hvH hvP
  generalize hMf : writeLog (writeLog (writeLog (writeLog Mc [(2147593504, 8, R' 6 + R' 15)])
    [(P + nb + 8, 8, R' 16 - R' 15 ||| 1#64)]) [(C.s.toNat - 64, 8, R' 13)])
    [(P + 8, 8, BitVec.ofNat 64 hP &&& 1#64 ||| R' 15)] = Mf at Rt ⊢
  have hsl : read64 Mf (C.s.toNat - 64) = some (R' 13).toNat := by
    rw [← hMf, rd_miss (by omega), read64_store_hit]
  have F4 : RFrame C R' Mf := by
    rw [← hMf]
    exact (((F.store (a := 2147593504) (w := 8) (by omega)).store (a := P + nb + 8) (w := 8)
      (by omega)).store (a := C.s.toNat - 64) (w := 8) (by omega)).store (a := P + 8) (w := 8) (by omega)
  have eS2 : (R' 2 + sign_extend (m := 64) (0#12)).toNat = C.s.toNat - 64 := by
    rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from rfl, BitVec.add_zero, F.sp, hs64]
  refine st_800055a8 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eS2]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eS2]
        exact O.stack (by unfold mHead; omega) (by omega)) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [eS2, ldv_ld (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (R' 13).isLt]; exact hsl)]
  refine st_800055ac O.live ?_
  refine repi O (F4.of_regs ?_ ?_ ?_) fun R'' hR h10 => O.ok R'' Mf ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have hp : (R'' 10).toNat = P + 16 := by
    rw [h10]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (R' 13).isLt, h13]
  refine ⟨hR, ?_, ?_, ⟨P + nb, brkv, cs₀ ++ [⟨P, nb, true⟩], updBins bins i (pre ++ post), ?_, Rt.top_le⟩, Rt.pres,
    fun k hk => ?_⟩ <;> try rw [hp]
  · exact Rt.heap.fresh_of_block Rt.starts
  · exact Rt.align
  · exact Rt.heap
  · exact Rt.data k hk

end VsaIris.VsaHeap
