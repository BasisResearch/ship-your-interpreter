import VsaIris.Vsa.ReallocMove

/-!
# `_realloc_r` through a new block

When the old chunk cannot grow in place, `_realloc_r` calls `_malloc_r`
(`rcall_malloc`). NULL returns NULL with the old block kept. A new chunk
right after the old one is merged into it and handed to the tail. Any other
new block receives the old payload (`S - 8` bytes: inline for up to 72, else
`memmove_fwd`), the old block is freed (`rcall_free`), and the new block is
returned.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

section Copy

variable {live : Nat → Prop} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- One word of an inline copy: `ld rT,offL(rS); sd rT,offS(rD)` copying word
`j` of `copyW`. -/
theorem cp_pair {rT rS rD : Nat} (hTD : rD ≠ rT) {pcL pcS pcN : BitVec 64} {offL offS : BitVec 12}
    {R : Nat → BitVec 64} {M0 : Mem} {d s j : Nat}
    (stL : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      LdOK ((R rS) + sign_extend (m := 64) offL).toNat 8 →
      (∀ b ∈ accAddrs ((R rS) + sign_extend (m := 64) offL).toNat 8, S b) →
      AW live S Q pcS (upd R rT (ldv .ld Mt ((R rS) + sign_extend (m := 64) offL).toNat)) Mt →
      AW live S Q pcL R Mt)
    (stS : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      StOK ((R rD) + sign_extend (m := 64) offS).toNat 8 →
      (∀ b ∈ accAddrs ((R rD) + sign_extend (m := 64) offS).toNat 8, S b) →
      AW live S Q pcN R (writeLog Mt [(((R rD) + sign_extend (m := 64) offS).toNat, 8, (R rT))]) →
      AW live S Q pcS R Mt)
    (hL : (R rS + sign_extend (m := 64) offL).toNat = s + 8 * j)
    (hS : (R rD + sign_extend (m := 64) offS).toNat = d + 8 * j)
    (hl1 : LdOK (s + 8 * j) 8) (hl2 : ∀ b ∈ accAddrs (s + 8 * j) 8, S b)
    (hs1 : StOK (d + 8 * j) 8) (hs2 : ∀ b ∈ accAddrs (d + 8 * j) 8, S b)
    (hk : AW live S Q pcN (upd R rT (ldv .ld (copyW M0 d s j) (s + 8 * j))) (copyW M0 d s (j + 1))) :
    AW live S Q pcL R (copyW M0 d s j) := by
  refine stL (by rw [hL]; exact hl1) (by rw [hL]; exact hl2) ?_
  have hS' : ((upd R rT (ldv .ld (copyW M0 d s j) (R rS + sign_extend (m := 64) offL).toNat)) rD +
      sign_extend (m := 64) offS).toNat = d + 8 * j := by rw [upd_other _ _ hTD]; exact hS
  refine stS (by rw [hS']; exact hs1) (by rw [hS']; exact hs2) ?_
  rw [hS', upd_same, hL, ← copyW_succ]
  exact hk

/-- The three-word tail of the malloc path's inline copy (`0x800053a8`): words
`j … j+2` from `a4` to `a5`. -/
theorem mal_tail3 {M0 : Mem} {d s L : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    {R : Nat → BitVec 64} {j : Nat} (h14 : (R 14).toNat = s + 8 * j) (h15 : (R 15).toNat = d + 8 * j)
    (hj : 8 * j + 24 ≤ L)
    (hk : ∀ R', (∀ x, x ≠ 12 → x ≠ 14 → R' x = R x) →
      AW live S Q 0x800053c0#64 R' (copyW M0 d s (j + 3))) :
    AW live S Q 0x800053a8#64 R (copyW M0 d s j) := by
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
  have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * j) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * j) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 14) (rD := 15) (by decide) (st_800053a8 hlive) (st_800053ac hlive)
    (by rw [n0, addr_add h14 0 (by omega)]; omega) (by rw [n0, addr_add h15 0 (by omega)]; omega)
    l1 l2 s1 s2 ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * (j + 1)) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * (j + 1)) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 12) (rS := 14) (rD := 15) (by decide) (st_800053b0 hlive) (st_800053b4 hlive)
    (by rw [upd_other _ _ (by decide), n8, addr_add h14 8 (by omega)]; omega)
    (by rw [upd_other _ _ (by decide), n8, addr_add h15 8 (by omega)]; omega) l1 l2 s1 s2 ?_
  obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * (j + 2)) (by omega) (by omega)
  obtain ⟨s1, s2⟩ := A.st (a := d + 8 * (j + 2)) (by omega) (by omega) (by omega)
  refine cp_pair (rT := 14) (rS := 14) (rD := 15) (by decide) (st_800053b8 hlive) (st_800053bc hlive)
    (by rw [upd_other _ _ (by decide), upd_other _ _ (by decide), n16, addr_add h14 16 (by omega)]; omega)
    (by rw [upd_other _ _ (by decide), upd_other _ _ (by decide), n16, addr_add h15 16 (by omega)]; omega)
    l1 l2 s1 s2 ?_
  exact hk _ fun x h12 h14 => by simp only [upd_apply, h12, h14, ite_false]

/-- Forget a register file's shape, keeping only facts about it. -/
theorem aw_forget {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (P : (Nat → BitVec 64) → Prop) (hP : P R) (hk : ∀ R', P R' → AW live S Q pc R' Mt) :
    AW live S Q pc R Mt := hk R hP

/-- The registers an inline copy's prefix keeps: `sp`, `s0-s3`, `a0` (the
destination), `a2` (the length), `a3` and `a5`. -/
structure CPKeep (R R' : Nat → BitVec 64) : Prop where
  sp : R' 2 = R 2
  s0 : R' 8 = R 8
  s1 : R' 9 = R 9
  a0 : R' 10 = R 10
  a2 : R' 12 = R 12
  a3 : R' 13 = R 13
  a5 : R' 15 = R 15
  s2 : R' 18 = R 18
  s3 : R' 19 = R 19

theorem CPKeep.upd {R R' : Nat → BitVec 64} (K : CPKeep R R') {k : Nat} (v : BitVec 64)
    (h2 : k ≠ 2) (h8 : k ≠ 8) (h9 : k ≠ 9) (h10 : k ≠ 10) (h12 : k ≠ 12) (h13 : k ≠ 13) (h15 : k ≠ 15)
    (h18 : k ≠ 18) (h19 : k ≠ 19) : CPKeep R (upd R' k v) :=
  ⟨by rw [upd_other _ _ (Ne.symm h2)]; exact K.sp, by rw [upd_other _ _ (Ne.symm h8)]; exact K.s0,
    by rw [upd_other _ _ (Ne.symm h9)]; exact K.s1, by rw [upd_other _ _ (Ne.symm h10)]; exact K.a0,
    by rw [upd_other _ _ (Ne.symm h12)]; exact K.a2, by rw [upd_other _ _ (Ne.symm h13)]; exact K.a3,
    by rw [upd_other _ _ (Ne.symm h15)]; exact K.a5, by rw [upd_other _ _ (Ne.symm h18)]; exact K.s2,
    by rw [upd_other _ _ (Ne.symm h19)]; exact K.s3⟩

/-- `CPKeep` through writes to other registers. -/
macro "cp_keep" h:term : tactic => `(tactic| (refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] <;>
  first | exact ($h).sp | exact ($h).s0 | exact ($h).s1 | exact ($h).a0 | exact ($h).a2 |
    exact ($h).a3 | exact ($h).a5 | exact ($h).s2 | exact ($h).s3))

/-- The inline copy's prefixes (`0x80005398`, a payload of 24, 40, 56 or 72
bytes): up to three pairs of words, then the tail. -/
theorem mal_inline {M0 : Mem} {d s L : Nat} (A : CPArgs S d s L) (hlive : ∀ p ∈ allocText, live p.1)
    (hL : L = 24 ∨ L = 40 ∨ L = 56 ∨ L = 72)
    {R : Nat → BitVec 64} (h8 : (R 8).toNat = s) (h10 : (R 10).toNat = d) (h12 : (R 12).toNat = L)
    (h15 : (R 15).toNat = 72)
    (hk : ∀ R', R' 2 = R 2 → R' 8 = R 8 → R' 9 = R 9 → R' 13 = R 13 → R' 18 = R 18 → R' 19 = R 19 →
      AW live S Q 0x800053c0#64 R' (copyW M0 d s (L / 8))) :
    AW live S Q 0x80005398#64 R (copyW M0 d s 0) := by
  have hd8 := A.d8; have hs8 := A.s8; have hshi := A.shi; have hdhi := A.dhi
  have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
  have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have n24 : (sign_extend (m := 64) (0x018#12) : BitVec 64) = BitVec.ofNat 64 24 := rfl
  have n32 : (sign_extend (m := 64) (0x020#12) : BitVec 64) = BitVec.ofNat 64 32 := rfl
  have n40 : (sign_extend (m := 64) (0x028#12) : BitVec 64) = BitVec.ofNat 64 40 := rfl
  have n48 : (sign_extend (m := 64) (0x030#12) : BitVec 64) = BitVec.ofNat 64 48 := rfl
  -- the tail from word `j`, the base registers at `s + 8 j` and `d + 8 j`
  have tail : ∀ j (R' : Nat → BitVec 64), j + 3 = L / 8 → (R' 14).toNat = s + 8 * j →
      (R' 15).toNat = d + 8 * j → R' 2 = R 2 → R' 8 = R 8 → R' 9 = R 9 → R' 13 = R 13 →
      R' 18 = R 18 → R' 19 = R 19 → AW live S Q 0x800053a8#64 R' (copyW M0 d s j) := by
    intro j R' hj g14 g15 g2 g8 g9 g13 g18 g19
    refine mal_tail3 A hlive g14 g15 (by omega) fun R'' hR => ?_
    rw [hj]
    exact hk R'' (by rw [hR 2 (by decide) (by decide), g2]) (by rw [hR 8 (by decide) (by decide), g8])
      (by rw [hR 9 (by decide) (by decide), g9]) (by rw [hR 13 (by decide) (by decide), g13])
      (by rw [hR 18 (by decide) (by decide), g18]) (by rw [hR 19 (by decide) (by decide), g19])
  -- a word pair from the `s0`/`a0` bases
  have pair : ∀ (j : Nat) {pcL pcS pcN : BitVec 64} {off : BitVec 12} (rT : Nat) (R1 : Nat → BitVec 64),
      rT ≠ 2 → rT ≠ 8 → rT ≠ 9 → rT ≠ 10 → rT ≠ 12 → rT ≠ 13 → rT ≠ 15 → rT ≠ 18 → rT ≠ 19 →
      (sign_extend (m := 64) off : BitVec 64) = BitVec.ofNat 64 (8 * j) → 8 * j + 8 ≤ L →
      (∀ {R : Nat → BitVec 64} {Mt : Mem},
        LdOK ((R 8) + sign_extend (m := 64) off).toNat 8 →
        (∀ b ∈ accAddrs ((R 8) + sign_extend (m := 64) off).toNat 8, S b) →
        AW live S Q pcS (upd R rT (ldv .ld Mt ((R 8) + sign_extend (m := 64) off).toNat)) Mt →
        AW live S Q pcL R Mt) →
      (∀ {R : Nat → BitVec 64} {Mt : Mem},
        StOK ((R 10) + sign_extend (m := 64) off).toNat 8 →
        (∀ b ∈ accAddrs ((R 10) + sign_extend (m := 64) off).toNat 8, S b) →
        AW live S Q pcN R (writeLog Mt [(((R 10) + sign_extend (m := 64) off).toNat, 8, (R rT))]) →
        AW live S Q pcS R Mt) →
      CPKeep R R1 → (∀ v, AW live S Q pcN (upd R1 rT v) (copyW M0 d s (j + 1))) →
      AW live S Q pcL R1 (copyW M0 d s j) := by
    intro j pcL pcS pcN off rT R1 t2 t8 t9 t10 t12 t13 t15 t18 t19 hoff hj stL stS K k
    obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * j) (by omega) (by omega)
    obtain ⟨s1, s2⟩ := A.st (a := d + 8 * j) (by omega) (by omega) (by omega)
    exact cp_pair (rT := rT) (rS := 8) (rD := 10) (Ne.symm t10) stL stS
      (by rw [K.s0, hoff, addr_add h8 _ (by omega)]) (by rw [K.a0, hoff, addr_add h10 _ (by omega)])
      l1 l2 s1 s2 (k _)
  refine st_80005398 hlive ?_
  refine st_8000539c hlive (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h12] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x027#12) : BitVec 64).toNat = 39 from rfl] at hc
  · -- 40, 56 or 72 bytes: the first word, with `li a4,55` before its store
    have K0 : CPKeep R R := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 0) (by omega) (by omega)
    obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 0) (by omega) (by omega) (by omega)
    have e0 : ((upd R 14 (0#64 + sign_extend (m := 64) (0x027#12))) 8 +
        sign_extend (m := 64) (0x000#12)).toNat = s + 8 * 0 := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n0, addr_add h8 0 (by omega)]
    refine st_800055c0 hlive (by rw [e0]; exact l1) (by rw [e0]; exact l2) ?_
    rw [e0]
    refine st_800055c4 hlive ?_
    have f0 : ((upd (upd (upd R 14 (0#64 + sign_extend (m := 64) (0x027#12))) 11
        (ldv .ld (copyW M0 d s 0) (s + 8 * 0))) 14
        (0#64 + sign_extend (m := 64) (0x037#12))) 10 + sign_extend (m := 64) (0x000#12)).toNat =
        d + 8 * 0 := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n0, addr_add h10 0 (by omega)]
    refine st_800055c8 hlive (by rw [f0]; exact s1) (by rw [f0]; exact s2) ?_
    rw [f0]
    have hv : (upd (upd (upd R 14 (0#64 + sign_extend (m := 64) (0x027#12))) 11
        (ldv .ld (copyW M0 d s 0) (s + 8 * 0))) 14 (0#64 + sign_extend (m := 64) (0x037#12))) 11 =
        ldv .ld (copyW M0 d s 0) (s + 8 * 0) := by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [hv, ← copyW_succ]
    refine aw_forget (fun R1 => CPKeep R R1 ∧ (R1 14).toNat = 55) ⟨by cp_keep K0, rfl⟩ fun R1 ⟨K1, g14⟩ => ?_
    -- the second word
    refine pair 1 11 R1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) n8 (by omega) (st_800055cc hlive) (st_800055d0 hlive) K1 fun v => ?_
    have K2 := K1.upd v (k := 11) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
    refine st_800055d4 hlive (fun hc' => ?_) (fun hc' => ?_) <;>
      rw [upd_other _ _ (by decide), upd_other _ _ (by decide), g14, K1.a2, h12] at hc'
    · -- 56 or 72 bytes: words 2 and 3
      refine pair 2 14 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) n16 (by omega) (st_800056f0 hlive) (st_800056f4 hlive) K2
        fun v2 => ?_
      have K3 := K2.upd v2 (k := 14) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      refine pair 3 14 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) n24 (by omega) (st_800056f8 hlive) (st_800056fc hlive) K3
        fun v3 => ?_
      have K4 := K3.upd v3 (k := 14) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
      refine st_80005700 hlive (fun hc'' => ?_) (fun hc'' => ?_)
      · -- 72 bytes: words 4 and 5, then the tail
        have hL72 : L = 72 := by
          have := congrArg BitVec.toNat hc''; rw [K4.a2, K4.a5, h12, h15] at this; exact this
        obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 4) (by omega) (by omega)
        obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 4) (by omega) (by omega) (by omega)
        have e4 : ((upd (upd R1 11 v) 14 v2) 14 |> fun _ => (upd (upd (upd R1 11 v) 14 v2) 14 v3) 8 +
            sign_extend (m := 64) (0x020#12)).toNat = s + 8 * 4 := by
          simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K1.s0, n32, addr_add h8 32 (by omega)]
        refine st_800057d8 hlive (by rw [e4]; exact l1) (by rw [e4]; exact l2) ?_
        rw [e4]
        refine st_800057dc hlive ?_
        refine st_800057e0 hlive ?_
        have f4 : ((upd (upd (upd (upd (upd (upd R1 11 v) 14 v2) 14 v3) 12
            (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 14
            ((upd (upd (upd (upd R1 11 v) 14 v2) 14 v3) 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 8 +
              sign_extend (m := 64) (0x030#12))) 15
            ((upd (upd (upd (upd (upd R1 11 v) 14 v2) 14 v3) 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 14
              ((upd (upd (upd (upd R1 11 v) 14 v2) 14 v3) 12 (ldv .ld (copyW M0 d s 4) (s + 8 * 4))) 8 +
                sign_extend (m := 64) (0x030#12))) 10 + sign_extend (m := 64) (0x030#12))) 10 +
            sign_extend (m := 64) (0x020#12)).toNat = d + 8 * 4 := by
          simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K1.a0, n32, addr_add h10 32 (by omega)]
        refine st_800057e4 hlive (by rw [f4]; exact s1) (by rw [f4]; exact s2) ?_
        rw [f4]
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        rw [← copyW_succ]
        obtain ⟨l1, l2⟩ := A.ld (a := s + 8 * 5) (by omega) (by omega)
        obtain ⟨s1, s2⟩ := A.st (a := d + 8 * 5) (by omega) (by omega) (by omega)
        refine cp_pair (rT := 12) (rS := 8) (rD := 10) (by decide) (st_800057e8 hlive)
          (st_800057ec hlive) ?_ ?_ l1 l2 s1 s2 ?_
        · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K1.s0, n40, addr_add h8 40 (by omega)]
        · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [K1.a0, n40, addr_add h10 40 (by omega)]
        refine st_800057f0 hlive ?_
        refine tail 6 _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        · rw [K1.s0, n48, addr_add h8 48 (by omega)]
        · rw [K1.a0, n48, addr_add h10 48 (by omega)]
        · exact K1.sp
        · exact K1.s0
        · exact K1.s1
        · exact K1.a3
        · exact K1.s2
        · exact K1.s3
      · -- 56 bytes: the tail from word 4
        have hL56 : L = 56 := by
          have : L ≠ 72 := fun h => hc'' (BitVec.eq_of_toNat_eq (by rw [K4.a2, K4.a5, h12, h15, h]))
          omega
        refine st_80005704 hlive ?_
        refine st_80005708 hlive ?_
        refine st_8000570c hlive ?_
        refine tail 4 _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
          simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
        · rw [K1.s0, n32, addr_add h8 32 (by omega)]
        · rw [K1.a0, n32, addr_add h10 32 (by omega)]
        · exact K1.sp
        · exact K1.s0
        · exact K1.s1
        · exact K1.a3
        · exact K1.s2
        · exact K1.s3
    · -- 40 bytes: the tail from word 2
      refine st_800055d8 hlive ?_
      refine st_800055dc hlive ?_
      refine st_800055e0 hlive ?_
      refine tail 2 _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [K1.s0, n16, addr_add h8 16 (by omega)]
      · rw [K1.a0, n16, addr_add h10 16 (by omega)]
      · exact K1.sp
      · exact K1.s0
      · exact K1.s1
      · exact K1.a3
      · exact K1.s2
      · exact K1.s3
  · -- 24 bytes: the tail alone
    have hL24 : L = 24 := by omega
    refine st_800053a0 hlive ?_
    refine st_800053a4 hlive ?_
    refine tail 0 _ (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [n0, addr_add h8 0 (by omega)]
    · rw [n0, addr_add h10 0 (by omega)]

end Copy

end VsaIris.VsaHeap
