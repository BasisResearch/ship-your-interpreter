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

/-- **The malloc path's copy** (`0x8000538c`): the old payload's `S - 8` bytes
to the new block, inline or by `memmove` (which spills the new block at
`sp`). -/
theorem mal_copy {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem} {d s S : Nat}
    (A : CPArgs C.S d s (S - 8)) (hS32 : 32 ≤ S) (hS16 : S % 16 = 0)
    (hslotD : C.s.toNat - 64 + 8 ≤ d ∨ d + (S - 8) ≤ C.s.toNat - 64)
    (hslotS : C.s.toNat - 64 + 8 ≤ s ∨ s + (S - 8) ≤ C.s.toNat - 64)
    (h8 : (R 8).toNat = s) (h10 : (R 10).toNat = d) (h14 : (R 14).toNat = S) (h13 : R 13 = R 10)
    (hsp : R 2 = C.s + 18446744073709551552#64)
    (hk : ∀ R' Mc, R' 2 = R 2 → R' 8 = R 8 → R' 9 = R 9 → R' 13 = R 13 → R' 18 = R 18 →
      R' 19 = R 19 →
      (∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 8 ≤ a) → Mc[a]? = (copyW Mt d s ((S - 8) / 8))[a]?) →
      AW C.live C.S C.Q 0x800053c0#64 R' Mc) :
    AW C.live C.S C.Q 0x8000538c#64 R Mt := by
  have hs64 := sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hL : ((R 14) + sign_extend (m := 64) (0xff8#12)).toNat = S - 8 := by
    rw [show (sign_extend (m := 64) (0xff8#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl,
      addr_sub h14 8 (by omega) (by omega)]
  refine st_8000538c O.live ?_
  refine st_80005390 O.live ?_
  refine st_80005394 O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hL] at hc <;>
    rw [show (0#64 + sign_extend (m := 64) (0x048#12) : BitVec 64).toNat = 72 from rfl] at hc
  · -- over 72 bytes: `memmove`
    refine st_80005658 O.live ?_
    have eS : (R 2 + sign_extend (m := 64) (0x000#12)).toNat = C.s.toNat - 64 := by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 from rfl, hsp,
        addr_add hs64 0 (by omega)]; omega
    refine st_8000565c O.live
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eS]; unfold StOK Vsa.Sim.tohostAddr; omega)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eS]
          exact O.stack (by unfold mHead; omega) (by omega)) ?_
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [eS]
    refine st_80005660 O.live ?_
    simp only [VsaIris.ra]
    have AM : MMArgs C.S d s (S - 8) := { A with n32 := by omega }
    refine memmove_fwd AM O.live ?_ ?_ ?_ (by simp only [upd_apply, Nat.reduceEqDiff, ite_true]; decide)
      fun R' hK => ?_ <;> try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact h10
    · rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 from rfl,
        addr_add h8 0 (by omega)]; rfl
    · exact hL
    -- back from `memmove`: reload the new block and join
    rw [show (BitVec.ofNat 64 (2147505760 + 4) : BitVec 64) = 0x80005664#64 from rfl]
    have hslot : read64 (copyW (writeLog Mt [(C.s.toNat - 64, 8, R 10)]) d s ((S - 8) / 8))
        (C.s.toNat - 64) = some (R 10).toNat := by
      rw [read64_keep (m := writeLog Mt [(C.s.toNat - 64, 8, R 10)]) fun k hk => copyW_out (by omega),
        read64_store_hit]
    have e2 : (R' 2 + sign_extend (m := 64) (0x000#12)).toNat = C.s.toNat - 64 := by
      rw [hK.sp]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact eS
    refine st_80005664 O.live (by rw [e2]; unfold LdOK Vsa.Sim.tohostAddr; omega)
      (by rw [e2]; exact O.stack (by unfold mHead; omega) (by omega)) ?_
    rw [e2, ldv_ld (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (R 10).isLt]; exact hslot)]
    refine st_80005668 O.live ?_
    refine hk _ _ ?_ ?_ ?_ ?_ ?_ ?_ fun a ha => copyW_agree (fun a ha => ?_) (by omega) a ha <;>
      try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · rw [hK.sp]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · rw [hK.s0]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · rw [hK.s1]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · rw [h13]; exact BitVec.eq_of_toNat_eq (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (R 10).isLt])
    · rw [hK.s2]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · rw [hK.s3]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    · have ho : OutL [(C.s.toNat - 64, 8, R 10)] a := ⟨by simp only; omega, trivial⟩
      rw [writeLog_out _ _ _ ho]
  · -- up to 72 bytes: inline
    have hLs : S - 8 = 24 ∨ S - 8 = 40 ∨ S - 8 = 56 ∨ S - 8 = 72 := by omega
    exact mal_inline A O.live hLs (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h8)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h10)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hL)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rfl)
      fun R' g2 g8 g9 g13 g18 g19 => hk R' _ (by rw [g2]; simp only [upd_apply, Nat.reduceEqDiff, ite_false])
        (by rw [g8]; simp only [upd_apply, Nat.reduceEqDiff, ite_false])
        (by rw [g9]; simp only [upd_apply, Nat.reduceEqDiff, ite_false])
        (by rw [g13]; simp only [upd_apply, Nat.reduceEqDiff, ite_false])
        (by rw [g18]; simp only [upd_apply, Nat.reduceEqDiff, ite_false])
        (by rw [g19]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]) fun _ _ => rfl

/-- The epilogue's third copy (`0x800053dc`). -/
theorem repi3 {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem} (F : RFrame C R Mt)
    (hfin : ∀ R' : Nat → BitVec 64, MRegs C R' → R' 10 = R 13 → AW C.live C.S C.Q C.r R' Mt) :
    AW C.live C.S C.Q 0x800053dc#64 R Mt :=
  repi_core O (st_800053dc O.live) (st_800053e0 O.live) (st_800053e4 O.live) (st_800053e8 O.live)
    (st_800053ec O.live) (st_800053f0 O.live) F hfin

/-- **Free the old block and return the new one** (`0x800053c0`): the copied
heap holds both blocks; `_free_r(p)`, unlock, return `p'`. -/
theorem mal_free {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mc : Mem}
    {p' top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (F : RFrame C R Mc) (h8 : (R 8).toNat = B.p) (h9 : R 9 = reentV) (h13 : (R 13).toNat = p')
    (hp16 : p' % 16 = 0)
    (hheap : PHeapAt Mc ((p', C.n.toNat) :: (B.p, B.nOld) :: C.H) top brkv chunks bins)
    (hst : Starts ((p', C.n.toNat) :: (B.p, B.nOld) :: C.H))
    (htop : top ≤ C.top0 + physSize C.n.toNat)
    (hpres : ∀ a, vsaFoot C.H a → (Mc[a]?).isSome)
    (hdisjD : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a)
    (hdata : ∀ k, k < B.nOld → Mc[p' + k]? = some (B.old (B.p + k))) (hold : B.nOld ≤ C.n.toNat) :
    AW C.live C.S C.Q 0x800053c0#64 R Mc := by
  have hs64 := sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hsp := F.sp
  have eS : (R 2 + sign_extend (m := 64) (0x000#12)).toNat = C.s.toNat - 64 := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 from rfl, hsp,
      addr_add hs64 0 (by omega)]; omega
  -- the new block's bytes are footprint of the others
  have hblk : ∀ k, k < C.n.toNat → vsaFoot C.H (p' + k) ∧ ¬ vsaFoot ((p', C.n.toNat) :: C.H) (p' + k) := by
    have hst' : Starts ((p', C.n.toNat) :: C.H) := by
      unfold Starts at *
      simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at *
      exact ⟨hst.1.2, hst.2.2⟩
    have Hd : PHeapAt Mc ((p', C.n.toNat) :: C.H) top brkv chunks bins :=
      (hheap.perm (H' := (B.p, B.nOld) :: (p', C.n.toNat) :: C.H) mem_swap).drop
    intro k hk
    refine ⟨Hd.block_foot hst' k hk, fun hf => ?_⟩
    rcases hf with hg | ⟨_, _, h3⟩
    · have := Hd.fresh_of_block hst'
      obtain ⟨_, hlo', hhi', _⟩ := this.block
      have := allocGlobal_off_arena _ hg
      change heapStart ≤ p' at hlo'
      change p' + C.n.toNat ≤ heapEnd at hhi'
      unfold heapStart heapEnd at *; omega
    · exact h3 _ List.mem_cons_self ⟨by simp only; omega, by simp only; omega⟩
  refine st_800053c0 O.live ?_
  refine st_800053c4 O.live ?_
  refine st_800053c8 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eS]; unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eS]
        exact O.stack (by unfold mHead; omega) (by omega)) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  rw [eS]
  generalize hM2 : writeLog Mc [(C.s.toNat - 64, 8, R 13)] = M2
  have hM2o : ∀ a, (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 8 ≤ a) → M2[a]? = Mc[a]? := fun a ha => by
    have ho : OutL [(C.s.toNat - 64, 8, R 13)] a := ⟨by simp only; omega, trivial⟩
    rw [← hM2, writeLog_out _ _ _ ho]
  have hfoot : ∀ a, vsaFoot C.H a → (a < C.s.toNat - 64 ∨ C.s.toNat - 64 + 8 ≤ a) := fun a ha =>
    Classical.byContradiction fun hc => hdisjD a (by unfold allocHeadroom; omega) (by omega) ha
  have H2 : PHeapAt M2 ((B.p, B.nOld) :: (p', C.n.toNat) :: C.H) top brkv chunks bins :=
    (hheap.perm mem_swap).transport_read fun a ha => (hM2o a (hfoot a (vsaFoot_cons_sub a
      (vsaFoot_cons_sub a (vsaFoot_perm mem_swap ha.1))))).symm
  refine st_800053cc O.live ?_
  simp only [VsaIris.ra]
  refine rcall_free O (link := 0x800053d0#64) (by decide) (fun a ha => vsaFoot_cons_sub a ha) ?_ ?_ ?_ ?_
    H2 hst.swap (fun a ha => by rw [← hM2]; exact writeLog_present _ _ _ (hpres a (vsaFoot_cons_sub a ha)))
    hdisjD (fun R' Mt' g1 g2 g8 g9 g18 g19 hfh hfp hfr => ?_) <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hsp
  · rw [h9]; rfl
  · rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 from rfl,
      addr_add h8 0 (by omega)]; rfl
  -- back from `_free_r`
  obtain ⟨top', brkv', chunks', bins', H3, htop'⟩ := hfh
  have hkeep : ∀ a, ((C.s.toNat - 64 ≤ a ∧ a < C.s.toNat) ∨ ¬ vsaFoot ((p', C.n.toNat) :: C.H) a ∧
      vsaFoot C.H a) → Mt'[a]? = M2[a]? := by
    intro a ha
    refine hfr a fun hw => ?_
    rcases hw with hf | ⟨h1, h2⟩
    · rcases ha with ⟨h1, h2⟩ | ⟨hn, _⟩
      · exact hdisjD a (by unfold allocHeadroom; omega) h2 (vsaFoot_cons_sub a hf)
      · exact hn hf
    · rw [hs64] at h1 h2
      rcases ha with ⟨h3, _⟩ | ⟨_, hf⟩
      · omega
      · exact hdisjD a (win64_le h1) (by omega) hf
  have hslot : ∀ a, C.s.toNat - 64 ≤ a → a + 8 ≤ C.s.toNat → read64 Mt' a = read64 M2 a :=
    fun a h1 h2 => read64_keep fun k hk => hkeep _ (.inl ⟨by omega, by omega⟩)
  sx_run [12] O.live at 0x800053d8
  have e2 : ((upd (upd (upd R' 10 (R' 9)) 1 2147505112#64) 10 2147596760#64) 2 +
      sign_extend (m := 64) (0x000#12)).toNat = C.s.toNat - 64 := by
    simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    rw [g2, show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from rfl, BitVec.add_zero]
    exact eS
  have hsl : read64 Mt' (C.s.toNat - 64) = some (R 13).toNat := by
    rw [hslot _ (by omega) (by omega), ← hM2, read64_store_hit]
  refine st_800053d8 O.live (by rw [e2]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [e2]; exact O.stack (by unfold mHead; omega) (by omega)) ?_
  rw [e2, ldv_ld (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (R 13).isLt]; exact hsl)]
  have F' : RFrame C R' Mt' := by
    refine ⟨g2.trans hsp, ?_, ?_, ?_, g18.trans F.s2, g19.trans F.s3⟩
    · rw [hslot _ (by omega) (by omega), ← hM2, read64_store_miss _ _ (by omega)]; exact F.s0
    · rw [hslot _ (by omega) (by omega), ← hM2, read64_store_miss _ _ (by omega)]; exact F.s1
    · rw [hslot _ (by omega) (by omega), ← hM2, read64_store_miss _ _ (by omega)]; exact F.ra
  have hst' : Starts ((p', C.n.toNat) :: C.H) := by
    unfold Starts at *
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at *
    exact ⟨hst.1.2, hst.2.2⟩
  refine repi3 O (F'.of_regs ?_ ?_ ?_) fun R'' hR h10 => O.ok R'' Mt' ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  have hp : (R'' 10).toNat = p' := by
    rw [h10]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (R 13).isLt, h13]
  refine ⟨hR, ?_, ?_, ⟨top', brkv', chunks', bins', ?_, by omega⟩, fun a ha => ?_, fun k hk => ?_⟩ <;>
    try rw [hp]
  · exact H3.fresh_of_block hst'
  · exact hp16
  · exact H3
  · by_cases hf : vsaFoot ((p', C.n.toNat) :: C.H) a
    · exact hfp a hf
    · rw [hkeep a (.inr ⟨hf, ha⟩), ← hM2]; exact writeLog_present _ _ _ (hpres a ha)
  · obtain ⟨hf, hn⟩ := hblk k (by omega)
    rw [hkeep _ (.inr ⟨hn, hf⟩), hM2o _ (hfoot _ hf)]
    exact hdata k hk

/-- The state back from the nested `_malloc_r` with a block `p'`: the frame and
the three spills (`nb`, `X`, `S`), the heap holding both blocks with `X`
unchanged (`LiveKeep`), the new block fresh, and the old contents in place. -/
structure RMal (C : MCtx) (B : RB) (R : Nat → BitVec 64) (Mt : Mem) (X S nb p' top brkv : Nat)
    (chunks : List Chunk) (bins : Nat → List Nat) : Prop where
  frame : RFrame C R Mt
  spNb : read64 Mt (C.s.toNat - 64) = some nb
  spX : read64 Mt (C.s.toNat - 64 + 8) = some X
  spS : read64 Mt (C.s.toNat - 64 + 16) = some S
  heap : PHeapAt Mt ((p', C.n.toNat) :: (B.p, B.nOld) :: C.H) top brkv chunks bins
  top_le : top ≤ C.top0 + physSize C.n.toNat
  fresh : FreshAt ((B.p, B.nOld) :: C.H) p' C.n.toNat
  align : p' % 16 = 0
  keepX : (⟨X, S, true⟩ : Chunk) ∈ chunks
  addr : X + 16 = B.p
  starts : Starts ((B.p, B.nOld) :: C.H)
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  disjD : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  data : ∀ k, k < B.nOld → Mt[B.p + k]? = some (B.old (B.p + k))
  nbok : NbOK C.n nb
  nb31 : nb < 2 ^ 31
  lt : S < nb
  grow : B.nOld < C.n.toNat
  s0 : (R 8).toNat = X + 16
  s1 : R 9 = reentV
  a0 : (R 10).toNat = p'

theorem RMal.of_regs {C : MCtx} {B : RB} {R R' : Nat → BitVec 64} {Mt : Mem}
    {X S nb p' top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (M : RMal C B R Mt X S nb p' top brkv chunks bins) (h2 : R' 2 = R 2) (h8 : R' 8 = R 8)
    (h9 : R' 9 = R 9) (h10 : R' 10 = R 10) (h18 : R' 18 = R 18) (h19 : R' 19 = R 19) :
    RMal C B R' Mt X S nb p' top brkv chunks bins :=
  { M with frame := M.frame.of_regs h2 h18 h19, s0 := h8 ▸ M.s0, s1 := h9 ▸ M.s1, a0 := h10 ▸ M.a0 }

/-- Both blocks with `p'` fresh start at distinct addresses. -/
theorem RMal.starts2 {C : MCtx} {B : RB} {R : Nat → BitVec 64} {Mt : Mem} {X S nb p' top brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (M : RMal C B R Mt X S nb p' top brkv chunks bins) :
    Starts ((p', C.n.toNat) :: (B.p, B.nOld) :: C.H) :=
  M.starts.cons M.fresh.start

/-- **The new chunk right after the old one** (`0x800055b0`): merge them and
go to the tail. -/
theorem mal_merge {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {X S nb p' top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (M : RMal C B R Mt X S nb p' top brkv chunks bins) (hp' : p' = X + S + 16)
    (h12 : (R 12).toNat = X) (h14 : (R 14).toNat = S) (h15 : (R 15).toNat = nb) :
    AW C.live C.S C.Q 0x800055b0#64 R Mt := by
  have HH := M.heap.heap.heap
  have hXm := M.keepX
  have hXb := HH.walk.chunk_bounds _ hXm
  have hS16 := (walk_sizes HH.walk _ hXm).1
  have hx16 := HH.aligned.1 _ hXm
  simp only at hXb hS16 hx16
  -- the new block's chunk `N` right after `X`
  obtain ⟨cN, hcN, huN, hcNa, hcNn⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
  simp only at hcNa hcNn
  obtain ⟨Na, ns, Ni⟩ := cN
  simp only at huN hcNa hcNn
  subst huN
  have hNa : Na = X + S := by omega
  subst hNa
  have hNb := HH.walk.chunk_bounds _ hcN
  have hns16 := (walk_sizes HH.walk _ hcN).1
  simp only at hNb hns16
  obtain ⟨cs₁, cs₂, hsp⟩ := List.append_of_mem hXm
  have hw := HH.walk
  rw [hsp] at hw
  obtain ⟨_, hnext⟩ := walk_next_of hw
  obtain ⟨cs₃, rfl⟩ : ∃ cs₃, cs₂ = ⟨X + S, ns, true⟩ :: cs₃ := by
    rcases hnext with ⟨he, _⟩ | ⟨d, cs₃, h1, h2⟩
    · exfalso; simp only at he; have := HH.walk.chunk_bounds _ hcN; simp only at this; omega
    · have hdm : d ∈ chunks := by rw [hsp, h1]; simp
      have := HH.chunk_eq hdm hcN (by simp only at h2 ⊢; omega)
      exact ⟨cs₃, by rw [h1, this]⟩
  have hbrk := HH.brk_le; have htle := HH.top_le
  unfold heapStart heapEnd at *
  obtain ⟨hX, hXr, hXs, hXl⟩ := walk_header HH.walk _ hXm
  obtain ⟨hN, hNr, hNs, hNl⟩ := walk_header HH.walk _ hcN
  simp only at hXr hXs hNr hNs
  have hNlt := Vsa.Sim.read64_lt _ _ _ hNr
  have hlo := O.sp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hNf : ∀ k, k < 8 → vsaFoot C.H (X + S + 8 + k) := fun k hk =>
    vsaFoot_cons_sub _ (vsaFoot_cons_sub _ (foot_header M.heap.heap (.inr ⟨_, hcN, rfl⟩) k hk))
  have eN : (R 10 + sign_extend (m := 64) (0xff8#12)).toNat = X + S + 8 := by
    rw [show (sign_extend (m := 64) (0xff8#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl,
      addr_sub M.a0 8 (by omega) (by omega)]; omega
  refine st_800055b0 O.live (by rw [eN]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [eN]; exact O.foot hNf) ?_
  rw [eN, ldv_at hNr _ rfl]
  refine st_800055b4 O.live ?_
  refine st_800055b8 O.live ?_
  refine st_800055bc O.live ?_
  have hns : (BitVec.ofNat 64 hN &&& sign_extend (m := 64) (0xffc#12)).toNat = ns := by
    rw [show (sign_extend (m := 64) (0xffc#12) : BitVec 64) = 18446744073709551612#64 from rfl,
      toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hNlt, ← hNs]; rfl
  -- the virtual heap: the new block dropped, `X` absorbing `N`, the block grown
  have hv : (BitVec.ofNat 64 (S + ns + hX % 2)).toNat = S + ns + hX % 2 := by
    rw [BitVec.toNat_ofNat]; omega
  generalize hV : writeLog Mt [(X + 8, 8, BitVec.ofNat 64 (S + ns + hX % 2))] = V
  have hVo : ∀ w, ¬ (X + 8 ≤ w ∧ w < X + 16) → V[w]? = Mt[w]? := fun w hw => by
    have ho : OutL [(X + 8, 8, BitVec.ofNat 64 (S + ns + hX % 2))] w := ⟨by simp only; omega, trivial⟩
    rw [← hV, writeLog_out _ _ _ ho]
  have H0 := M.heap
  rw [hsp] at H0
  have Ha := H0.drop.absorb (m' := V) (x := X) (a := S) (b := ns) (h' := S + ns + hX % 2)
    (fun e he heq => M.fresh.start e he (by rw [heq, hp']))
    (by rw [← hV, read64_store_hit, hv]) (by unfold chunkSize; omega) (by omega)
    (fun h0 hr => by
      rw [hXr] at hr; cases hr; unfold prevInuse; rw [show (S + ns + hX % 2) % 2 = hX % 2 by omega])
    (fun w _ hw _ => hVo w hw)
  have Hr := Ha.reblock (c := ⟨X, S + ns, true⟩) (by simp) rfl M.addr (n' := C.n.toNat)
    (by simp only; omega)
  rw [← M.addr] at Hr
  -- the header after the merged chunk
  have hw2 := HH.walk
  rw [hsp] at hw2
  obtain ⟨⟨hn, hnr, hnp⟩, _⟩ := walk_next_of (cs₁ := cs₁ ++ [⟨X, S, true⟩]) (by simpa using hw2)
  simp only at hnr hnp
  have hnodd : hn % 2 = 1 := by unfold prevInuse at hnp; simpa using hnp
  have hnb := M.nbok.eq
  refine realloc_tail O (V := V) (X := X) (S := S + ns) (nb := nb) (cs₁ := cs₁) (cs₂ := cs₃)
    ⟨M.frame.of_regs ?_ ?_ ?_, Hr, by rw [M.addr]; exact M.starts, M.top_le, M.nbok,
      by rw [hnb]; unfold physSize; omega, ⟨hX, hXr, by rw [← hV, read64_store_hit, hv]⟩,
      ⟨hn, by rw [show X + (S + ns) + 8 = X + S + ns + 8 by omega]; exact hnr, by
        rw [show hn / 2 * 2 + 1 = hn by omega, ← hV, rd_miss (by omega),
          show X + (S + ns) + 8 = X + S + ns + 8 by omega]; exact hnr⟩,
      fun w _ hw _ => (hVo w hw).symm, M.pres, M.disj, M.disjD, by rw [M.addr]; exact M.data,
      by have := M.grow; omega, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · rw [M.s0]
  · exact M.s1
  · exact h12
  · rw [BitVec.toNat_add, h14, hns, Nat.mod_eq_of_lt (by omega)]
  · exact h15

/-- **NULL from the nested `_malloc_r`** (`0x80005364`): unlock and return NULL,
the old block kept. -/
theorem mal_null {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    (F : RFrame C R Mt) (h10 : R 10 = 0#64)
    (hheap : ∃ top brkv chunks bins, PHeapAt Mt ((B.p, B.nOld) :: C.H) top brkv chunks bins)
    (hpres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome)
    (hdata : ∀ k, k < B.nOld → Mt[B.p + k]? = some (B.old (B.p + k)))
    (hst : Starved C.top0 C.n.toNat) :
    AW C.live C.S C.Q 0x80005364#64 R Mt := by
  have hs64 := sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hsp := F.sp
  have e : ∀ c : Nat, c ≤ 16 → (R 2 + BitVec.ofNat 64 c).toNat = C.s.toNat - 64 + c := fun c hc => by
    rw [hsp, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
  have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  refine st_80005364 O.live (by rw [n0, e 0 (by omega)]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [n0, e 0 (by omega)]; exact O.stack (by unfold mHead; omega) (by omega)) ?_
  refine st_80005368 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n8, e 8 (by omega)]
        unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n8, e 8 (by omega)]
        exact O.stack (by unfold mHead; omega) (by omega)) ?_
  refine st_8000536c O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n16, e 16 (by omega)]
        unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n16, e 16 (by omega)]
        exact O.stack (by unfold mHead; omega) (by omega)) ?_
  refine st_80005370 O.live ?_
  refine st_80005374 O.live (fun _ => ?_) (fun hc => absurd ?_ hc)
  · sx_run [12] O.live at 0x800054c4
    refine repi0 O (F.of_regs ?_ ?_ ?_) fun R' hR h13 => O.null R' Mt ⟨hR, ?_, hheap, hpres, hdata, hst⟩ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *
    rw [h13]; rfl
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h10

/-- **Back from `_malloc_r` with a block** (`0x80005364`): reload the spills;
a new chunk right after the old one is merged (`mal_merge`), any other gets
the old payload (`mal_copy`) and the old block is freed (`mal_free`). -/
theorem mal_ok {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {X S nb p' top brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (M : RMal C B R Mt X S nb p' top brkv chunks bins) :
    AW C.live C.S C.Q 0x80005364#64 R Mt := by
  have HH := M.heap.heap.heap
  have hs64 := sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hsp := M.frame.sp
  have hXm := M.keepX
  have hXb := HH.walk.chunk_bounds _ hXm
  have hS16 := (walk_sizes HH.walk _ hXm).1
  have hx16 := HH.aligned.1 _ hXm
  have hbrk := HH.brk_le; have htle := HH.top_le
  simp only at hXb hS16 hx16
  unfold heapStart heapEnd at *
  obtain ⟨hX, hXr, hXs, hXl⟩ := walk_header HH.walk _ hXm
  simp only at hXr hXs
  have hXlt := Vsa.Sim.read64_lt _ _ _ hXr
  obtain ⟨_, hp'lo, hp'hi, hp'dj⟩ := M.fresh.block
  change heapStart ≤ p' at hp'lo
  change p' + C.n.toNat ≤ heapEnd at hp'hi
  unfold heapStart at hp'lo; unfold heapEnd at hp'hi
  have hnb := M.nbok.eq
  have e : ∀ c : Nat, c ≤ 16 → (R 2 + BitVec.ofNat 64 c).toNat = C.s.toNat - 64 + c := fun c hc => by
    rw [hsp, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
  have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  have hnblt : nb < 2 ^ 64 := by have := M.nb31; omega
  refine st_80005364 O.live (by rw [n0, e 0 (by omega)]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by rw [n0, e 0 (by omega)]; exact O.stack (by unfold mHead; omega) (by omega)) ?_
  rw [n0, e 0 (by omega), show C.s.toNat - 64 + 0 = C.s.toNat - 64 by omega, ldv_at M.spNb _ rfl]
  refine st_80005368 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n8, e 8 (by omega)]
        unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n8, e 8 (by omega)]
        exact O.stack (by unfold mHead; omega) (by omega)) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [n8, e 8 (by omega), ldv_at M.spX _ rfl]
  refine st_8000536c O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n16, e 16 (by omega)]
        unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n16, e 16 (by omega)]
        exact O.stack (by unfold mHead; omega) (by omega)) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [n16, e 16 (by omega), ldv_at M.spS _ rfl]
  refine st_80005370 O.live ?_
  refine st_80005374 O.live (fun hc => absurd hc ?_) (fun _ => ?_)
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]
    intro h0; have := congrArg BitVec.toNat h0; rw [M.a0] at this; simp at this; omega
  -- `X`'s header, unchanged in size
  have hXf : ∀ k, k < 8 → vsaFoot C.H (X + 8 + k) := fun k hk =>
    vsaFoot_cons_sub _ (vsaFoot_cons_sub _ (foot_header M.heap.heap (.inr ⟨_, hXm, rfl⟩) k hk))
  have eX : (R 8 + sign_extend (m := 64) (0xff8#12)).toNat = X + 8 := by
    rw [show (sign_extend (m := 64) (0xff8#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl,
      addr_sub M.s0 8 (by omega) (by omega)]; omega
  refine st_80005378 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eX]; unfold LdOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [eX]; exact O.foot hXf) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [eX, ldv_at hXr _ rfl]
  refine st_8000537c O.live ?_
  refine st_80005380 O.live ?_
  refine st_80005384 O.live ?_
  have hS' : (BitVec.ofNat 64 hX &&& sign_extend (m := 64) (0xffe#12)).toNat = S := by
    rw [show (sign_extend (m := 64) (0xffe#12) : BitVec 64) = 18446744073709551614#64 from rfl,
      toNat_and_m2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hXlt]
    unfold chunkSize at hXs; omega
  have hXv : (BitVec.ofNat 64 X).toNat = X := by rw [BitVec.toNat_ofNat]; omega
  have hN : (R 10 + sign_extend (m := 64) (0xff0#12)).toNat = p' - 16 := by
    rw [show (sign_extend (m := 64) (0xff0#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 16) from rfl,
      addr_sub M.a0 16 (by omega) (by omega)]
  refine st_80005388 O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  · -- the new chunk is right after `X`
    have hm : X + S = p' - 16 := by
      have := congrArg BitVec.toNat hc
      rw [BitVec.toNat_add, hXv, hS', hN, Nat.mod_eq_of_lt (by omega)] at this; exact this
    exact mal_merge O (M.of_regs (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])) (by omega)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hXv)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [BitVec.toNat_ofNat]; omega)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [BitVec.toNat_ofNat]; omega)
  -- copy the old payload into the new block
  have hne : X + S ≠ p' - 16 := fun h => hc (BitVec.eq_of_toNat_eq (by
    rw [BitVec.toNat_add, hXv, hS', hN, Nat.mod_eq_of_lt (by omega)]; exact h))
  have hst2 := M.starts2
  have hstN : Starts ((p', C.n.toNat) :: C.H) := by
    unfold Starts at *
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at *
    exact ⟨hst2.1.2, hst2.2.2⟩
  have HN : PHeapAt Mt ((p', C.n.toNat) :: C.H) top brkv chunks bins := (M.heap.perm mem_swap).drop
  have HO : PHeapAt Mt C.H top brkv chunks bins := M.heap.drop.drop
  have hnoX : ∀ e ∈ C.H, e.1 ≠ X + 16 := by
    have := M.starts; unfold Starts at this; rw [List.map_cons, List.nodup_cons] at this
    exact fun e he heq => this.1 (List.mem_map.2 ⟨e, he, by rw [heq, M.addr]⟩)
  have hsrcF : ∀ k, k < S - 8 → vsaFoot C.H (X + 16 + k) := fun k hk =>
    HO.payload_foot hXm hnoX _ (by simp only; omega) (by simp only; omega)
  have hdstF : ∀ k, k < C.n.toNat → vsaFoot C.H (p' + k) := HN.block_foot hstN
  have hSn : S - 8 < C.n.toNat := by rw [hnb] at M; have := M.lt; unfold physSize at this; omega
  -- where the new block lies relative to `X`
  obtain ⟨cN, hcN, _, hcNa, hcNn⟩ := HH.exact _ List.mem_cons_self List.mem_cons_self
  simp only at hcNa hcNn
  have hNb := HH.walk.chunk_bounds cN hcN
  have hov : p' ≤ X + 16 ∨ X + 16 + (S - 8) ≤ p' := by
    rcases HH.walk.chunk_sep cN hcN _ hXm with rfl | h3 | h3
    · exfalso; have := M.addr
      exact M.fresh.start (B.p, B.nOld) List.mem_cons_self (by simp only at hcNa ⊢; omega)
    · left; simp only at h3; omega
    · right; simp only at h3; omega
  have hstk : ∀ a, vsaFoot C.H a → a < C.s.toNat - 64 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc' => M.disjD a (by unfold allocHeadroom; omega) (by omega) ha
  have hslotD : C.s.toNat - 64 + 8 ≤ p' ∨ p' + (S - 8) ≤ C.s.toNat - 64 := by
    by_cases hA : C.s.toNat - 64 + 8 ≤ p'
    · exact .inl hA
    by_cases hB : p' + (S - 8) ≤ C.s.toNat - 64
    · exact .inr hB
    exfalso
    rcases Nat.lt_or_ge p' (C.s.toNat - 64) with h | h
    · have := hstk _ (hdstF (C.s.toNat - 64 - p') (by omega)); omega
    · have := hstk _ (hdstF 0 (by omega)); omega
  have hslotS : C.s.toNat - 64 + 8 ≤ X + 16 ∨ X + 16 + (S - 8) ≤ C.s.toNat - 64 := by
    by_cases hA : C.s.toNat - 64 + 8 ≤ X + 16
    · exact .inl hA
    by_cases hB : X + 16 + (S - 8) ≤ C.s.toNat - 64
    · exact .inr hB
    exfalso
    rcases Nat.lt_or_ge (X + 16) (C.s.toNat - 64) with h | h
    · have := hstk _ (hsrcF (C.s.toNat - 64 - (X + 16)) (by omega)); omega
    · have := hstk _ (hsrcF 0 (by omega)); omega
  have A : CPArgs C.S p' (X + 16) (S - 8) :=
    { n8 := by omega, d8 := by have := M.align; omega, s8 := by omega, ov := hov,
      dlo := by unfold Vsa.Sim.tohostAddr; omega, dhi := by omega,
      slo := by unfold Vsa.Sim.tohostAddr; omega, shi := by omega,
      sS := fun k hk => O.own _ (.inl (hsrcF k hk)), dS := fun k hk => O.own _ (.inl (hdstF k (by omega))) }
  refine mal_copy O A (by omega) hS16 hslotD hslotS ?_ ?_ ?_ ?_ ?_ fun R' Mc g2 g8 g9 g13 g18 g19 hMc => ?_ <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact M.s0
  · exact M.a0
  · rw [BitVec.toNat_ofNat]; omega
  · rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from rfl, BitVec.add_zero]
  · exact hsp
  -- the copied memory: the new block's first `S - 8` bytes, the slot at `sp`
  have hdS : p' + (S - 8) ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ p' := by
    by_cases hA : C.s.toNat ≤ p'
    · exact .inr hA
    by_cases hB : p' + (S - 8) ≤ C.s.toNat - 64
    · exact .inl hB
    exfalso
    rcases Nat.lt_or_ge p' (C.s.toNat - 64) with h | h
    · have := hstk _ (hdstF (C.s.toNat - 64 - p') (by omega)); omega
    · have := hstk _ (hdstF 0 (by omega)); omega
  have hL8 : 8 * ((S - 8) / 8) = S - 8 := by omega
  have hMcF : ∀ a, vsaFoot C.H a → Mc[a]? = (copyW Mt p' (X + 16) ((S - 8) / 8))[a]? := fun a ha =>
    hMc a (by have := hstk a ha; omega)
  have hMcS : ∀ a, C.s.toNat - 64 + 8 ≤ a → a < C.s.toNat → Mc[a]? = Mt[a]? := fun a h1 h2 => by
    rw [hMc a (by omega), copyW_out (by omega)]
  have hslot : ∀ a, C.s.toNat - 64 + 8 ≤ a → a + 8 ≤ C.s.toNat → read64 Mc a = read64 Mt a :=
    fun a h1 h2 => read64_keep fun k hk => hMcS _ (by omega) (by omega)
  have F := M.frame
  have hblk : ∀ a, vsaFoot ((p', C.n.toNat) :: (B.p, B.nOld) :: C.H) a → ¬ (p' ≤ a ∧ a < p' + (S - 8)) :=
    fun a ha hin => by
      rcases ha with hg | ⟨_, _, h3⟩
      · have := allocGlobal_off_arena _ hg; unfold heapStart heapEnd at this; omega
      · exact h3 _ List.mem_cons_self ⟨by simp only; omega, by simp only; omega⟩
  refine mal_free O (brkv := brkv) (chunks := chunks) (bins := bins) ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ ?_ ?_ ?_ M.align ?_ M.starts2 M.top_le ?_ M.disjD ?_
    (by have := M.grow; omega)
  · rw [g2]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact hsp
  · rw [hslot _ (by omega) (by omega)]; exact F.s0
  · rw [hslot _ (by omega) (by omega)]; exact F.s1
  · rw [hslot _ (by omega) (by omega)]; exact F.ra
  · rw [g18]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact F.s2
  · rw [g19]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact F.s3
  · rw [g8]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [M.s0, M.addr]
  · rw [g9]; simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact M.s1
  · rw [g13]; simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from rfl, BitVec.add_zero]; exact M.a0
  · refine M.heap.transport_read fun a ha => ?_
    have hf := vsaFoot_cons_sub a (vsaFoot_cons_sub a ha.1)
    rw [hMcF a hf, copyW_out (by have := hblk a ha.1; omega)]
  · intro a ha; rw [hMcF a ha]; exact copyW_present (M.pres a ha)
  · intro k hk
    have hk' : k < C.n.toNat := by have := M.grow; omega
    have hold := M.grow
    have hS8 : B.nOld + 8 ≤ S := by
      obtain ⟨c0, hc0, _, hc0a, hc0n⟩ := HH.exact (B.p, B.nOld) (List.mem_cons_of_mem _ List.mem_cons_self)
        (List.mem_cons_of_mem _ List.mem_cons_self)
      have := HH.chunk_eq hc0 hXm (by simp only at hc0a ⊢; have := M.addr; omega)
      subst this; simpa using hc0n
    rw [hMcF _ (hdstF k hk'), copyW_spec (by rw [hL8]; exact hov)
      (fun i hi => M.pres _ (hsrcF i (by omega))) k (by omega),
      show X + 16 + k = B.p + k by rw [M.addr]]
    exact M.data k hk

/-- **The malloc path** (`0x80005350`): spill `S`, `X` and `nb`, call
`_malloc_r(n)`, and continue on its result (`mal_ok`, `mal_null`). -/
theorem realloc_mal {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {X S hdr0 nb : Nat}
    (D : RD C B R Mt brkv chunks bins X S hdr0 nb) :
    AW C.live C.S C.Q 0x80005350#64 R Mt := by
  have hs64 := sp64_toNat O.spA
  have hlo := O.spA.lo; have hhi := O.spA.hi; have hal := O.spA.align
  unfold allocHeadroom Vsa.Sim.tohostAddr at hlo
  have hsp := D.frame.sp
  have e : ∀ c : Nat, c ≤ 16 → (R 2 + BitVec.ofNat 64 c).toNat = C.s.toNat - 64 + c := fun c hc => by
    rw [hsp, BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
  have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
  have n16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 16 := rfl
  refine st_80005350 O.live ?_
  refine st_80005354 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n16, e 16 (by omega)]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n16, e 16 (by omega)]
        exact O.stack (by unfold mHead; omega) (by omega)) ?_
  refine st_80005358 O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n8, e 8 (by omega)]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n8, e 8 (by omega)]
        exact O.stack (by unfold mHead; omega) (by omega)) ?_
  refine st_8000535c O.live
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n0, e 0 (by omega)]
        unfold StOK Vsa.Sim.tohostAddr; omega)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n0, e 0 (by omega)]
        exact O.stack (by unfold mHead; omega) (by omega)) ?_
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [n16, e 16 (by omega), n8, e 8 (by omega), n0, e 0 (by omega)]
  refine st_80005360 O.live ?_
  simp only [VsaIris.ra]
  have Hp := ((D.heap.store_stack (a := C.s.toNat - 64 + 16) (w := 8) (v := R 14) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 64 + 8) (w := 8) (v := R 12) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 64 + 0) (w := 8) (v := R 15) (by unfold mHead; omega)
    (by omega)
  generalize hM1 : writeLog (writeLog (writeLog Mt [(C.s.toNat - 64 + 16, 8, R 14)])
    [(C.s.toNat - 64 + 8, 8, R 12)]) [(C.s.toNat - 64 + 0, 8, R 15)] = M1 at Hp ⊢
  have hrd : ∀ a, a + 8 ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ a → read64 M1 a = read64 Mt a := fun a ha => by
    rw [← hM1, rd_miss (by omega), rd_miss (by omega), rd_miss (by omega)]
  have hX8 : read64 M1 (B.p - 8) = some hdr0 := by
    have := D.addr; have := D.hdr
    rw [hrd _ (by
      have hf := foot_header D.heap.heap.heap (.inr ⟨_, D.mem, rfl⟩)
      have := off_stack_of D.heap.disj fun k hk => vsaFoot_cons_sub _ (hf k hk)
      simp only at this; omega), show B.p - 8 = X + 8 by omega]
    exact D.hdr
  -- the spills and the frame words are off the callee's window
  have hwin : ∀ a, C.s.toNat - 64 ≤ a → a < C.s.toNat → ¬ MWin ((B.p, B.nOld) :: C.H)
      (C.s + 18446744073709551552#64) a := fun a h1 h2 hw => by
    rcases hw with hf | ⟨h3, h4⟩
    · exact D.heap.disj a (by unfold mHead; omega) h2 (vsaFoot_cons_sub a hf)
    · rw [hs64] at h4; omega
  have hFr : ∀ (Mt' : Mem), (∀ a, ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) a →
      Mt'[a]? = M1[a]?) → ∀ a, C.s.toNat - 64 ≤ a → a + 8 ≤ C.s.toNat → read64 Mt' a = read64 M1 a :=
    fun Mt' hf a h1 h2 => read64_keep fun k hk => hf _ (hwin _ (by omega) (by omega))
  -- block bytes are off the callee's window too
  have hbA : ∀ k, k < B.nOld → heapStart ≤ B.p + k ∧ B.p + k < heapEnd := by
    obtain ⟨c, hc, _, h8, h9⟩ := D.heap.heap.heap.heap.live _ List.mem_cons_self
    have := D.heap.heap.heap.heap.walk.chunk_bounds c hc
    have := D.heap.heap.heap.heap.brk_le; have := D.heap.heap.heap.heap.top_le
    have := D.heap.heap.heap.top_room
    simp only at h8 h9; intro k hk; unfold heapStart heapEnd at *; omega
  have hblkw : ∀ k, k < B.nOld → ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) (B.p + k) :=
    fun k hk hw => by
      obtain ⟨hA1, hA2⟩ := hbA k hk
      rcases hw with hf' | ⟨h3, h4⟩
      · rcases hf' with hg | ⟨_, _, h5⟩
        · have := allocGlobal_off_arena _ hg; omega
        · exact h5 _ List.mem_cons_self ⟨by simp only; omega, by simp only; omega⟩
      · rw [hs64] at h3 h4
        exact D.heap.disjD _ (win64_le h3) (by omega) (D.heap.blk k hk)
  have hbd : ∀ k, k < B.nOld → M1[B.p + k]? = some (B.old (B.p + k)) := fun k hk => by
    exact Hp.data k hk
  have hsl : ∀ Mt' : Mem, (∀ a, ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) a →
      Mt'[a]? = M1[a]?) → ∀ a, vsaFoot C.H a → ¬ vsaFoot ((B.p, B.nOld) :: C.H) a →
      (Mt'[a]?).isSome ∧ ∀ k, k < B.nOld → Mt'[B.p + k]? = some (B.old (B.p + k)) :=
    fun Mt' hf a ha hna => ⟨by
      rw [hf a fun hw => ?_]
      · exact Hp.pres a ha
      rcases hw with hf' | ⟨h3, h4⟩
      · exact hna hf'
      · rw [hs64] at h3 h4; exact D.heap.disjD _ (win64_le h3) (by omega) ha,
      fun k hk => by rw [hf _ (hblkw k hk)]; exact hbd k hk⟩
  have hpres' : ∀ Mt' : Mem, (∀ a, ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) a →
      Mt'[a]? = M1[a]?) → (∀ a, vsaFoot ((B.p, B.nOld) :: C.H) a → (Mt'[a]?).isSome) →
      ∀ a, vsaFoot C.H a → (Mt'[a]?).isSome := fun Mt' hf hp a ha => by
    by_cases h : vsaFoot ((B.p, B.nOld) :: C.H) a
    · exact hp a h
    · exact (hsl Mt' hf a ha h).1
  have hdata' : ∀ Mt' : Mem, (∀ a, ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) a →
      Mt'[a]? = M1[a]?) → ∀ k, k < B.nOld → Mt'[B.p + k]? = some (B.old (B.p + k)) :=
    fun Mt' hf k hk => by rw [hf _ (hblkw k hk)]; exact hbd k hk
  have hF : ∀ (R' : Nat → BitVec 64) (Mt' : Mem), R' 2 = R 2 → R' 18 = R 18 → R' 19 = R 19 →
      (∀ a, ¬ MWin ((B.p, B.nOld) :: C.H) (C.s + 18446744073709551552#64) a → Mt'[a]? = M1[a]?) →
      RFrame C R' Mt' := fun R' Mt' g2 g18 g19 hf => by
    have F := D.frame
    refine ⟨g2.trans hsp, ?_, ?_, ?_, g18.trans F.s2, g19.trans F.s3⟩ <;>
      rw [hFr Mt' hf _ (by omega) (by omega), ← hM1, rd_miss (by omega), rd_miss (by omega),
        rd_miss (by omega)]
    · exact F.s0
    · exact F.s1
    · exact F.ra
  refine rcall_malloc O (n := C.n) (link := 0x80005364#64) (by decide) (fun a ha => vsaFoot_cons_sub a ha) ?_ ?_ ?_ ?_
    Hp.heap (fun a ha => Hp.pres a (vsaFoot_cons_sub a ha)) D.heap.disjD
    (fun R' Mt' g1 g2 g8 g9 g18 g19 hfr hal' hheap' hpres'' hframe' => ?_)
    (fun R' Mt' g1 g2 g8 g9 g18 g19 h10 hheap' hpres'' hframe' hst => ?_) <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact hsp
  · rw [D.s1]; rfl
  · exact D.a1
  · -- a fresh block
    obtain ⟨top', brkv', chunks', bins', H', htop', hkeep⟩ := hheap'
    simp only [upd_apply, Nat.reduceEqDiff, ite_false] at g2 g8 g9 g18 g19
    have F' := hF R' Mt' g2 g18 g19 hframe'
    have hkX : (⟨X, S, true⟩ : Chunk) ∈ chunks' := by
      have := hkeep (B.p, B.nOld) List.mem_cons_self hdr0 hX8
      have ha := D.addr; have hs := D.hsz
      simp only at this
      rwa [show B.p - 16 = X by omega, hs] at this
    refine mal_ok O (X := X) (S := S) (nb := nb) (p' := (R' 10).toNat)
      ⟨F', ?_, ?_, ?_, H', by omega, hfr, hal', hkX, D.addr, D.heap.starts, hpres' Mt' hframe' hpres'',
        D.heap.disj, D.heap.disjD, hdata' Mt' hframe', D.nbok, D.nb31, D.lt, D.heap.grow, ?_, ?_, rfl⟩
    · rw [hFr Mt' hframe' _ (by omega) (by omega), ← hM1,
        show C.s.toNat - 64 = C.s.toNat - 64 + 0 by omega, read64_store_hit, D.a5]
    · rw [hFr Mt' hframe' _ (by omega) (by omega), ← hM1, rd_miss (by omega), read64_store_hit, D.a2]
    · rw [hFr Mt' hframe' _ (by omega) (by omega), ← hM1, rd_miss (by omega), rd_miss (by omega),
        read64_store_hit, D.a4]
    · rw [g8, D.s0]
    · rw [g9, D.s1]
  · -- NULL
    simp only [upd_apply, Nat.reduceEqDiff, ite_false] at g2 g8 g9 g18 g19
    exact mal_null O (hF R' Mt' g2 g18 g19 hframe') h10 hheap' (hpres' Mt' hframe' hpres'')
      (hdata' Mt' hframe') hst

end VsaIris.VsaHeap
