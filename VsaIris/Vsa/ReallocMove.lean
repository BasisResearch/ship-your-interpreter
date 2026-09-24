import VsaIris.Vsa.ReallocCopy

/-!
# `memmove`'s forward copy

`_realloc_r` calls `memmove(d, s, n)` for payloads over 72 bytes: `n` a
multiple of 8, both pointers 8-aligned, and the destination not above the
source or wholly above it. `memmove` then takes its forward path: a 32-byte
loop (`mm_l32`) and an 8-byte loop (`mm_l8`), each storing the source's words
in order, so the memory at the return is `copyW m d s (n / 8)`
(`memmove_fwd`). The lemmas are stated for any `AW` context: the caller
supplies ownership of both ranges.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `memmove(d, s, n)`'s arguments on `_realloc_r`'s forward path. -/
structure MMArgs (S : Nat → Prop) (d s n : Nat) : Prop where
  n32 : 32 ≤ n
  n8 : n % 8 = 0
  d8 : d % 8 = 0
  s8 : s % 8 = 0
  ov : d ≤ s ∨ s + n ≤ d
  dlo : Vsa.Sim.tohostAddr + 16 ≤ d
  dhi : d + n ≤ 0x100000000
  slo : Vsa.Sim.tohostAddr + 16 ≤ s
  shi : s + n ≤ 0x100000000
  sS : ∀ k, k < n → S (s + k)
  dS : ∀ k, k < n → S (d + k)

theorem MMArgs.ld {S : Nat → Prop} {d s n : Nat} (A : MMArgs S d s n) {a : Nat} (h1 : s ≤ a)
    (h2 : a + 8 ≤ s + n) : LdOK a 8 ∧ ∀ b ∈ accAddrs a 8, S b := by
  have := A.slo; have := A.shi
  unfold Vsa.Sim.tohostAddr at *
  refine ⟨by unfold LdOK Vsa.Sim.tohostAddr; omega, fun b hb => ?_⟩
  obtain ⟨hb1, hb2⟩ := of_mem_accAddrs hb
  have := A.sS (b - s) (by omega)
  rwa [show s + (b - s) = b by omega] at this

theorem MMArgs.st {S : Nat → Prop} {d s n : Nat} (A : MMArgs S d s n) {a : Nat} (h1 : d ≤ a)
    (h2 : a + 8 ≤ d + n) (h8 : a % 8 = 0) : StOK a 8 ∧ ∀ b ∈ accAddrs a 8, S b := by
  have := A.dlo; have := A.dhi
  unfold Vsa.Sim.tohostAddr at *
  refine ⟨by unfold StOK Vsa.Sim.tohostAddr; omega, fun b hb => ?_⟩
  obtain ⟨hb1, hb2⟩ := of_mem_accAddrs hb
  have := A.dS (b - d) (by omega)
  rwa [show d + (b - d) = b by omega] at this

/-- The registers `memmove` keeps. -/
structure MMKeep (R R' : Nat → BitVec 64) : Prop where
  ra : R' 1 = R 1
  sp : R' 2 = R 2
  s0 : R' 8 = R 8
  s1 : R' 9 = R 9
  a0 : R' 10 = R 10
  s2 : R' 18 = R 18
  s3 : R' 19 = R 19

theorem MMKeep.refl (R : Nat → BitVec 64) : MMKeep R R := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem MMKeep.trans {R R' R'' : Nat → BitVec 64} (h : MMKeep R R') (h' : MMKeep R' R'') :
    MMKeep R R'' :=
  ⟨h'.ra.trans h.ra, h'.sp.trans h.sp, h'.s0.trans h.s0, h'.s1.trans h.s1, h'.a0.trans h.a0,
    h'.s2.trans h.s2, h'.s3.trans h.s3⟩

theorem MMKeep.of_eq {R R' R'' : Nat → BitVec 64} (h : MMKeep R R') (e1 : R'' 1 = R' 1)
    (e2 : R'' 2 = R' 2) (e8 : R'' 8 = R' 8) (e9 : R'' 9 = R' 9) (e10 : R'' 10 = R' 10)
    (e18 : R'' 18 = R' 18) (e19 : R'' 19 = R' 19) : MMKeep R R'' :=
  ⟨e1.trans h.ra, e2.trans h.sp, e8.trans h.s0, e9.trans h.s1, e10.trans h.a0, e18.trans h.s2,
    e19.trans h.s3⟩

/-- `MMKeep` through a chain of writes to other registers, by `simp`. -/
macro "mm_keep" h:term : tactic => `(tactic| (refine MMKeep.of_eq $h ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]))

theorem MMKeep.upd {R R' : Nat → BitVec 64} (h : MMKeep R R') {k : Nat} (v : BitVec 64)
    (hk : k ≠ 1 ∧ k ≠ 2 ∧ k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10 ∧ k ≠ 18 ∧ k ≠ 19) : MMKeep R (upd R' k v) := by
  obtain ⟨h1, h2, h8, h9, h10, h18, h19⟩ := hk
  exact ⟨by rw [upd_other _ _ (Ne.symm h1)]; exact h.ra, by rw [upd_other _ _ (Ne.symm h2)]; exact h.sp,
    by rw [upd_other _ _ (Ne.symm h8)]; exact h.s0, by rw [upd_other _ _ (Ne.symm h9)]; exact h.s1,
    by rw [upd_other _ _ (Ne.symm h10)]; exact h.a0, by rw [upd_other _ _ (Ne.symm h18)]; exact h.s2,
    by rw [upd_other _ _ (Ne.symm h19)]; exact h.s3⟩

section Loops

variable {live : Nat → Prop} {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- One `ld a3,offL(a1); sd a3,offS(a4)` pair of the 32-byte loop, copying word `j`. -/
theorem mm_pair {pcL pcS pcN : BitVec 64} {offL offS : BitVec 12} {R : Nat → BitVec 64}
    {M0 : Mem} {d s n j : Nat} (A : MMArgs S d s n)
    (stL : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      LdOK ((R 11) + sign_extend (m := 64) offL).toNat 8 →
      (∀ b ∈ accAddrs ((R 11) + sign_extend (m := 64) offL).toNat 8, S b) →
      AW live S Q pcS (upd R 13 (ldv .ld Mt ((R 11) + sign_extend (m := 64) offL).toNat)) Mt →
      AW live S Q pcL R Mt)
    (stS : ∀ {R : Nat → BitVec 64} {Mt : Mem},
      StOK ((R 14) + sign_extend (m := 64) offS).toNat 8 →
      (∀ b ∈ accAddrs ((R 14) + sign_extend (m := 64) offS).toNat 8, S b) →
      AW live S Q pcN R (writeLog Mt [(((R 14) + sign_extend (m := 64) offS).toNat, 8, (R 13))]) →
      AW live S Q pcS R Mt)
    (hL : (R 11 + sign_extend (m := 64) offL).toNat = s + 8 * j)
    (hS : (R 14 + sign_extend (m := 64) offS).toNat = d + 8 * j) (hj : 8 * j + 8 ≤ n)
    (hk : AW live S Q pcN (upd R 13 (ldv .ld (copyW M0 d s j) (s + 8 * j))) (copyW M0 d s (j + 1))) :
    AW live S Q pcL R (copyW M0 d s j) := by
  have hd8 := A.d8
  obtain ⟨hl1, hl2⟩ := A.ld (a := s + 8 * j) (by omega) (by omega)
  obtain ⟨hs1, hs2⟩ := A.st (a := d + 8 * j) (by omega) (by omega) (by omega)
  refine stL (by rw [hL]; exact hl1) (by rw [hL]; exact hl2) ?_
  have hS' : ((upd R 13 (ldv .ld (copyW M0 d s j) (R 11 + sign_extend (m := 64) offL).toNat)) 14 +
      sign_extend (m := 64) offS).toNat = d + 8 * j := by rw [upd_other _ _ (by decide)]; exact hS
  refine stS (by rw [hS']; exact hs1) (by rw [hS']; exact hs2) ?_
  rw [hS', upd_same, hL, ← copyW_succ]
  exact hk

/-- `x + imm` for a small positive immediate or a negative one within range. -/
theorem addr_add {x : BitVec 64} {a : Nat} (hx : x.toNat = a) (c : Nat) (hc : a + c < 2 ^ 64) :
    (x + BitVec.ofNat 64 c).toNat = a + c := by
  rw [BitVec.toNat_add, hx, BitVec.toNat_ofNat]; omega

theorem addr_sub {x : BitVec 64} {a : Nat} (hx : x.toNat = a) (c : Nat) (hc : c ≤ a) (hpos : 0 < c) :
    (x + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = a - c := by
  rw [BitVec.toNat_add, hx, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 2 ^ 64 - c < 2 ^ 64 by omega)]
  have : a < 2 ^ 64 := by rw [← hx]; exact x.isLt
  · rw [show a + (2 ^ 64 - c) = (a - c) + 2 ^ 64 by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

/-- The rest of a 32-byte round (`0x80006a58`): words `4i+1 … 4i+3` and the
back edge. -/
theorem mm_l32_rest {M0 : Mem} {d s n : Nat} (A : MMArgs S d s n) (hlive : ∀ p ∈ allocText, live p.1)
    {R0 : Nat → BitVec 64} (i : Nat) (hi : i < n / 32) (R : Nat → BitVec 64)
    (hK : MMKeep R0 R) (h10 : (R 10).toNat = d) (h11 : (R 11).toNat = s + 32 * i + 32)
    (h12 : (R 12).toNat = n) (h14 : (R 14).toNat = d + 32 * i + 32) (h15 : (R 15).toNat = n / 32 - 1)
    (h16 : (R 16).toNat = d + 32 * (n / 32)) (h17 : (R 17).toNat = s)
    (hnext : ∀ R', i + 1 < n / 32 → MMKeep R0 R' → (R' 10).toNat = d →
      (R' 11).toNat = s + 32 * (i + 1) → (R' 12).toNat = n → (R' 14).toNat = d + 32 * (i + 1) →
      (R' 15).toNat = n / 32 - 1 → (R' 16).toNat = d + 32 * (n / 32) → (R' 17).toNat = s →
      AW live S Q 0x80006a48#64 R' (copyW M0 d s (4 * (i + 1))))
    (hk : ∀ R', MMKeep R0 R' → (R' 12).toNat = n → (R' 15).toNat = n / 32 - 1 → (R' 17).toNat = s →
      (R' 14).toNat = d + 32 * (n / 32) → (R' 16).toNat = d + 32 * (n / 32) →
      AW live S Q 0x80006a74#64 R' (copyW M0 d s (4 * (n / 32)))) :
    AW live S Q 0x80006a58#64 R (copyW M0 d s (4 * i + 1)) := by
  have hn := A.n32; have hdhi := A.dhi; have hshi := A.shi
  have hq : 32 * (n / 32) ≤ n := Nat.mul_div_le n 32
  have eL : ∀ (c k : Nat), 0 < c → c ≤ 32 → 32 - c = 8 * k →
      (R 11 + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = s + 8 * (4 * i + k) := fun c k h1 h2 h3 => by
    rw [addr_sub h11 c (by omega) h1]; omega
  have eS : ∀ (c k : Nat), 0 < c → c ≤ 32 → 32 - c = 8 * k →
      (R 14 + BitVec.ofNat 64 (2 ^ 64 - c)).toNat = d + 8 * (4 * i + k) := fun c k h1 h2 h3 => by
    rw [addr_sub h14 c (by omega) h1]; omega
  have n24 : (sign_extend (m := 64) (0xfe8#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 24) := rfl
  have n16 : (sign_extend (m := 64) (0xff0#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 16) := rfl
  have n8 : (sign_extend (m := 64) (0xff8#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 8) := rfl
  refine mm_pair A (st_80006a58 hlive) (st_80006a5c hlive)
    (by rw [n24]; exact eL 24 1 (by omega) (by omega) (by omega))
    (by rw [n24]; exact eS 24 1 (by omega) (by omega) (by omega)) (by omega) ?_
  have hK1 := hK.upd (ldv .ld (copyW M0 d s (4 * i + 1)) (s + 8 * (4 * i + 1))) (k := 13) (by decide)
  refine mm_pair A (st_80006a60 hlive) (st_80006a64 hlive)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n16]; exact eL 16 2 (by omega) (by omega) (by omega))
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n16]; exact eS 16 2 (by omega) (by omega) (by omega))
    (by omega) ?_
  refine mm_pair A (st_80006a68 hlive) (st_80006a6c hlive)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n8]; exact eL 8 3 (by omega) (by omega) (by omega))
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [n8]; exact eS 8 3 (by omega) (by omega) (by omega))
    (by omega) ?_
  rw [show 4 * i + 3 + 1 = 4 * (i + 1) by omega]
  have hK3 := ((hK.upd (k := 13) (ldv .ld (copyW M0 d s (4 * i + 1)) (s + 8 * (4 * i + 1))) (by decide)).upd
    (k := 13) (ldv .ld (copyW M0 d s (4 * i + 2)) (s + 8 * (4 * i + 2))) (by decide)).upd
    (k := 13) (ldv .ld (copyW M0 d s (4 * i + 3)) (s + 8 * (4 * i + 3))) (by decide)
  refine st_80006a70 hlive (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_false] at hc
  · have hlt : i + 1 < n / 32 := by
      have : i + 1 ≠ n / 32 := fun he => hc (BitVec.eq_of_toNat_eq (by rw [h14, h16, ← he]; omega))
      omega
    exact hnext _ hlt hK3 (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h10)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [h11]; omega)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h12)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [h14]; omega)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h15)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h16)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h17)
  · have heq : i + 1 = n / 32 := by
      have := congrArg BitVec.toNat (Decidable.of_not_not hc); rw [h14, h16] at this; omega
    rw [heq]
    exact hk _ hK3 (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h12)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h15)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h17)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [h14]; omega)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h16)

/-- `x + (y - z)` with `z ≤ x`, in range. -/
theorem add_sub_toNat {x y z : BitVec 64} {a b c : Nat} (hx : x.toNat = a) (hy : y.toNat = b)
    (hz : z.toNat = c) (hca : c ≤ a) (hlt : b + (a - c) < 2 ^ 64) :
    (x + (y - z)).toNat = b + (a - c) := by
  have hc : c < 2 ^ 64 := by rw [← hz]; exact z.isLt
  rw [BitVec.toNat_add, BitVec.toNat_sub, hx, hy, hz, Nat.add_mod_mod,
    show a + (2 ^ 64 - c + b) = (b + (a - c)) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt hlt]

/-- **The 32-byte loop** (`0x80006a48`), after `i` of its `n / 32` rounds. -/
theorem mm_l32 {M0 : Mem} {d s n : Nat} (A : MMArgs S d s n) (hlive : ∀ p ∈ allocText, live p.1)
    {R0 : Nat → BitVec 64}
    (hk : ∀ R', MMKeep R0 R' → (R' 12).toNat = n → (R' 15).toNat = n / 32 - 1 → (R' 17).toNat = s →
      (R' 14).toNat = d + 32 * (n / 32) → (R' 16).toNat = d + 32 * (n / 32) →
      AW live S Q 0x80006a74#64 R' (copyW M0 d s (4 * (n / 32)))) :
    ∀ k i (R : Nat → BitVec 64), n / 32 - i = k → i < n / 32 → MMKeep R0 R →
      (R 10).toNat = d → (R 11).toNat = s + 32 * i → (R 12).toNat = n → (R 14).toNat = d + 32 * i →
      (R 15).toNat = n / 32 - 1 → (R 16).toNat = d + 32 * (n / 32) → (R 17).toNat = s →
      AW live S Q 0x80006a48#64 R (copyW M0 d s (4 * i))
  | 0, i, R, hki, hi, _, _, _, _, _, _, _, _ => by omega
  | k + 1, i, R, hki, hi, hK, h10, h11, h12, h14, h15, h16, h17 => by
    have hn := A.n32; have hdhi := A.dhi; have hshi := A.shi; have hd8 := A.d8
    have hq : 32 * (n / 32) ≤ n := Nat.mul_div_le n 32
    have hi1 : 32 * i + 32 ≤ n := by omega
    -- word `4i`
    obtain ⟨hl1, hl2⟩ := A.ld (a := s + 8 * (4 * i)) (by omega) (by omega)
    obtain ⟨hs1, hs2⟩ := A.st (a := d + 8 * (4 * i)) (by omega) (by omega) (by omega)
    have e0 : (R 11 + sign_extend (m := 64) (0x000#12)).toNat = s + 8 * (4 * i) := by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 from rfl,
        addr_add h11 0 (by omega)]; omega
    refine st_80006a48 hlive (by rw [e0]; exact hl1) (by rw [e0]; exact hl2) ?_
    rw [e0]
    refine st_80006a4c hlive ?_
    refine st_80006a50 hlive ?_
    have h11' : ((upd (upd (upd R 13 (ldv .ld (copyW M0 d s (4 * i)) (s + 8 * (4 * i)))) 11
        ((upd R 13 (ldv .ld (copyW M0 d s (4 * i)) (s + 8 * (4 * i)))) 11 +
          sign_extend (m := 64) (0x020#12))) 14
        ((upd (upd R 13 (ldv .ld (copyW M0 d s (4 * i)) (s + 8 * (4 * i)))) 11
          ((upd R 13 (ldv .ld (copyW M0 d s (4 * i)) (s + 8 * (4 * i)))) 11 +
            sign_extend (m := 64) (0x020#12))) 14 + sign_extend (m := 64) (0x020#12))) 11).toNat =
        s + 32 * i + 32 := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [show (sign_extend (m := 64) (0x020#12) : BitVec 64) = BitVec.ofNat 64 32 from rfl,
        addr_add h11 32 (by omega)]
    have n32 : (sign_extend (m := 64) (0x020#12) : BitVec 64) = BitVec.ofNat 64 32 := rfl
    have e1 : ((upd (upd (upd R 13 (ldv .ld (copyW M0 d s (4 * i)) (s + 8 * (4 * i)))) 11
        ((upd R 13 (ldv .ld (copyW M0 d s (4 * i)) (s + 8 * (4 * i)))) 11 +
          sign_extend (m := 64) (0x020#12))) 14
        ((upd (upd R 13 (ldv .ld (copyW M0 d s (4 * i)) (s + 8 * (4 * i)))) 11
          ((upd R 13 (ldv .ld (copyW M0 d s (4 * i)) (s + 8 * (4 * i)))) 11 +
            sign_extend (m := 64) (0x020#12))) 14 + sign_extend (m := 64) (0x020#12))) 14 +
        sign_extend (m := 64) (0xfe0#12)).toNat = d + 8 * (4 * i) := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      rw [n32, show (sign_extend (m := 64) (0xfe0#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 32) from rfl,
        addr_sub (addr_add h14 32 (by omega)) 32 (by omega) (by omega)]
      omega
    refine st_80006a54 hlive (by rw [e1]; exact hs1) (by rw [e1]; exact hs2) ?_
    rw [e1]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [← copyW_succ]
    refine mm_l32_rest A hlive (R0 := R0) i hi _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      (fun R' hlt hK' g10 g11 g12 g14 g15 g16 g17 =>
        mm_l32 A hlive hk k (i + 1) R' (by omega) hlt hK' g10 g11 g12 g14 g15 g16 g17) hk
    · exact ((hK.upd (k := 13) _ (by decide)).upd (k := 11) _ (by decide)).upd (k := 14) _ (by decide)
    all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact h10
    · rw [n32, addr_add h11 32 (by omega)]
    · exact h12
    · rw [n32, addr_add h14 32 (by omega)]
    · exact h15
    · exact h16
    · exact h17

/-- **The 8-byte loop** (`0x80006aac`), after `j` of the `w` words left by
the 32-byte loop, which ends at `e = s + 32 q + 8 w`. -/
theorem mm_l8 {M0 : Mem} {d s n : Nat} (A : MMArgs S d s n) (hlive : ∀ p ∈ allocText, live p.1)
    {R0 : Nat → BitVec 64} {c w : Nat} (hcw : c + 8 * w ≤ n)
    (hk : ∀ R', MMKeep R0 R' → (R' 12).toNat = n → (R' 11).toNat = s + c + 8 * w →
      AW live S Q 0x80006ac0#64 R' (copyW M0 d s (c / 8 + w))) (hc8 : c % 8 = 0) :
    ∀ k j (R : Nat → BitVec 64), w - j = k → j < w → MMKeep R0 R →
      (R 10).toNat = d → (R 11).toNat = s + c + 8 * j → (R 12).toNat = n →
      (R 14).toNat = s + c + 8 * w → R 16 = R 10 - BitVec.ofNat 64 s →
      AW live S Q 0x80006aac#64 R (copyW M0 d s (c / 8 + j))
  | 0, j, R, hkj, hj, _, _, _, _, _, _ => by omega
  | k + 1, j, R, hkj, hj, hK, h10, h11, h12, h14, h16 => by
    have hn := A.n32; have hdhi := A.dhi; have hshi := A.shi; have hd8 := A.d8
    have ej : c / 8 + j = (c + 8 * j) / 8 := by omega
    obtain ⟨hl1, hl2⟩ := A.ld (a := s + 8 * (c / 8 + j)) (by omega) (by omega)
    obtain ⟨hs1, hs2⟩ := A.st (a := d + 8 * (c / 8 + j)) (by omega) (by omega) (by omega)
    have n0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 := rfl
    have n8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := rfl
    have eL : (R 11 + sign_extend (m := 64) (0x000#12)).toNat = s + 8 * (c / 8 + j) := by
      rw [n0, addr_add h11 0 (by omega)]; omega
    refine st_80006aac hlive (by rw [eL]; exact hl1) (by rw [eL]; exact hl2) ?_
    rw [eL]
    refine st_80006ab0 hlive ?_
    refine st_80006ab4 hlive ?_
    have eS : ((upd (upd (upd R 6 (ldv .ld (copyW M0 d s (c / 8 + j)) (s + 8 * (c / 8 + j)))) 17
        ((upd R 6 (ldv .ld (copyW M0 d s (c / 8 + j)) (s + 8 * (c / 8 + j)))) 11 +
          (upd R 6 (ldv .ld (copyW M0 d s (c / 8 + j)) (s + 8 * (c / 8 + j)))) 16)) 11
        ((upd (upd R 6 (ldv .ld (copyW M0 d s (c / 8 + j)) (s + 8 * (c / 8 + j)))) 17
          ((upd R 6 (ldv .ld (copyW M0 d s (c / 8 + j)) (s + 8 * (c / 8 + j)))) 11 +
            (upd R 6 (ldv .ld (copyW M0 d s (c / 8 + j)) (s + 8 * (c / 8 + j)))) 16)) 11 +
          sign_extend (m := 64) (0x008#12))) 17 + sign_extend (m := 64) (0x000#12)).toNat =
        d + 8 * (c / 8 + j) := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      have h17 : (BitVec.ofNat 64 s).toNat = s := by rw [BitVec.toNat_ofNat]; omega
      rw [n0, h16, addr_add (add_sub_toNat h11 h10 h17 (by omega) (by omega)) 0 (by omega)]
      omega
    refine st_80006ab8 hlive (by rw [eS]; exact hs1) (by rw [eS]; exact hs2) ?_
    rw [eS]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    rw [← copyW_succ]
    have g11 : (R 11 + sign_extend (m := 64) (0x008#12)).toNat = s + c + 8 * (j + 1) := by
      rw [n8, addr_add h11 8 (by omega)]; omega
    refine st_80006abc hlive (fun hc => ?_) (fun hc => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
    · have hlt : j + 1 < w := by
        have : j + 1 ≠ w := fun he => hc (BitVec.eq_of_toNat_eq (by rw [g11, h14, ← he]))
        omega
      exact mm_l8 A hlive hcw hk hc8 k (j + 1) _ (by omega) hlt (by mm_keep hK)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h10)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact g11)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h12)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h14)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h16)
    · have heq : j + 1 = w := by
        have := congrArg BitVec.toNat (Decidable.of_not_not hc); rw [g11, h14] at this; omega
      rw [show c / 8 + j + 1 = c / 8 + w by omega]
      exact hk _ (by mm_keep hK) (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h12)
        (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [g11, heq])

end Loops

end VsaIris.VsaHeap
