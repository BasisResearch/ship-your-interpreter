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

/-- A forward copy of `n` bytes from `s` to `d`: word multiples, 8-aligned
pointers, the destination not above the source or wholly above it, both
ranges in RAM above the HTIF words and owned. -/
structure CPArgs (S : Nat → Prop) (d s n : Nat) : Prop where
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

/-- `memmove(d, s, n)`'s arguments on `_realloc_r`'s forward path. -/
structure MMArgs (S : Nat → Prop) (d s n : Nat) : Prop extends CPArgs S d s n where
  n32 : 32 ≤ n

theorem CPArgs.ld {S : Nat → Prop} {d s n : Nat} (A : CPArgs S d s n) {a : Nat} (h1 : s ≤ a)
    (h2 : a + 8 ≤ s + n) : LdOK a 8 ∧ ∀ b ∈ accAddrs a 8, S b := by
  have := A.slo; have := A.shi
  unfold Vsa.Sim.tohostAddr at *
  refine ⟨by unfold LdOK Vsa.Sim.tohostAddr; omega, fun b hb => ?_⟩
  obtain ⟨hb1, hb2⟩ := of_mem_accAddrs hb
  have := A.sS (b - s) (by omega)
  rwa [show s + (b - s) = b by omega] at this

theorem CPArgs.st {S : Nat → Prop} {d s n : Nat} (A : CPArgs S d s n) {a : Nat} (h1 : d ≤ a)
    (h2 : a + 8 ≤ d + n) (h8 : a % 8 = 0) : StOK a 8 ∧ ∀ b ∈ accAddrs a 8, S b := by
  have := A.dlo; have := A.dhi
  unfold Vsa.Sim.tohostAddr at *
  refine ⟨by unfold StOK Vsa.Sim.tohostAddr; omega, fun b hb => ?_⟩
  obtain ⟨hb1, hb2⟩ := of_mem_accAddrs hb
  have := A.dS (b - d) (by omega)
  rwa [show d + (b - d) = b by omega] at this

theorem MMArgs.ld {S : Nat → Prop} {d s n : Nat} (A : MMArgs S d s n) {a : Nat} (h1 : s ≤ a)
    (h2 : a + 8 ≤ s + n) : LdOK a 8 ∧ ∀ b ∈ accAddrs a 8, S b := A.toCPArgs.ld h1 h2

theorem MMArgs.st {S : Nat → Prop} {d s n : Nat} (A : MMArgs S d s n) {a : Nat} (h1 : d ≤ a)
    (h2 : a + 8 ≤ d + n) (h8 : a % 8 = 0) : StOK a 8 ∧ ∀ b ∈ accAddrs a 8, S b := A.toCPArgs.st h1 h2 h8

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

theorem and24 (n : Nat) (h : n % 8 = 0) : n &&& 24 = n % 32 := by
  have h1 : n &&& 24 = (n % 2 ^ 5) &&& 24 := by
    apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_mod_two_pow]
    by_cases hi : i < 5
    · simp [hi]
    · have : Nat.testBit 24 i = false := by
        apply Nat.testBit_lt_two_pow
        exact Nat.lt_of_lt_of_le (by decide : 24 < 2 ^ 5) (Nat.pow_le_pow_right (by decide) (by omega))
      simp [this]
  rw [h1]
  have : n % 32 = 0 ∨ n % 32 = 8 ∨ n % 32 = 16 ∨ n % 32 = 24 := by omega
  rcases this with h | h | h | h <;> simp only [show (2:Nat) ^ 5 = 32 from rfl, h] <;> decide

theorem or8 (a b : Nat) (ha : a % 8 = 0) (hb : b % 8 = 0) : (a ||| b) % 8 = 0 := by
  have := Nat.or_mod_two_pow (a := a) (b := b) (n := 3)
  simp only [show (2:Nat)^3 = 8 from rfl, ha, hb] at this
  rw [this]; rfl

theorem andm_toNat (x : BitVec 64) (k : Nat) (hk : k < 2 ^ 64) :
    (x &&& BitVec.ofNat 64 k).toNat = x.toNat &&& k := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk]

theorem toNat_and_m8 (x : BitVec 64) : (x &&& 18446744073709551608#64).toNat = x.toNat / 8 * 8 := by
  rw [show (18446744073709551608#64 : BitVec 64) = BitVec.allOnes 64 <<< 3 by decide,
    VsaIris.MallocFast.and_high_toNat x 3 (by decide)]

theorem shr5_toNat (x : BitVec 64) : (x >>> 5).toNat = x.toNat / 32 := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem shl5_toNat {x : BitVec 64} (h : x.toNat * 32 < 2 ^ 64) : (x <<< 5).toNat = x.toNat * 32 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by simpa using h)]

/-- **Between the loops** (`0x80006a74`): the words the 32-byte loop left,
by the 8-byte loop, then the return. -/
theorem mm_post {M0 : Mem} {d s n : Nat} (A : MMArgs S d s n) (hlive : ∀ p ∈ allocText, live p.1)
    {R0 : Nat → BitVec 64} (hra : (R0 1).toNat % 4 = 0) (h0 : (R0 10).toNat = d)
    (hk : ∀ R', MMKeep R0 R' → AW live S Q (R0 1) R' (copyW M0 d s (n / 8)))
    (R : Nat → BitVec 64) (hK : MMKeep R0 R) (h12 : (R 12).toNat = n) (h15 : (R 15).toNat = n / 32 - 1)
    (h17 : (R 17).toNat = s) (h14 : (R 14).toNat = d + 32 * (n / 32))
    (h16 : (R 16).toNat = d + 32 * (n / 32)) :
    AW live S Q 0x80006a74#64 R (copyW M0 d s (4 * (n / 32))) := by
  have hn := A.n32; have hn8 := A.n8; have hshi := A.shi; have hdhi := A.dhi
  have hq : 32 * (n / 32) ≤ n := Nat.mul_div_le n 32
  have hq1 : 1 ≤ n / 32 := by omega
  have k10 : (R 10).toNat = d := by rw [hK.a0, h0]
  have kra : R 1 = R0 1 := hK.ra
  -- the return, from any state whose `a2` is zero
  have hret : ∀ R' (M : Mem), MMKeep R0 R' → R' 12 = 0#64 → M = copyW M0 d s (n / 8) →
      AW live S Q 0x800069fc#64 R' M := by
    intro R' M hK' h0' hM
    subst hM
    refine st_800069fc hlive ?_
    refine st_80006a00 hlive (fun _ => ?_) (fun hc => absurd ?_ hc)
    · refine st_80006ae0 hlive (by rw [upd_other _ _ (by decide), hK'.ra]; exact hra) ?_
      rw [upd_other _ _ (by decide), hK'.ra]
      exact hk _ (by mm_keep hK')
    · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h0'
  sx_run [8] hlive at 0x80006a94
  have e5 : (R 15 <<< 5).toNat = 32 * (n / 32 - 1) := by rw [shl5_toNat (by rw [h15]; omega), h15]; omega
  have e14 : (R 15 <<< 5 + R 17).toNat = s + 32 * (n / 32 - 1) := by
    rw [BitVec.toNat_add, e5, h17, Nat.mod_eq_of_lt (by omega)]; omega
  have e11 : (R 15 <<< 5 + R 17 + 32#64).toNat = s + 32 * (n / 32) := by
    rw [BitVec.toNat_add, e14]; simp; omega
  have e24 : (R 12 &&& 24#64).toNat = n % 32 := by
    rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 24 from rfl, andm_toNat _ _ (by decide), h12,
      and24 n hn8]
  have e31 : (R 12 &&& 31#64).toNat = n % 32 := by
    rw [show (31#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 5 - 1) from rfl, andm_toNat _ _ (by decide),
      h12, Nat.and_two_pow_sub_one_eq_mod]
  refine st_80006a94 hlive (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  · -- no words left
    have h32 : n % 32 = 0 := by rw [← e24, hc]; rfl
    refine st_80006ae4 hlive ?_
    refine st_80006ae8 hlive ?_
    refine hret _ _ (by mm_keep hK) ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; sx_norm
      apply BitVec.eq_of_toNat_eq; rw [e31, h32]; rfl
    · congr 1; omega
  -- the 8-byte loop over the `n % 32 / 8` words left
  have h32 : n % 32 ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by rw [e24, h]; rfl))
  sx_run [5] hlive at 0x80006aac
  have ea3 : ((R 12 &&& 31#64) + 18446744073709551608#64 &&& 18446744073709551608#64).toNat =
      n % 32 - 8 := by
    rw [toNat_and_m8, show (18446744073709551608#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 8) from rfl,
      addr_sub e31 8 (by omega) (by omega)]
    omega
  have e4 : (R 15 <<< 5 + R 17 + ((R 12 &&& 31#64) + 18446744073709551608#64 &&& 18446744073709551608#64) +
      40#64).toNat = s + 32 * (n / 32) + 8 * (n % 32 / 8) := by
    rw [BitVec.toNat_add, BitVec.toNat_add, e14, ea3]; simp; omega
  have hR17 : R 17 = BitVec.ofNat 64 s := BitVec.eq_of_toNat_eq (by rw [h17, BitVec.toNat_ofNat]; omega)
  rw [show 4 * (n / 32) = 32 * (n / 32) / 8 + 0 by omega]
  refine mm_l8 A hlive (R0 := R0) (c := 32 * (n / 32)) (w := n % 32 / 8) (by omega) ?_ (by omega)
    (n % 32 / 8) 0 _ (by omega) (by omega) (by mm_keep hK) ?_ ?_ ?_ ?_ ?_
  · -- after the 8-byte loop
    intro R' hK' g12 g11
    sx_run [6] hlive at 0x800069fc
    refine hret _ _ (by mm_keep hK') ?_ ?_
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      apply BitVec.eq_of_toNat_eq
      rw [show (7#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 3 - 1) from rfl, andm_toNat _ _ (by decide),
        Nat.and_two_pow_sub_one_eq_mod, g12]; simp; omega
    · congr 1; omega
  all_goals simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exact k10
  · rw [e11]; omega
  · exact h12
  · rw [e4]
  · rw [hR17]

/-- **`memmove(d, s, n)` forwards** (`0x800069c4`): back at `ra` with the
callee-saved registers, `a0` and `sp` kept and the source's `n / 8` words at
the destination. -/
theorem memmove_fwd {M0 : Mem} {d s n : Nat} (A : MMArgs S d s n) (hlive : ∀ p ∈ allocText, live p.1)
    {R : Nat → BitVec 64} (h10 : (R 10).toNat = d) (h11 : (R 11).toNat = s) (h12 : (R 12).toNat = n)
    (hra : (R 1).toNat % 4 = 0)
    (hk : ∀ R', MMKeep R R' → AW live S Q (R 1) R' (copyW M0 d s (n / 8))) :
    AW live S Q 0x800069c4#64 R M0 := by
  have hn := A.n32; have hn8 := A.n8; have hd8 := A.d8; have hs8 := A.s8; have hov := A.ov
  have hdhi := A.dhi; have hshi := A.shi
  -- the forward path
  have hfwd : ∀ R', MMKeep R R' → R' 10 = R 10 → R' 11 = R 11 → R' 12 = R 12 →
      AW live S Q 0x800069f0#64 R' M0 := by
    intro R' hK g10 g11 g12
    have k10 : (R' 10).toNat = d := by rw [g10, h10]
    have k11 : (R' 11).toNat = s := by rw [g11, h11]
    have k12 : (R' 12).toNat = n := by rw [g12, h12]
    clear g10 g11 g12
    refine st_800069f0 hlive ?_
    refine st_800069f4 hlive (fun _ => ?_) (fun hc => absurd ?_ hc)
    rotate_left
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [k12]
      show 31 < n; omega
    sx_run [4] hlive at 0x80006a30
    have hal : (R' 10 ||| R' 11) &&& 7#64 = 0#64 := by
      apply BitVec.eq_of_toNat_eq
      rw [show (7#64 : BitVec 64) = BitVec.ofNat 64 (2 ^ 3 - 1) from rfl, andm_toNat _ _ (by decide),
        Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_or, k10, k11, or8 d s hd8 hs8]; rfl
    refine st_80006a30 hlive (fun hc => absurd ?_ hc) (fun _ => ?_)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact hal
    sx_run [5] hlive at 0x80006a48
    have hq1 : 1 ≤ n / 32 := by omega
    have hq : 32 * (n / 32) ≤ n := Nat.mul_div_le n 32
    have e15 : (R' 12 >>> 5).toNat = n / 32 := by rw [shr5_toNat, k12]
    have e16 : (R' 12 >>> 5 <<< 5).toNat = 32 * (n / 32) := by
      rw [shl5_toNat (by rw [e15]; omega), e15]; omega
    rw [show M0 = copyW M0 d s (4 * 0) from rfl]
    refine mm_l32 A hlive (R0 := R) (mm_post A hlive hra h10 hk) (n / 32) 0 _ (by omega) (by omega)
      (by mm_keep hK) ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact k10
    · rw [k11]; omega
    · exact k12
    · rw [k10]; omega
    · rw [BitVec.toNat_add, e15]; simp; omega
    · rw [BitVec.toNat_add, k10, e16, Nat.mod_eq_of_lt (by omega)]
    · exact k11
  refine st_800069c4 hlive (fun _ => hfwd R (MMKeep.refl R) rfl rfl rfl) (fun hc => ?_)
  rw [h10, h11] at hc
  refine st_800069c8 hlive ?_
  refine st_800069cc hlive (fun _ => hfwd _ (by mm_keep (MMKeep.refl R)) ?_ ?_ ?_) (fun hc' => ?_) <;>
    try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  · exfalso
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc'
    rw [BitVec.toNat_add, h11, h12, h10, Nat.mod_eq_of_lt (by omega)] at hc'
    omega

end Loops

end VsaIris.VsaHeap
