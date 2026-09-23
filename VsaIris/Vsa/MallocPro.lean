import VsaIris.Vsa.MallocPaths

/-!
# `_malloc_r`'s prologue

From the entry to the first join: the frame, the request's chunk size
(`request2size`), and the dispatch to the small-bin join `j_small`, the
large-bin index at `0x80004884`, or the error return (`errno := ENOMEM`,
NULL) for a request no chunk can hold.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The reentrancy structure `_impure_ptr` points at (its first word is `_errno`). -/
abbrev reentV : BitVec 64 := 0x8001b538#64

/-- `_malloc_r`'s registers at its entry. -/
structure MEntry (C : MCtx) (R : Nat → BitVec 64) : Prop where
  ra : R 1 = C.r
  sp : R 2 = C.s
  a0 : R 10 = reentV
  a1 : R 11 = C.n
  s0 : R 8 = C.rv0 8
  s1 : R 9 = C.rv0 9
  s2 : R 18 = C.rv0 18
  s3 : R 19 = C.rv0 19

/-- The `_errno` word is in the footprint. -/
theorem errno_foot {H : List (Nat × Nat)} : ∀ k, k < 4 → vsaFoot H (0x8001b538 + k) :=
  fun k hk => .inl (.inr (.inl ⟨by omega, by omega⟩))

/-- **The error return** (`0x80004840`): `errno := ENOMEM`, NULL, for a request
the arena cannot hold. -/
theorem malloc_errno {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins) (h8 : R 8 = reentV)
    (hst : heapEnd < C.top0 + physSize C.n.toNat + extendSlack) :
    AW C.live C.S C.Q 0x80004840#64 R Mt := by
  have hoff := Hp.off_stack_w (by decide) errno_foot
  have hlo := O.sp.lo
  unfold mHead at hlo hoff; unfold Vsa.Sim.tohostAddr at hlo
  have he : ((R 8) + sign_extend (m := 64) (0x000#12)).toNat = 0x8001b538 := by
    rw [h8]; decide
  refine st_80004840 O.live ?_
  refine st_80004844 O.live ?_ ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [he]; unfold StOK Vsa.Sim.tohostAddr; omega
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [he]; exact O.foot errno_foot
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [he]
  refine st_80004848 O.live ?_
  have Hp' := Hp.store_errno (v := upd R 15 ((0#64) + sign_extend (m := 64) (0x00c#12)) 15)
  exact epi_8000484c O (((F.store (a := 0x8001b538) (w := 4) (by omega)).upd (k := 15) (by decide)).upd
    (k := 10) (by decide)) (O.fin_null (by simp only [upd_apply, ite_true]; decide)
    ⟨_, _, _, _, Hp'.heap⟩ Hp'.pres Hp'.frame hst)

theorem malloc_pro {C : MCtx} (O : MOK C) {R : Nat → BitVec 64}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (E : MEntry C R) (Hp : MHeap C C.Mt0 brkv chunks bins)
    (hsm : ∀ R Mt nb, MFrame C R Mt → MHeap C Mt brkv chunks bins → SmallRegs nb R →
      NbOK C.n nb → nb ≤ 503 → R 8 = reentV → AW C.live C.S C.Q 0x800047dc#64 R Mt)
    (hlg : ∀ R Mt nb, MFrame C R Mt → MHeap C Mt brkv chunks bins → NbOK C.n nb → 503 < nb →
      nb < 2 ^ 31 → (R 14).toNat = nb → R 8 = reentV → AW C.live C.S C.Q 0x80004884#64 R Mt) :
    AW C.live C.S C.Q 0x800047a8#64 R C.Mt0 := by
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := E.sp
  have hs2n : (R 2).toNat = C.s.toNat := by rw [hs2]
  sx_run [8] O.live at 0x800047c0
  rw [show (R 2 + 18446744073709551520#64 + 80#64).toNat = C.s.toNat - 96 + 80 by sx_addr,
    show (R 2 + 18446744073709551520#64 + 88#64).toNat = C.s.toNat - 96 + 88 by sx_addr]
  -- the frame and the heap after the two spills
  have Hp1 := (Hp.store_stack (a := C.s.toNat - 96 + 80) (w := 8) (v := R 8) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 96 + 88) (w := 8) (v := R 1) (by unfold mHead; omega)
    (by omega)
  have hS0 : read64 (writeLog (writeLog C.Mt0 [(C.s.toNat - 96 + 80, 8, R 8)])
      [(C.s.toNat - 96 + 88, 8, R 1)]) (C.s.toNat - 96 + 80) = some (C.rv0 8).toNat := by
    rw [read64_store_miss _ _ (by omega), read64_store_hit, E.s0]
  have hRA : read64 (writeLog (writeLog C.Mt0 [(C.s.toNat - 96 + 80, 8, R 8)])
      [(C.s.toNat - 96 + 88, 8, R 1)]) (C.s.toNat - 96 + 88) = some C.r.toNat := by
    rw [read64_store_hit, E.ra]
  have h9 := E.s1; have h18 := E.s2; have h19 := E.s3
  have hn := E.a1
  have hN : (R 11 + 23#64).toNat = (C.n.toNat + 23) % 2 ^ 64 := by
    rw [BitVec.toNat_add, hn]; rfl
  have htop0 : heapStart ≤ C.top0 := Hp.heap.heap.heap.walk.le
  have hs8 : R 10 = reentV := E.a0
  refine st_800047c0 O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  · -- `n + 23 > 46`
    rw [hN, show (46#64).toNat = 46 from rfl] at hc
    sx_run [4] O.live at 0x80004868
    have hX : C.n.toNat + 23 < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hX] at hc
    have hN' : (C.n + 23#64).toNat = C.n.toNat + 23 := by
      rw [← hn, hN, hn, Nat.mod_eq_of_lt hX]
    have hnb : (C.n + 23#64 &&& 18446744073709551600#64).toNat = (C.n.toNat + 23) / 16 * 16 := by
      rw [toNat_and_m16, hN']
    have hP : physSize C.n.toNat = (C.n.toNat + 23) / 16 * 16 := by
      unfold physSize
      rw [show C.n.toNat + 8 + 15 = C.n.toNat + 23 by omega, Nat.mul_comm]
      exact Nat.max_eq_right (by omega)
    refine st_80004868 O.live (fun h1 => ?_) (fun h1 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hn, hnb,
        show (2147483648#64).toNat = 2 ^ 31 from rfl] at h1
    · -- the chunk would not fit in 31 bits
      refine malloc_errno O ⟨?_, hS0, hRA, ?_, ?_, ?_⟩ Hp1 ?_ ?_ <;>
        try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [hs2]
      · exact h9
      · exact h18
      · exact h19
      · exact hs8
      rw [hP]
      have hE : heapEnd < heapStart + 2 ^ 31 := by decide
      exact Nat.lt_of_lt_of_le hE (Nat.le_trans (Nat.add_le_add htop0 h1) (Nat.le_add_right _ _))
    refine st_8000486c O.live (fun h2 => ?_) (fun h2 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hnb, hn] at h2
    · -- `nb < n`: impossible without a wrap
      omega
    -- spill `nb`, take the lock, reload it
    sx_run [8] O.live at 0x80004880
    rw [show (R 2 + 18446744073709551520#64 + 8#64).toNat = C.s.toNat - 96 + 8 by sx_addr]
    have Hp2 := Hp1.store_stack (a := C.s.toNat - 96 + 8) (w := 8)
      (v := R 11 + 23#64 &&& 18446744073709551600#64) (by unfold mHead; omega) (by omega)
    have hS0' := hS0; have hRA' := hRA
    rw [← read64_store_miss (a := C.s.toNat - 96 + 80) (b := C.s.toNat - 96 + 8) (w := 8)
      (v := R 11 + 23#64 &&& 18446744073709551600#64) _ (by omega)] at hS0'
    rw [← read64_store_miss (a := C.s.toNat - 96 + 88) (b := C.s.toNat - 96 + 8) (w := 8)
      (v := R 11 + 23#64 &&& 18446744073709551600#64) _ (by omega)] at hRA'
    have hnb' : (R 11 + 23#64 &&& 18446744073709551600#64).toNat = (C.n.toNat + 23) / 16 * 16 := by
      rw [hn]; exact hnb
    have hNb : NbOK C.n ((C.n.toNat + 23) / 16 * 16) := ⟨hP.symm⟩
    refine st_80004880 O.live (fun h3 => ?_) (fun h3 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hnb',
        show (503#64).toNat = 503 from rfl] at h3
    · -- a small chunk
      sx_run [8] O.live at 0x800047dc
      refine hsm _ _ ((C.n.toNat + 23) / 16 * 16) ⟨?_, hS0', hRA', ?_, ?_, ?_⟩ Hp2 ⟨?_, ?_, ?_⟩ hNb h3 ?_ <;>
        try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [hs2]
      · exact h9
      · exact h18
      · exact h19
      · exact hnb'
      · rw [BitVec.toNat_ushiftRight, hnb', Nat.shiftRight_eq_div_pow]
      · have ha7 : ((R 11 + 23#64 &&& 18446744073709551600#64) >>> 3).toNat =
            (C.n.toNat + 23) / 16 * 16 / 8 := by
          rw [BitVec.toNat_ushiftRight, hnb', Nat.shiftRight_eq_div_pow]
        have hy : ((R 11 + 23#64 &&& 18446744073709551600#64) >>> 3 <<< 1 + 2#64).toNat =
            2 * ((C.n.toNat + 23) / 16 * 16 / 8) + 2 := by
          rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, ha7, Nat.shiftLeft_eq]
          simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
          omega
        rw [BitVec.toNat_shiftLeft, toNat_sx32_small _ (by rw [hy]; omega), hy, Nat.shiftLeft_eq]
        simp only [Nat.reducePow]
        omega
      · exact hs8
    · -- a large chunk
      refine hlg _ _ ((C.n.toNat + 23) / 16 * 16) ⟨?_, hS0', hRA', ?_, ?_, ?_⟩ Hp2 hNb (by omega)
        (by omega) ?_ ?_ <;>
        try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [hs2]
      · exact h9
      · exact h18
      · exact h19
      · exact hnb'
      · exact hs8
  · -- `n + 23 ≤ 46`
    rw [hN, show (46#64).toNat = 46 from rfl] at hc
    have e32 : (0#64 + sign_extend (m := 64) (0x020#12)).toNat = 32 := by decide
    refine st_800047c4 O.live ?_
    refine st_800047c8 O.live (fun hc2 => ?_) (fun hc2 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hn] at hc2
    · -- `n > 32`: `n + 23` wrapped
      refine malloc_errno O ⟨?_, hS0, hRA, ?_, ?_, ?_⟩ Hp1 ?_ ?_ <;>
        try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [hs2]
      · exact E.s1
      · exact E.s2
      · exact E.s3
      · exact hs8
      · rw [e32] at hc2
        unfold physSize heapEnd extendSlack
        unfold heapStart at htop0
        omega
    · -- `n ≤ 23`: the 32-byte chunk
      sx_run [8] O.live at 0x800047dc
      refine hsm _ _ 32 ⟨?_, hS0, hRA, ?_, ?_, ?_⟩ Hp1 ⟨?_, ?_, ?_⟩ ⟨?_⟩ (by decide) ?_ <;>
        try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · rw [hs2]
      · exact E.s1
      · exact E.s2
      · exact E.s3
      · rfl
      · rfl
      · rfl
      · have e32' : (0#64 + sign_extend (m := 64) (0x020#12)).toNat = 32 := by decide
        try simp only [e32'] at hc2
        unfold physSize
        omega
      · exact hs8

end VsaIris.VsaHeap
