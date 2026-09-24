import VsaIris.Vsa.ReallocCtx

/-!
# `_realloc_r`'s prologue

From the entry to the first join (`0x800052e0`): the frame, the lock, and
the request's chunk size, or the error return (`errno := ENOMEM`, NULL) for a
request no chunk can hold.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- `sltu` then `xori 1`: zero exactly when the comparison held. -/
theorem sltu_xori_eq (x y : BitVec 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y)) ^^^ 1#64) = 0#64 ↔ x.toNat < y.toNat := by
  by_cases hl : x.toNat < y.toNat
  · rw [(ult_iff x y).2 hl]; exact ⟨fun _ => hl, fun _ => by decide⟩
  · rw [(ult_false_iff x y).2 (by omega)]; exact ⟨fun h => absurd h (by decide), fun h => absurd h hl⟩

/-- **The error return** (`0x800054b8`): `errno := ENOMEM`, NULL, the old
block kept, for a request the arena cannot hold. -/
theorem realloc_errno {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (F : RFrame C R Mt) (Hp : RHeap C B Mt brkv chunks bins) (h9 : R 9 = reentV)
    (hst : Starved C.top0 C.n.toNat) :
    AW C.live C.S C.Q 0x800054b8#64 R Mt := by
  have hlo := O.sp.lo
  unfold mHead Vsa.Sim.tohostAddr at hlo
  obtain ⟨hoff, _⟩ := glob_off_of Hp.disj
  unfold mHead at hoff
  have he : ((R 9) + sign_extend (m := 64) (0x000#12)).toNat = 0x8001b538 := by
    rw [h9]; decide
  refine st_800054b8 O.live ?_
  refine st_800054bc O.live ?_ ?_ ?_
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [he]; unfold StOK Vsa.Sim.tohostAddr; omega
  · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; rw [he]; exact O.foot errno_foot
  simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  rw [he]
  refine st_800054c0 O.live ?_
  have Hp' := Hp.store_errno (v := upd R 15 ((0#64) + sign_extend (m := 64) (0x00c#12)) 15)
  refine repi0 O (((F.store (a := 0x8001b538) (w := 4) (by omega)).of_regs ?_ ?_ ?_))
    fun R' hR h10 => O.null _ _ ⟨hR, ?_, ⟨_, _, _, _, Hp'.heap⟩, Hp'.pres, Hp'.data, hst⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *
  rw [h10]; decide

theorem realloc_pro {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (E : REntry C B R) (Hp : RHeap C B C.Mt0 brkv chunks bins)
    (hk : ∀ R' Mt nb, RFrame C R' Mt → RHeap C B Mt brkv chunks bins → NbOK C.n nb → nb < 2 ^ 31 →
      (R' 8).toNat = B.p → R' 9 = reentV → R' 11 = C.n → (R' 15).toNat = nb →
      AW C.live C.S C.Q 0x800052e0#64 R' Mt) :
    AW C.live C.S C.Q 0x80005290#64 R C.Mt0 := by
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := E.sp
  have hs2n : (R 2).toNat = C.s.toNat := by rw [hs2]
  have HH := Hp.heap.heap.heap
  obtain ⟨c, hc, _, hca, hcn⟩ := HH.live _ List.mem_cons_self
  have hcb := HH.walk.chunk_bounds c hc
  unfold heapStart at hcb
  simp only at hca hcn
  have hp := E.a1
  refine st_80005290 O.live (fun h => absurd (congrArg BitVec.toNat h) (by rw [hp]; simp; omega))
    (fun _ => ?_)
  sx_run [40] O.live at 0x800052b4
  rw [show (R 2 + 18446744073709551552#64 + 48#64).toNat = C.s.toNat - 64 + 48 by sx_addr,
    show (R 2 + 18446744073709551552#64 + 40#64).toNat = C.s.toNat - 64 + 40 by sx_addr,
    show (R 2 + 18446744073709551552#64 + 56#64).toNat = C.s.toNat - 64 + 56 by sx_addr,
    show (R 2 + 18446744073709551552#64).toNat = C.s.toNat - 64 by sx_addr]
  have Hp1 := (((Hp.store_stack (a := C.s.toNat - 64 + 48) (w := 8) (v := R 8) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 64 + 40) (w := 8) (v := R 9) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 64 + 56) (w := 8) (v := R 1) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 64) (w := 8) (v := R 12) (by unfold mHead; omega)
    (by omega)
  generalize hM1 : writeLog (writeLog (writeLog (writeLog C.Mt0 [(C.s.toNat - 64 + 48, 8, R 8)])
    [(C.s.toNat - 64 + 40, 8, R 9)]) [(C.s.toNat - 64 + 56, 8, R 1)]) [(C.s.toNat - 64, 8, R 12)] = M1
    at Hp1 ⊢
  have F1 : RFrame C (upd (upd (upd (upd (upd R 2 (R 2 + 18446744073709551552#64)) 8 (R 11)) 9 (R 10)) 1
      2147504820#64) 10 2147596760#64) M1 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; rw [hs2]
    · rw [← hM1, read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
        read64_store_miss _ _ (by omega), read64_store_hit, E.s0]
    · rw [← hM1, read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
        read64_store_hit, E.s1]
    · rw [← hM1, read64_store_miss _ _ (by omega), read64_store_hit, E.ra]
    · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact E.s2
    · simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact E.s3
  have hsp0 : read64 M1 (C.s.toNat - 64) = some C.n.toNat := by
    rw [← hM1, read64_store_hit, E.a2]
  refine st_800052b4 O.live (by sx_norm; rw [hs2]; sx_addr) (by sx_norm; rw [hs2]; sx_side) ?_
  sx_norm
  rw [show (R 2 + 18446744073709551552#64).toNat = C.s.toNat - 64 by sx_addr, ldv_ld hsp0]
  try simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have htop0 : heapStart ≤ C.top0 := Hp.heap.heap.heap.walk.le
  have hN : (C.n + 23#64).toNat = (C.n.toNat + 23) % 2 ^ 64 := by rw [BitVec.toNat_add]; rfl
  have F2 := fun (R' : Nat → BitVec 64) (h2 : R' 2 = R 2 + 18446744073709551552#64)
      (h18 : R' 18 = R 18) (h19 : R' 19 = R 19) =>
    F1.of_regs (R' := R') (by simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]; exact h2)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h18)
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h19)
  sx_run [2] O.live at 0x800052c0
  refine st_800052c0 O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  · -- `n + 23 ≤ 46` (or wraps): the minimum chunk
    rw [hN, show (46#64).toNat = 46 from rfl] at hc
    sx_run [3] O.live at 0x800052d8
    refine st_800052d8 O.live (fun h1 => ?_) (fun h1 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at h1
    · -- a wrapped request
      rw [show (32#64).toNat = 32 from rfl] at h1
      have hlt := C.n.isLt
      refine realloc_errno O (F2 _ ?_ ?_ ?_) Hp1 ?_ (Starved.of_lt ?_) <;>
        try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · exact E.a0
      · unfold physSize heapEnd; omega
    refine st_800052dc O.live (fun h2 => ?_) (fun _ => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at *
    · exact absurd h2 (by decide)
    rw [show (32#64).toNat = 32 from rfl] at h1
    refine hk _ _ 32 (F2 _ ?_ ?_ ?_) Hp1 ⟨?_⟩ (by decide) ?_ ?_ ?_ ?_ <;>
      try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · unfold physSize; omega
    · exact hp
    · exact E.a0
    · rfl
  · rw [hN, show (46#64).toNat = 46 from rfl] at hc
    have hX : C.n.toNat + 23 < 2 ^ 64 := by
      rcases Nat.lt_or_ge (C.n.toNat + 23) (2 ^ 64) with h | h
      · exact h
      · exfalso; have := C.n.isLt; rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at hc; omega
    rw [Nat.mod_eq_of_lt hX] at hc
    sx_run [3] O.live at 0x800052d0
    refine st_800052d0 O.live ?_
    sx_run [1] O.live at 0x800052d8
    have hnb : (C.n + 23#64 &&& 18446744073709551600#64).toNat = (C.n.toNat + 23) / 16 * 16 := by
      rw [toNat_and_m16, BitVec.toNat_add, show (23#64).toNat = 23 from rfl, Nat.mod_eq_of_lt hX]
    have hP : physSize C.n.toNat = (C.n.toNat + 23) / 16 * 16 := by
      unfold physSize; omega
    refine st_800052d8 O.live (fun h1 => ?_) (fun h1 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hnb] at h1
    · omega
    refine st_800052dc O.live (fun h2 => ?_) (fun h2 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, ne_eq, sltu_xori_eq, hnb,
        Decidable.not_not] at h2 <;> rw [show (2147483648#64 : BitVec 64).toNat = 2 ^ 31 from rfl] at h2
    · -- the chunk would not fit in 31 bits
      refine realloc_errno O (F2 _ ?_ ?_ ?_) Hp1 ?_ (Starved.of_lt ?_) <;>
        try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · exact E.a0
      · rw [hP]; unfold heapEnd heapStart at *; omega
    refine hk _ _ ((C.n.toNat + 23) / 16 * 16) (F2 _ ?_ ?_ ?_) Hp1 ⟨hP.symm⟩ h2 ?_ ?_ ?_ ?_ <;>
      try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
    · exact hp
    · exact E.a0
    · exact hnb

end VsaIris.VsaHeap
