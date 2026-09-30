import VsaIris.Vsa.ReallocCtx
import VsaIris.Vsa.HeapPermit

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem sltu_xori_eq (x y : BitVec 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u x y)) ^^^ 1#64) = 0#64 ↔ x.toNat < y.toNat := by
  by_cases hl : x.toNat < y.toNat
  · rw [(ult_iff x y).2 hl]; exact ⟨fun _ => hl, fun _ => by decide⟩
  · rw [(ult_false_iff x y).2 (by omega)]; exact ⟨fun h => absurd h (by decide), fun h => absurd h hl⟩

theorem realloc_errno {C : MCtx} {B : RB} (O : ROK C B) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (F : RFrame C R Mt) (Hp : RHeap C B Mt brkv chunks bins) (h9 : R 9 = reentV)
    (hst : Starved C.top0 C.n.toNat) :
    AW C.live C.S C.Q 0x800054b8#64 R Mt := by
  have E : Rgn (vsaFoot C.H) 0x8001b538 4 := ⟨errno_foot⟩
  have h9n : (R 9).toNat = 0x8001b538 := by rw [h9]; rfl
  have hoff := E.offStack Hp.disj (by omega); unfold mHead at hoff
  rgn_run O.live at 0x800054c4
  rw [h9n]
  have Hp' := Hp.store_errno (v := 12#64)
  refine repi0 O ((F.store (a := 0x8001b538) (w := 4) (by omega)).of_regs ?_ ?_ ?_)
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
  refine (step% st 0x80005290) O.live (fun h => absurd (congrArg BitVec.toNat h) (by rw [hp]; simp; omega))
    (fun _ => ?_)
  have Sk := O.toWOK.stackRgn
  rgn_run O.live at 0x800052c0
  rw [show (R 2 + 18446744073709551552#64 + 48#64).toNat = C.s.toNat - 64 + 48 by rgn_arith,
    show (R 2 + 18446744073709551552#64 + 40#64).toNat = C.s.toNat - 64 + 40 by rgn_arith,
    show (R 2 + 18446744073709551552#64 + 56#64).toNat = C.s.toNat - 64 + 56 by rgn_arith,
    show (R 2 + 18446744073709551552#64).toNat = C.s.toNat - 64 by rgn_arith, E.a2]
  have Hp1 := (((Hp.store_stack (a := C.s.toNat - 64 + 48) (w := 8) (v := R 8) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 64 + 40) (w := 8) (v := R 9) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 64 + 56) (w := 8) (v := R 1) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 64) (w := 8) (v := C.n) (by unfold mHead; omega)
    (by omega)
  generalize hM1 : writeLog (writeLog (writeLog (writeLog C.Mt0 [(C.s.toNat - 64 + 48, 8, R 8)])
    [(C.s.toNat - 64 + 40, 8, R 9)]) [(C.s.toNat - 64 + 56, 8, R 1)]) [(C.s.toNat - 64, 8, C.n)] = M1
    at Hp1 ⊢
  have F2 : ∀ R' : Nat → BitVec 64, R' 2 = R 2 + 18446744073709551552#64 → R' 18 = R 18 →
      R' 19 = R 19 → RFrame C R' M1 := fun R' h2 h18 h19 =>
    ⟨by rw [h2, hs2], by rw [← hM1]; rd_log [E.s0], by rw [← hM1]; rd_log [E.s1],
      by rw [← hM1]; rd_log [E.ra], h18.trans E.s2, h19.trans E.s3⟩
  have htop0 : heapStart ≤ C.top0 := Hp.heap.heap.heap.walk.le
  have hN : (C.n + 23#64).toNat = (C.n.toNat + 23) % 2 ^ 64 := by rw [BitVec.toNat_add]; rfl
  refine (step% st 0x800052c0) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  ·
    rw [hN, show (46#64).toNat = 46 from rfl] at hc
    sx_run [3] O.live at 0x800052d8
    refine (step% st 0x800052d8) O.live (fun h1 => ?_) (fun h1 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at h1
    ·
      rw [show (32#64).toNat = 32 from rfl] at h1
      have hlt := C.n.isLt
      refine realloc_errno O (F2 _ ?_ ?_ ?_) Hp1 ?_ (Starved.of_lt ?_) <;>
        try simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      · exact E.a0
      · unfold physSize heapEnd; omega
    refine (step% st 0x800052dc) O.live (fun h2 => ?_) (fun _ => ?_) <;>
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
    refine (step% st 0x800052d0) O.live ?_
    sx_run [1] O.live at 0x800052d8
    have hnb : (C.n + 23#64 &&& 18446744073709551600#64).toNat = (C.n.toNat + 23) / 16 * 16 := by
      rw [toNat_and_m16, BitVec.toNat_add, show (23#64).toNat = 23 from rfl, Nat.mod_eq_of_lt hX]
    have hP : physSize C.n.toNat = (C.n.toNat + 23) / 16 * 16 := by
      unfold physSize; omega
    refine (step% st 0x800052d8) O.live (fun h1 => ?_) (fun h1 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hnb] at h1
    · omega
    refine (step% st 0x800052dc) O.live (fun h2 => ?_) (fun h2 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, ne_eq, sltu_xori_eq, hnb,
        Decidable.not_not] at h2 <;> rw [show (2147483648#64 : BitVec 64).toNat = 2 ^ 31 from rfl] at h2
    ·
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
