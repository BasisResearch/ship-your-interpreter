import VsaIris.Vsa.MallocPaths
import VsaIris.Vsa.HeapPermit
import VsaIris.Vsa.RegKeep

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

abbrev reentV : BitVec 64 := 0x8001b538#64

structure MEntry (C : MCtx) (R : Nat → BitVec 64) : Prop where
  ra : R 1 = C.r
  sp : R 2 = C.s
  a0 : R 10 = reentV
  a1 : R 11 = C.n
  s0 : R 8 = C.rv0 8
  s1 : R 9 = C.rv0 9
  s2 : R 18 = C.rv0 18
  s3 : R 19 = C.rv0 19


theorem malloc_errno {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins) (h8 : R 8 = reentV)
    (hst : Starved C.top0 C.n.toNat) :
    AW C.live C.S C.Q 0x80004840#64 R Mt := by
  have Er := errnoRgn C.H
  have hoff := Er.offStack Hp.disj (by decide); have hlo := O.sp.lo
  unfold mHead at hlo hoff; unfold Vsa.Sim.tohostAddr at hlo
  have h8n : (R 8).toNat = 0x8001b538 := by rw [h8]; rfl
  rgn_run O.live at 0x8000484c
  rw [h8n]
  have Hp' := Hp.store_errno (v := 12#64)
  exact epi_8000484c O ((F.store (a := 0x8001b538) (w := 4) (by omega)).of_regs rfl rfl rfl rfl)
    (O.fin_null rfl ⟨_, _, _, _, Hp'.heap⟩ Hp'.pres Hp'.frame hst)

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

  have Hp1 := (Hp.store_stack (a := C.s.toNat - 96 + 80) (w := 8) (v := R 8) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 96 + 88) (w := 8) (v := R 1) (by unfold mHead; omega)
    (by omega)
  have F0 : MFrame C (upd R 2 (R 2 + 18446744073709551520#64)) (writeLog (writeLog C.Mt0
      [(C.s.toNat - 96 + 80, 8, R 8)]) [(C.s.toNat - 96 + 88, 8, R 1)]) :=
    ⟨by rw [upd_same, hs2], by rd_log [E.s0], by rd_log [E.ra], E.s1, E.s2, E.s3⟩
  have hn := E.a1
  have hN : (R 11 + 23#64).toNat = (C.n.toNat + 23) % 2 ^ 64 := by
    rw [BitVec.toNat_add, hn]; rfl
  have htop0 : heapStart ≤ C.top0 := Hp.heap.heap.heap.walk.le
  have hs8 : R 10 = reentV := E.a0
  refine (step% st 0x800047c0) O.live (fun hc => ?_) (fun hc => ?_) <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hc
  ·
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
    refine (step% st 0x80004868) O.live (fun h1 => ?_) (fun h1 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hn, hnb,
        show (2147483648#64).toNat = 2 ^ 31 from rfl] at h1
    ·
      refine malloc_errno O (F0.of_regs ?_ ?_ ?_ ?_) Hp1 ?_ ?_ <;> try reg_close [hs8]
      refine Starved.of_lt ?_
      rw [hP]
      have hE : heapEnd < heapStart + 2 ^ 31 := by decide
      exact Nat.lt_of_lt_of_le hE (Nat.add_le_add htop0 h1)
    refine (step% st 0x8000486c) O.live (fun h2 => ?_) (fun h2 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hnb, hn] at h2
    ·
      omega

    sx_run [8] O.live at 0x80004880
    rw [show (R 2 + 18446744073709551520#64 + 8#64).toNat = C.s.toNat - 96 + 8 by sx_addr]
    have Hp2 := Hp1.store_stack (a := C.s.toNat - 96 + 8) (w := 8)
      (v := R 11 + 23#64 &&& 18446744073709551600#64) (by unfold mHead; omega) (by omega)
    have hnb' : (R 11 + 23#64 &&& 18446744073709551600#64).toNat = (C.n.toNat + 23) / 16 * 16 := by
      rw [hn]; exact hnb
    have hNb : NbOK C.n ((C.n.toNat + 23) / 16 * 16) := ⟨hP.symm⟩
    refine (step% st 0x80004880) O.live (fun h3 => ?_) (fun h3 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hnb',
        show (503#64).toNat = 503 from rfl] at h3
    ·
      sx_run [8] O.live at 0x800047dc
      refine hsm _ _ ((C.n.toNat + 23) / 16 * 16) ((F0.store (by omega)).of_regs ?_ ?_ ?_ ?_) Hp2
        ⟨?_, ?_, ?_⟩ hNb h3 ?_ <;> reg_try [hnb', hs8]
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
    ·
      refine hlg _ _ ((C.n.toNat + 23) / 16 * 16) ((F0.store (by omega)).of_regs ?_ ?_ ?_ ?_) Hp2
        hNb (by omega) (by omega) ?_ ?_ <;> reg_close [hnb', hs8]
  ·
    rw [hN, show (46#64).toNat = 46 from rfl] at hc
    have e32 : (0#64 + sign_extend (m := 64) (0x020#12)).toNat = 32 := by decide
    refine (step% st 0x800047c4) O.live ?_
    refine (step% st 0x800047c8) O.live (fun hc2 => ?_) (fun hc2 => ?_) <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hn] at hc2
    ·
      refine malloc_errno O (F0.of_regs ?_ ?_ ?_ ?_) Hp1 ?_ ?_ <;> try reg_close [hs8]
      · rw [e32] at hc2
        unfold Starved physSize heapEnd extendSlack
        unfold heapStart at htop0
        omega
    ·
      sx_run [8] O.live at 0x800047dc
      refine hsm _ _ 32 (F0.of_regs ?_ ?_ ?_ ?_) Hp1 ⟨?_, ?_, ?_⟩ ⟨?_⟩ (by decide) ?_ <;>
        try reg_close [hs8]
      · have e32' : (0#64 + sign_extend (m := 64) (0x020#12)).toNat = 32 := by decide
        try simp only [e32'] at hc2
        unfold physSize
        omega

end VsaIris.VsaHeap
