import VsaIris.Vsa.FreeCtx
import VsaIris.Vsa.HeapPermit
import VsaIris.Vsa.Carry

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

structure FHeap (C : MCtx) (Mt : Mem) (q n brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) : Prop where
  heap : PHeapAt Mt ((q, n) :: C.H) C.top0 brkv chunks bins
  starts : Starts ((q, n) :: C.H)
  pres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome
  disj : ∀ a, C.s.toNat - mHead ≤ a → a < C.s.toNat → ¬ vsaFoot C.H a
  frame : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?

theorem FHeap.store_stack {C : MCtx} {Mt : Mem} {q n brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (Hp : FHeap C Mt q n brkv chunks bins) {a w : Nat} {v : BitVec 64}
    (h1 : C.s.toNat - mHead ≤ a) (h2 : a + w ≤ C.s.toNat) :
    FHeap C (writeLog Mt [(a, w, v)]) q n brkv chunks bins where
  heap := Hp.heap.transport_read fun x hx => by
    have hd := Hp.disj x
    have ho : OutL [(a, w, v)] x := ⟨Classical.byContradiction fun hc => by
      simp only at hc
      exact hd (by omega) (by omega) (vsaFoot_of_cons hx.1), trivial⟩
    rw [writeLog_out _ _ _ ho]
  starts := Hp.starts
  pres := pres_store Hp.pres
  disj := Hp.disj
  frame := frame_store (win_stack h1 h2) Hp.frame

structure FChunk (Mt : Mem) (q : Nat) (chunks : List Chunk) (x sz hdr0 nh : Nat) : Prop where
  mem : (⟨x, sz, true⟩ : Chunk) ∈ chunks
  addr : x + 16 = q
  hdr : read64 Mt (x + 8) = some hdr0
  hsz : chunkSize hdr0 = sz
  hlow : hdr0 % 4 < 2
  next : read64 Mt (x + sz + 8) = some nh

structure FDec (C : MCtx) (R : Nat → BitVec 64) (Mt : Mem) (q n brkv : Nat) (chunks : List Chunk)
    (bins : Nat → List Nat) (x sz hdr0 nh : Nat) : Prop where
  frame : FFrame C R Mt
  heap : FHeap C Mt q n brkv chunks bins
  chunk : FChunk Mt q chunks x sz hdr0 nh
  s0 : R 8 = reentV
  a7 : R 17 = 0x8001ad10#64
  a1 : (R 11).toNat = q
  a6 : (R 16).toNat = C.top0
  a4 : (R 14).toNat = x
  a5 : (R 15).toNat = sz
  a2 : (R 12).toNat = x + sz
  a0 : (R 10).toNat = hdr0
  t1 : (R 6).toNat = hdr0 % 2
  a3 : (R 13).toNat = chunkSize nh

theorem free_pro {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {q n brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat}
    (E : FEntry C q R) (Hp : FHeap C C.Mt0 q n brkv chunks bins)
    (hk : ∀ R' Mt x sz hdr0 nh, FDec C R' Mt q n brkv chunks bins x sz hdr0 nh →
      AW C.live C.S C.Q 0x80007398#64 R' Mt) :
    AW C.live C.S C.Q 0x80007350#64 R C.Mt0 := by
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := E.sp
  have hs2n : (R 2).toNat = C.s.toNat := by rw [hs2]
  have HH := Hp.heap.heap.heap
  obtain ⟨c, hc, hcu, hca, hcn⟩ := HH.exact (q, n) List.mem_cons_self List.mem_cons_self
  have hcb := HH.walk.chunk_bounds c hc
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapStart at hcb; unfold heapEnd at hbrk
  simp only at hca hcn
  have hq := E.a1
  refine (step% st 0x80007350) O.live (fun h => absurd (congrArg BitVec.toNat h) (by rw [hq]; simp; omega))
    (fun _ => ?_)
  have rS := O.stackRgn; have rG := globRgn C.H
  rgn_run O.live at 0x8000736c
  rw [show (R 2 + 18446744073709551584#64 + 16#64).toNat = C.s.toNat - 32 + 16 by rgn_arith,
    show (R 2 + 18446744073709551584#64 + 8#64).toNat = C.s.toNat - 32 + 8 by rgn_arith,
    show (R 2 + 18446744073709551584#64 + 24#64).toNat = C.s.toNat - 32 + 24 by rgn_arith]
  have Hp1 := ((Hp.store_stack (a := C.s.toNat - 32 + 16) (w := 8) (v := R 8) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 32 + 8) (w := 8) (v := R 11) (by unfold mHead; omega)
    (by omega)).store_stack (a := C.s.toNat - 32 + 24) (w := 8) (v := R 1) (by unfold mHead; omega)
    (by omega)
  generalize hM1 : writeLog (writeLog (writeLog C.Mt0 [(C.s.toNat - 32 + 16, 8, R 8)])
    [(C.s.toNat - 32 + 8, 8, R 11)]) [(C.s.toNat - 32 + 24, 8, R 1)] = Mt1 at Hp1 ⊢
  have hA1 : read64 Mt1 (C.s.toNat - 32 + 8) = some (R 11).toNat := by rw [← hM1]; rd_log
  have K := (Hp1.heap.heap.chunkK hc).lower
  open_fields K
  obtain ⟨hdr0, hdr0r, hdr0s, hdr0l⟩ := K_hdrv
  obtain ⟨nh, nhr, nhp⟩ := K_nhdrv
  have htp := Hp1.heap.heap.heap.top_ptr; unfold topAddr avAddr at htp
  have hsz : (BitVec.ofNat 64 hdr0 &&& 18446744073709551614#64).toNat = c.size := by
    rw [toNat_and_m2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hdr0r)]
    unfold chunkSize at hdr0s; omega
  rgn_run O.live at 0x80007378
  rgn_ld [hA1]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.reduceAppend, BitVec.reduceSignExtend,
    BitVec.reduceAdd]
  rgn_run O.live at 0x80007380
  rgn_ld [htp, hdr0r]
  rgn_run O.live at 0x80007390
  rgn_ld [nhr]
  rgn_run O.live at 0x80007398
  have hx : (R 11 + 18446744073709551600#64).toNat = c.addr := by rgn_arith
  have hnx : (R 11 + 18446744073709551600#64 + (BitVec.ofNat 64 hdr0 &&& 18446744073709551614#64)).toNat
      = c.addr + c.size := by rgn_arith
  have hS0 : read64 Mt1 (C.s.toNat - 32 + 16) = some (C.rv0 8).toNat := by rw [← hM1]; rd_log [E.s0]
  have hRA : read64 Mt1 (C.s.toNat - 32 + 24) = some C.r.toNat := by rw [← hM1]; rd_log [E.ra]
  obtain ⟨cx, csz, cu⟩ := c
  simp only at hcu hca hdr0r hdr0s hdr0l nhr hx hsz hnx
  subst hcu
  refine hk _ Mt1 cx csz hdr0 nh ⟨⟨?_, hS0, hRA, ?_, ?_, ?_⟩, Hp1, ⟨hc, hca, hdr0r, hdr0s, hdr0l, nhr⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, hs2, E.s1, E.s2, E.s3, E.a0, hq, hx, hsz, hnx]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hdr0r)]
  · rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ hdr0r),
      show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  · rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Vsa.Sim.read64_lt _ _ _ nhr)]; rfl

end VsaIris.VsaHeap

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem free_epi {C : MCtx} (O : FOK C) {R : Nat → BitVec 64} {Mt : Mem} (F : FFrame C R Mt)
    (hheap : ∃ top brkv chunks bins, PHeapAt Mt C.H top brkv chunks bins ∧ top ≤ C.top0)
    (hpres : ∀ a, vsaFoot C.H a → (Mt[a]?).isSome)
    (hframe : ∀ a, ¬ MWin C.H C.s a → Mt[a]? = C.Mt0[a]?) :
    AW C.live C.S C.Q 0x80007434#64 R Mt := by
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2n : (R 2).toNat = C.s.toNat - 32 := by rw [F.sp]; sx_addr
  have rS := O.stackRgn
  rgn_run O.live at 0
  all_goals rgn_ld [F.s0, F.ra]
  all_goals simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact O.ral
  refine O.ok _ Mt ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hheap, hpres, hframe⟩ <;> carry_close [F.sp, F.s1, F.s2, F.s3]

end VsaIris.VsaHeap
