import VsaIris.Vsa.MallocExtend
import VsaIris.Vsa.HeapCarve
import VsaIris.Vsa.HeapPermit

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem lr_split_ret {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb v sz : Nat} (hsp : MSp C.s) (Hp : MHeap C Mt brkv chunks bins)
    (hnb : NbOK C.n nb)
    (hbin : bins 1 = [v]) (hfree : FreeAt chunks v sz) (hle : nb + 32 ≤ sz)
    {w1 w2 w4 w6 w7 w8 : BitVec 64} (h1 : w1.toNat = nb + 1) (h2 : w2.toNat = v + nb)
    (h4 : w4.toNat = binAt 1) (h6 : w6.toNat = sz - nb + 1) (h7 : w7.toNat = sz - nb) :
    TakeRet C (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
      [(v + 8, 8, w1)]) [(binAt 1 + 24, 8, w2)]) [(binAt 1 + 16, 8, w2)])
      [(v + nb + 24, 8, w4)]) [(v + nb + 16, 8, w4)]) [(v + nb + 8, 8, w6)])
      [(v + sz, 8, w7)]) [(C.s.toNat - 96 + 8, 8, w8)]) v := by
  have K := Hp.heap.heap.chunkK hfree; have F := Hp.heap.heap.freeSpan hfree rfl
  have Bn := binRgn C.H (j := 1) (by decide)
  open_fields K; simp only at F
  have hfo := F.offStack Hp.disj (by omega); have hbo := Bn.offStack Hp.disj (by decide)
  have hnb16 := hnb.al; have hnb32 := hnb.lo; have hn8 := hnb.fits; have hslo := hsp.lo
  have hb1 : binAt 1 = 2147593504 := rfl
  simp only [mHead, Vsa.Sim.tohostAddr] at hfo hbo hslo
  obtain ⟨cs₁, cs₂, hsp⟩ := List.append_of_mem hfree
  obtain ⟨hfr, hal16⟩ := PHeapAt.take_fresh Hp.heap hfree rfl (n := C.n.toNat) (by simp only; omega)
  refine ⟨hfr, hal16, ⟨_, _, _, _, (hsp ▸ Hp.heap).split_permit (i := 1) (by decide)
    (by unfold numBins; decide) (pre := []) (post := []) (by rw [hbin]; rfl) hnb16 hnb32 hle
    (n := C.n.toNat) hn8 (by rw [updBins_same]; rfl) rfl rfl (fun h => absurd rfl h)
    (fun h => absurd rfl h)
    (Realises.of_log (by wl_win <;> first
        | exact .inl (.inr (by unfold CarveW; omega))
        | exact .inr fun hf => by have := offStack_pt Hp.disj hf; omega)
      (by rd_log [h1, h2, h4, h6, h7]) (by rd_log)), by omega, Hp.live.split hsp _ _⟩, ?_, ?_⟩
  all_goals simp only [writeLog_nest, List.cons_append, List.nil_append]
  · exact pres_log _ Hp.pres
  · exact frame_log (by log_in) Hp.frame

theorem lr_split {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem}
    {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat} {nb idx v sz : Nat}
    (F : MFrame C R Mt) (Hp : MHeap C Mt brkv chunks bins) (G : LRRegs nb idx R)
    (V : LRVictim nb sz v R) (hnb : NbOK C.n nb) (hbin : bins 1 = [v]) (hfree : FreeAt chunks v sz)
    (hle : nb + 32 ≤ sz) :
    AW C.live C.S C.Q 0x80004da0#64 R Mt := by
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have ha4 := V.a4; have ha5 := V.a5; have ht1 := V.t1; have ha3 := V.a3; have ht4 := V.t4
  have ha6 := G.a6
  have hs2 := F.sp
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hsal := O.sp.align
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [hs2]; sx_addr
  have hbnd := HH.walk.chunk_bounds _ hfree
  have htle := HH.top_le; have hbrk := HH.brk_le
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hv16 := hal0 _ hfree
  have hsz16 := (walk_sizes HH.walk _ hfree).1
  simp only at hbnd hv16 hsz16
  unfold heapStart at hbnd; unfold heapEnd at hbrk
  have hnb16 := hnb.al; have hnb32 := hnb.lo
  have hb1 : binAt 1 = 2147593504 := by unfold binAt avAddr; rfl
  have hFV := foot_free_span B hfree rfl
  simp only at hFV
  have hrem : (R 13).toNat = sz - nb := by rw [ha3, BitVec.toNat_sub, ht1, ha4]; omega

  refine st_80004da0 O.live ?_
  refine st_80004da4 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm

  refine st_80004da8 O.live ?_
  refine st_80004dac O.live ?_ ?_ ?_
  · sx_norm; rw [ha6]; decide
  · sx_norm; rw [ha6]; exact O.bin_link (j := 1) (by unfold numBins; decide) (.inr (by rw [hb1]; decide))
  sx_norm
  refine st_80004db0 O.live ?_ ?_ ?_
  · sx_norm; rw [ha6]; decide
  · sx_norm; rw [ha6]; exact O.bin_link (j := 1) (by unfold numBins; decide) (.inl (by rw [hb1]; decide))
  sx_norm

  refine st_80004db4 O.live ?_
  refine st_80004db8 O.live ?_
  refine st_80004dbc O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm
  refine st_80004dc0 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm
  refine st_80004dc4 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm

  refine st_80004dc8 O.live ?_
  refine st_80004dcc O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm
  have e1 : (R 15 + 8#64).toNat = v + 8 := by sx_addr
  have e2 : (R 16 + 40#64).toNat = binAt 1 + 24 := by rw [ha6, hb1]; rfl
  have e3 : (R 16 + 32#64).toNat = binAt 1 + 16 := by rw [ha6, hb1]; rfl
  have e4 : (R 15 + R 14 + 24#64).toNat = v + nb + 24 := by sx_addr
  have e5 : (R 15 + R 14 + 16#64).toNat = v + nb + 16 := by sx_addr
  have e6 : (R 15 + R 14 + 8#64).toNat = v + nb + 8 := by sx_addr
  have e7 : (R 15 + R 6).toNat = v + sz := by sx_addr
  rw [e1, e2, e3, e4, e5, e6, e7]
  sx_run [8] O.live at 0x8000484c
  rw [show (R 2 + 8#64).toNat = C.s.toNat - 96 + 8 by sx_addr]
  have hoff := Hp.off_stack_w (a := v + 8) (w := sz + 8) (by omega)
    (fun k hk => hFV _ (by omega) (by omega))
  unfold mHead at hoff
  refine epi_8000484c O ?F (O.fin_take (v := v) ?_ (lr_split_ret O.sp Hp hnb hbin hfree hle
    (or1_toNat ha4 (by omega)) (by sx_addr) ht4 (or1_toNat hrem (by omega)) hrem))
  case F =>
    refine MFrame.of_regs ((((((((F.store (by omega)).store (by unfold binAt avAddr; omega)).store
      (by unfold binAt avAddr; omega)).store (by omega)).store (by omega)).store (by omega)).store
      (by omega)).store (by omega)) ?_ ?_ ?_ ?_ <;>
      simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  sx_addr

end VsaIris.VsaHeap
