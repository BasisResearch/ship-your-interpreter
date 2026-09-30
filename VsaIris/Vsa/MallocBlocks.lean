import VsaIris.Vsa.MallocChain
import VsaIris.Vsa.HeapClear
import VsaIris.Vsa.HeapPermit

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

structure BinNbrs (C : MCtx) (Mt : Mem) (chunks : List Chunk) (bins : Nat → List Nat)
    (k x sz pred succ : Nat) : Prop where
  pred16 : pred % 16 = 0
  succ16 : succ % 16 = 0
  predLoc : pred = binAt k ∨ (0x8001c170 ≤ pred ∧ pred + 32 ≤ C.top0)
  succLoc : succ = binAt k ∨ (0x8001c170 ≤ succ ∧ succ + 32 ≤ C.top0)
  predFoot : ∀ o, 16 ≤ o → o < 32 → vsaFoot C.H (pred + o)
  succFoot : ∀ o, 16 ≤ o → o < 32 → vsaFoot C.H (succ + o)
  predNx : x + sz ≠ pred + 8
  succNx : x + sz ≠ succ + 16
  predSep : pred + 32 ≤ x ∨ x + sz ≤ pred
  succSep : succ + 32 ≤ x ∨ x + sz ≤ succ

theorem binNbrs {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {k x sz pred succ : Nat} {pre post : List Nat}
    (Hp : MHeap C Mt brkv chunks bins) (hk0 : 0 < k) (hk : k < numBins)
    (hmem : bins k = pre ++ x :: post) (hfree : FreeAt chunks x sz)
    (hpred : (binAt k :: pre).getLast? = some pred) (hsucc : (post ++ [binAt k]).head? = some succ) :
    BinNbrs C Mt chunks bins k x sz pred succ := by
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have hpm : pred = binAt k ∨ pred ∈ bins k := by
    have := List.mem_of_getLast? hpred
    rcases List.mem_cons.mp this with h1 | h1
    · exact .inl h1
    · exact .inr (by rw [hmem]; exact List.mem_append_left _ h1)
  have hsm : succ = binAt k ∨ succ ∈ bins k := by
    have := List.mem_of_head? hsucc
    rcases List.mem_append.mp this with h1 | h1
    · exact .inr (by rw [hmem]; exact List.mem_append_right _ (List.mem_cons_of_mem _ h1))
    · exact .inl (List.mem_singleton.mp h1)
  have hloc : ∀ y, (y = binAt k ∨ y ∈ bins k) →
      y % 16 = 0 ∧ (y = binAt k ∨ (0x8001c170 ≤ y ∧ y + 32 ≤ C.top0)) := by
    intro y hy
    obtain ⟨hy16, hyn⟩ := HH.node hk0 hk hy
    refine ⟨hy16, ?_⟩
    rcases hyn with h | ⟨cy, hcy, rfl, _, _⟩
    · exact .inl h
    · have := HH.walk.chunk_bounds cy hcy; unfold heapStart at this; exact .inr ⟨this.1, by omega⟩
  obtain ⟨_, hpn⟩ := HH.node hk0 hk hpm
  obtain ⟨_, hsn⟩ := HH.node hk0 hk hsm
  have hbn : x + sz = C.top0 ∨ ∃ c ∈ chunks, c.addr = x + sz := HH.end_bnd hfree
  have hxb := HH.walk.chunk_bounds _ hfree
  unfold heapStart at hxb; simp only at hxb
  have sep : ∀ y, (y = binAt k ∨ y ∈ bins k) → y ≠ x → y + 32 ≤ x ∨ x + sz ≤ y := by
    intro y hy hne
    rcases hy with rfl | hy
    · have := binAt_geo k hk; omega
    · obtain ⟨cy, hcy, rfl, _⟩ := HH.member hk0 hk hy
      have := HH.walk.chunk_bounds cy hcy
      rcases HH.walk.chunk_sep cy hcy _ hfree with he | h1 | h1
      · exact absurd (congrArg Chunk.addr he) hne
      · simp only at h1; omega
      · simp only at h1; omega
  have hnd := HH.bins_nodup k
  rw [hmem] at hnd
  have hbne := (binList_iff_ring.1 (HH.bins_list k hk0 hk)).2
  have hpx : pred ≠ x := by
    rcases hpm with rfl | hp
    · intro he; exact hbne x (by rw [hmem]; simp) he.symm
    · intro he; subst he
      have := List.mem_of_getLast? hpred
      rcases List.mem_cons.mp this with h1 | h1
      · exact hbne pred (by rw [hmem]; simp) h1
      · exact (List.nodup_append.mp hnd).2.2 _ h1 _ List.mem_cons_self rfl
  have hsx : succ ≠ x := by
    rcases hsm with rfl | hs
    · intro he; exact hbne x (by rw [hmem]; simp) he.symm
    · intro he; subst he
      have := List.mem_of_head? hsucc
      rcases List.mem_append.mp this with h1 | h1
      · exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 h1
      · exact hbne succ (by rw [hmem]; simp) (List.mem_singleton.mp h1)
  exact ⟨(hloc pred hpm).1, (hloc succ hsm).1, (hloc pred hpm).2, (hloc succ hsm).2,
    B.node_foot hk0 hk hpm, B.node_foot hk0 hk hsm,
    HH.bnd_ne_node hk hpn hbn 8 (by omega) (by omega),
    HH.bnd_ne_node hk hsn hbn 16 (by omega) (by omega), sep pred hpm hpx, sep succ hsm hsx⟩

theorem BinNbrs.rgnsBlocks {C : MCtx} {Mt : Mem} {chunks : List Chunk} {bins : Nat → List Nat}
    {k x sz pred succ : Nat} (N : BinNbrs C Mt chunks bins k x sz pred succ) :
    Rgn (vsaFoot C.H) (pred + 16) 16 ∧ Rgn (vsaFoot C.H) (succ + 16) 16 :=
  ⟨⟨fun o ho => by rw [Nat.add_assoc]; exact N.predFoot _ (by omega) (by omega)⟩,
    ⟨fun o ho => by rw [Nat.add_assoc]; exact N.succFoot _ (by omega) (by omega)⟩⟩

theorem bw_take_ret {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb k x sz pred succ hd : Nat} {pre post : List Nat}
    (hsp : MSp C.s) (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb) (hk0 : 0 < k)
    (hk : k < numBins) (hmem : bins k = pre ++ x :: post) (hfree : FreeAt chunks x sz)
    (hle : nb ≤ sz) (hpred : (binAt k :: pre).getLast? = some pred)
    (hsucc : (post ++ [binAt k]).head? = some succ) (hdr : read64 Mt (x + sz + 8) = some hd)
    {w1 w2 w3 w4 : BitVec 64} (h1 : w1.toNat = hd + 1) (h2 : w2.toNat = pred)
    (h3 : w3.toNat = succ) :
    TakeRet C (writeLog (writeLog (writeLog (writeLog Mt [(x + sz + 8, 8, w1)])
      [(succ + 24, 8, w2)]) [(pred + 16, 8, w3)]) [(C.s.toNat - 96 + 8, 8, w4)]) x := by
  have N := binNbrs Hp hk0 hk hmem hfree hpred hsucc
  have K := Hp.heap.heap.chunkK hfree; obtain ⟨rP, rS⟩ := N.rgnsBlocks
  open_fields K
  have hp16 := N.pred16; have hs16 := N.succ16; have hbp := N.predNx; have hbs := N.succNx
  have hlo := hsp.lo; have oN := K_nhdr.offStack Hp.disj (by decide)
  have oP := rP.offStack Hp.disj (by decide); have oS := rS.offStack Hp.disj (by decide)
  simp only [mHead, Vsa.Sim.tohostAddr] at hlo oN oP oS
  refine take_ret Hp hnb hk0 hk hmem hfree hle hpred hsucc
    (by show read64 _ (pred + 16) = _; rd_log [h3]) (by show read64 _ (succ + 24) = _; rd_log [h2])
    (fun hd' hd'r => ?_) (fun a ha hna => ?_) ?_ ?_
  · rw [hdr] at hd'r; cases hd'r; rd_log [h1]
  · unfold TakeW at hna; have := offStack_pt Hp.disj ha
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  all_goals simp only [writeLog_nest, List.cons_append, List.nil_append]
  · exact pres_log _ Hp.pres
  · exact frame_log (by log_in) Hp.frame

theorem bw_split_ret {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb k x sz pred succ : Nat} {pre post : List Nat}
    (hsp : MSp C.s) (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb) (hk1 : 1 < k)
    (hk : k < numBins) (hb1 : bins 1 = []) (hmem : bins k = pre ++ x :: post)
    (hfree : FreeAt chunks x sz) (hle : nb + 32 ≤ sz) (hpred : (binAt k :: pre).getLast? = some pred)
    (hsucc : (post ++ [binAt k]).head? = some succ)
    {wh wp ws wr wb wrh wf wx : BitVec 64} (hh : wh.toNat = nb + 1) (hp : wp.toNat = pred)
    (hs : ws.toNat = succ) (hr : wr.toNat = x + nb) (hb : wb.toNat = binAt 1)
    (hrh : wrh.toNat = sz - nb + 1) (hf : wf.toNat = sz - nb) :
    TakeRet C (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog
      (writeLog (writeLog Mt [(x + 8, 8, wh)]) [(succ + 24, 8, wp)]) [(pred + 16, 8, ws)])
      [(binAt 1 + 24, 8, wr)]) [(binAt 1 + 16, 8, wr)]) [(x + nb + 24, 8, wb)])
      [(x + nb + 16, 8, wb)]) [(x + nb + 8, 8, wrh)]) [(x + sz, 8, wf)])
      [(C.s.toNat - 96 + 8, 8, wx)]) x := by
  have N := binNbrs Hp (by omega) hk hmem hfree hpred hsucc
  have K := Hp.heap.heap.chunkK hfree; have F := Hp.heap.heap.freeSpan hfree rfl
  obtain ⟨rP, rS⟩ := N.rgnsBlocks; have Bn := binRgn C.H (j := 1) (by decide)
  open_fields K; simp only at F
  have hp16 := N.pred16; have hs16 := N.succ16; have hpsep := N.predSep; have hssep := N.succSep
  have hploc := N.predLoc; have hsloc := N.succLoc
  have hfo := F.offStack Hp.disj (by omega); have hbo := Bn.offStack Hp.disj (by decide)
  have hpo := rP.offStack Hp.disj (by decide); have hso := rS.offStack Hp.disj (by decide)
  have hnb16 := hnb.al; have hnb32 := hnb.lo; have hn8 := hnb.fits; have hslo := hsp.lo
  have hb1v : binAt 1 = 2147593504 := rfl
  have hbkv : binAt k = 2147593488 + 16 * k := rfl
  have hk' : k < 128 := hk
  simp only [mHead, Vsa.Sim.tohostAddr] at hfo hbo hpo hso hslo
  obtain ⟨cs₁, cs₂, hsp'⟩ := List.append_of_mem hfree
  obtain ⟨hfr, hal16⟩ := PHeapAt.take_fresh Hp.heap hfree rfl (n := C.n.toNat) (by simp only; omega)
  refine ⟨hfr, hal16, ⟨_, _, _, _, (hsp' ▸ Hp.heap).split_permit (i := k) (by omega) hk hmem hnb16
    hnb32 hle (n := C.n.toNat) hn8 (by rw [updBins_other _ _ (by omega : (1 : Nat) ≠ k)]; exact hb1)
    hpred hsucc (fun _ => by show read64 _ (pred + 16) = _; rd_log [hs])
    (fun _ => by show read64 _ (succ + 24) = _; rd_log [hp])
    (Realises.of_log (by wl_win <;> first
        | exact .inl (.inr (by unfold CarveW; omega))
        | exact .inl (.inl (by unfold TakeW; omega))
        | exact .inr fun hf => by have := offStack_pt Hp.disj hf; omega)
      (by rd_log [hh, hr, hb, hrh, hf]) (by rd_log)), by omega, Hp.live.split hsp' _ _⟩, ?_, ?_⟩
  all_goals simp only [writeLog_nest, List.cons_append, List.nil_append]
  · exact pres_log _ Hp.pres
  · exact frame_log (by log_in) Hp.frame

structure BW (C : MCtx) (Mt : Mem) (brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat)
    (nb : Nat) (R : Nat → BitVec 64) : Prop where
  frame : MFrame C R Mt
  heap : MHeap C Mt brkv chunks bins
  nbok : NbOK C.n nb
  nb31 : nb < 2 ^ 31
  b1 : bins 1 = []
  a4 : (R 14).toNat = nb
  a6 : R 16 = 0x8001ad10#64
  t4 : (R 29).toNat = binAt 1
  s0 : R 8 = reentV

theorem bw_take {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb k x sz pred : Nat} {pre post : List Nat}
    (W : BW C Mt brkv chunks bins nb R) (hk1 : 1 < k) (hk : k < numBins)
    (hmem : bins k = pre ++ x :: post) (hfree : FreeAt chunks x sz) (hle : nb ≤ sz)
    (hpred : (binAt k :: pre).getLast? = some pred)
    (h15 : (R 15).toNat = x) (h13 : (R 13).toNat = pred) (h12 : (R 12).toNat = sz) :
    AW C.live C.S C.Q 0x800049e8#64 R Mt := by
  have HH := W.heap.heap.heap.heap
  obtain ⟨succ, hsucc⟩ : ∃ q, (post ++ [binAt k]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have N := binNbrs W.heap (by omega) hk hmem hfree hpred hsucc
  have K := W.heap.heap.heap.chunkK hfree; have FS := W.heap.heap.heap.freeSpan hfree rfl
  obtain ⟨rP, rS⟩ := N.rgnsBlocks; have St := O.stackRgn
  open_fields K; simp only at FS
  have hp16 := N.pred16; have hs16 := N.succ16; have hploc := N.predLoc; have hsloc := N.succLoc
  have hbkv : binAt k = 2147593488 + 16 * k := rfl; have hk' : k < 128 := hk
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [W.frame.sp]; sx_addr
  have hring := (binList_iff_ring.1 (HH.bins_list k (by omega) hk)).1
  rw [hmem] at hring
  have hfd := (ring_member hring hpred hsucc).1
  have hsuccl := Vsa.Sim.read64_lt _ _ _ hfd
  obtain ⟨hd, hdr, hdp⟩ := K_nhdrv
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  have hdev : hd % 2 = 0 := by
    unfold prevInuse at hdp; simp only [beq_eq_false_iff_ne, ne_eq] at hdp; omega
  have oN := K_nhdr.offStack W.heap.disj (by decide); have oP := rP.offStack W.heap.disj (by decide)
  have oS := rS.offStack W.heap.disj (by decide); unfold mHead at oN oP oS
  rgn_run O.live at 0x800049f4
  rgn_ld [hdr, hfd]
  rgn_run O.live at 0x8000484c
  rw [show (R 15 + R 12 + 8#64).toNat = x + sz + 8 by rgn_arith,
    show (BitVec.ofNat 64 succ + 24#64).toNat = succ + 24 by rgn_arith,
    show (R 13 + 16#64).toNat = pred + 16 by rgn_arith,
    show (R 2 + 8#64).toNat = C.s.toNat - 96 + 8 by rgn_arith]
  have hOr : (BitVec.ofNat 64 hd ||| 1#64).toNat = hd + 1 :=
    or1_toNat (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]) hdev
  refine epi_8000484c O ?F (O.fin_take (v := x) ?_ (bw_take_ret O.sp W.heap W.nbok (by omega) hk hmem
    hfree hle hpred hsucc hdr hOr h13 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuccl])))
  case F =>
    refine MFrame.of_regs ((((W.frame.store (by omega)).store (by omega)).store (by omega)).store
      (by omega)) ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  sx_addr

theorem bw_split2 {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb k x sz pred succ : Nat} {pre post : List Nat}
    (Hp : MHeap C Mt brkv chunks bins) (hnb : NbOK C.n nb) (hb1 : bins 1 = [])
    (ht4 : (R 29).toNat = binAt 1) (hk1 : 1 < k) (hk : k < numBins)
    (hmem : bins k = pre ++ x :: post) (hfree : FreeAt chunks x sz) (hle : nb + 32 ≤ sz)
    (hpred : (binAt k :: pre).getLast? = some pred) (hsucc : (post ++ [binAt k]).head? = some succ)
    {M1 : Mem} {wh wp ws : BitVec 64}
    (hM1 : M1 = writeLog (writeLog (writeLog (writeLog (writeLog Mt [(x + 8, 8, wh)])
      [(succ + 24, 8, wp)]) [(pred + 16, 8, ws)]) [(binAt 1 + 24, 8, R 14)])
      [(binAt 1 + 16, 8, R 14)])
    (F1 : MFrame C R M1) (hh : wh.toNat = nb + 1) (hp : wp.toNat = pred) (hs : ws.toNat = succ)
    (h15 : (R 15).toNat = x) (h14 : (R 14).toNat = x + nb) (h12 : (R 12).toNat = sz)
    (h11 : (R 11).toNat = sz - nb) :
    AW C.live C.S C.Q 0x80004d34#64 R M1 := by
  subst hM1
  have K := Hp.heap.heap.chunkK hfree; have FS := Hp.heap.heap.freeSpan hfree rfl
  have St := O.stackRgn
  open_fields K; simp only at FS; clear K_next
  have hnb16 := hnb.al; have hnb32 := hnb.lo
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [F1.sp]; sx_addr
  rgn_run O.live at 0x8000484c
  rw [show (R 14 + 24#64).toNat = x + nb + 24 by rgn_arith,
    show (R 14 + 16#64).toNat = x + nb + 16 by rgn_arith,
    show (R 14 + 8#64).toNat = x + nb + 8 by rgn_arith,
    show (R 15 + R 12).toNat = x + sz by rgn_arith,
    show (R 2 + 8#64).toNat = C.s.toNat - 96 + 8 by rgn_arith]
  have hoff := FS.offStack Hp.disj (by omega); unfold mHead at hoff
  refine epi_8000484c O ?F (O.fin_take (v := x) ?_ (bw_split_ret O.sp Hp hnb hk1 hk hb1
    hmem hfree hle hpred hsucc hh hp hs h14 ht4 (or1_toNat h11 (by omega)) h11))
  case F =>
    refine MFrame.of_regs (((((F1.store (by omega)).store (by omega)).store (by omega)).store
      (by omega)).store (by omega)) ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  sx_addr

theorem bw_split {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb k x sz pred : Nat} {pre post : List Nat}
    (W : BW C Mt brkv chunks bins nb R) (hk1 : 1 < k) (hk : k < numBins)
    (hmem : bins k = pre ++ x :: post) (hfree : FreeAt chunks x sz) (hle : nb + 32 ≤ sz)
    (hpred : (binAt k :: pre).getLast? = some pred)
    (h15 : (R 15).toNat = x) (h13 : (R 13).toNat = pred) (h12 : (R 12).toNat = sz)
    (h11 : (R 11).toNat = sz - nb) :
    AW C.live C.S C.Q 0x80004d14#64 R Mt := by
  have HH := W.heap.heap.heap.heap
  obtain ⟨succ, hsucc⟩ : ∃ q, (post ++ [binAt k]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have N := binNbrs W.heap (by omega) hk hmem hfree hpred hsucc
  have K := W.heap.heap.heap.chunkK hfree; have FS := W.heap.heap.heap.freeSpan hfree rfl
  obtain ⟨rP, rS⟩ := N.rgnsBlocks; have Bn := binRgn C.H (j := 1) (by decide)
  open_fields K; simp only at FS
  have hp16 := N.pred16; have hs16 := N.succ16; have hploc := N.predLoc; have hsloc := N.succLoc
  have hbkv : binAt k = 2147593488 + 16 * k := rfl; have hk' : k < 128 := hk
  have hnb16 := W.nbok.al; have hnb32 := W.nbok.lo; have ha4 := W.a4; have ht4 := W.t4
  have ha6 : (R 16).toNat = 2147593488 := by rw [W.a6]; rfl
  have hb1 : binAt 1 = 2147593504 := rfl
  have hlo := O.sp.lo; have hhi := O.sp.hi
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hring := (binList_iff_ring.1 (HH.bins_list k (by omega) hk)).1
  rw [hmem] at hring
  have hfd := (ring_member hring hpred hsucc).1
  have hsuccl := Vsa.Sim.read64_lt _ _ _ hfd
  rgn_run O.live at 0x80004d18
  rgn_ld [hfd]
  rgn_run O.live at 0x80004d34
  rw [show (R 15 + 8#64).toNat = x + 8 by rgn_arith,
    show (BitVec.ofNat 64 succ + 24#64).toNat = succ + 24 by rgn_arith,
    show (R 13 + 16#64).toNat = pred + 16 by rgn_arith,
    show (R 16 + 40#64).toNat = binAt 1 + 24 by rgn_arith,
    show (R 16 + 32#64).toNat = binAt 1 + 16 by rgn_arith]
  have oV := FS.offStack W.heap.disj (by omega); have oP := rP.offStack W.heap.disj (by decide)
  have oS := rS.offStack W.heap.disj (by decide); unfold mHead at oV oP oS
  exact bw_split2 O W.heap W.nbok W.b1 (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact ht4)
    hk1 hk hmem hfree hle hpred hsucc rfl
    ((((((W.frame.store (by omega)).store (by omega)).store (by omega)).store
      (by omega)).store (by omega)).of_regs
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]))
    (or1_toNat ha4 (by omega)) h13 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuccl])
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h15)
    (by simp only [upd_apply, ite_true]; sx_addr)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h12)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h11)

abbrev MKeep (R R0 : Nat → BitVec 64) : Prop :=
  ∀ x, x ≠ 11 → x ≠ 12 → x ≠ 13 → x ≠ 15 → R x = R0 x

theorem BW.keep {C : MCtx} {Mt : Mem} {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    {nb : Nat} {R R0 : Nat → BitVec 64} (W : BW C Mt brkv chunks bins nb R0) (h : MKeep R R0) :
    BW C Mt brkv chunks bins nb R :=
  ⟨W.frame.of_regs (h 2 (by decide) (by decide) (by decide) (by decide))
    (h 9 (by decide) (by decide) (by decide) (by decide))
    (h 18 (by decide) (by decide) (by decide) (by decide))
    (h 19 (by decide) (by decide) (by decide) (by decide)),
   W.heap, W.nbok, W.nb31, W.b1,
   by rw [h 14 (by decide) (by decide) (by decide) (by decide)]; exact W.a4,
   by rw [h 16 (by decide) (by decide) (by decide) (by decide)]; exact W.a6,
   by rw [h 29 (by decide) (by decide) (by decide) (by decide)]; exact W.t4,
   by rw [h 8 (by decide) (by decide) (by decide) (by decide)]; exact W.s0⟩

abbrev AllSmall (chunks : List Chunk) (l : List Nat) (nb : Nat) : Prop :=
  ∀ x ∈ l, ∀ sz, FreeAt chunks x sz → sz < nb

theorem bw_member {C : MCtx} (O : MOK C) {R0 : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb k : Nat}
    (W : BW C Mt brkv chunks bins nb R0) (hk1 : 1 < k) (hk : k < numBins)
    (h6 : (R0 6).toNat = binAt k) (h28 : (R0 28).toNat = 31)
    (hex : ∀ R', AllSmall chunks (bins k) nb → MKeep R' R0 → (R' 13).toNat = binAt k →
      AW C.live C.S C.Q 0x80004cfc#64 R' Mt) :
    ∀ (rpre post : List Nat) (R : Nat → BitVec 64), bins k = rpre.reverse ++ post →
      AllSmall chunks post nb → MKeep R R0 → (R 13).toNat = rpre.head?.getD (binAt k) →
      AW C.live C.S C.Q 0x800049c8#64 R Mt := by
  have HH := W.heap.heap.heap.heap
  have B := W.heap.heap.heap
  have hgk := binAt_geo k hk
  have hring := (binList_iff_ring.1 (HH.bins_list k (by omega) hk)).1
  have hbne := (binList_iff_ring.1 (HH.bins_list k (by omega) hk)).2
  have hbl : binAt k < 2 ^ 64 := by omega
  intro rpre
  induction rpre with
  | nil =>
    intro post R hmem hsm hkp h13
    simp only [List.reverse_nil, List.nil_append] at hmem
    simp only [List.head?_nil, Option.getD_none] at h13
    refine (step% st 0x800049c8) O.live (fun _ => hex R (hmem ▸ hsm) hkp h13) (fun hne => absurd ?_ hne)
    apply BitVec.eq_of_toNat_eq
    rw [hkp 6 (by decide) (by decide) (by decide) (by decide), h6, h13]
  | cons y rpre ih =>
    intro post R hmem hsm hkp h13
    simp only [List.head?_cons, Option.getD_some] at h13
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hmem
    have hy : y ∈ bins k := by rw [hmem]; simp
    obtain ⟨cy, hcy, hya, hyf⟩ := HH.member (by omega) hk hy
    obtain ⟨cya, sz, cyi⟩ := cy
    simp only at hya hyf
    subst hya hyf
    have K := B.chunkK hcy; have FS := B.freeSpan hcy rfl
    open_fields K; simp only at FS; clear K_next
    have hyne : cya ≠ binAt k := hbne _ hy
    obtain ⟨h, hr, hs, _⟩ := K_hdrv
    have hhlt := Vsa.Sim.read64_lt _ _ _ hr
    obtain ⟨nx, hnx⟩ : ∃ q, (post ++ [binAt k]).head? = some q := by
      rcases post with _ | ⟨z, zs⟩ <;> simp
    have hpred : (binAt k :: rpre.reverse).getLast? = some (rpre.head?.getD (binAt k)) := by
      rcases rpre with _ | ⟨z, zs⟩
      · rfl
      · simp only [List.reverse_cons, List.head?_cons, Option.getD_some]
        rw [← List.cons_append, List.getLast?_concat]
    have hr2 := hring
    rw [hmem] at hr2
    have hbk := (ring_member hr2 hpred hnx).2
    have hbklt := Vsa.Sim.read64_lt _ _ _ hbk
    have h6' : (R 6).toNat = binAt k := by rw [hkp 6 (by decide) (by decide) (by decide) (by decide)]; exact h6
    refine (step% st 0x800049c8) O.live (fun he => absurd he ?_) (fun _ => ?_)
    · intro he; apply hyne
      have := congrArg BitVec.toNat he; rw [h6', h13] at this; exact this.symm
    have hszv : (BitVec.ofNat 64 h &&& 18446744073709551612#64).toNat = sz := by
      rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhlt, ← hs]; rfl
    have key : ∀ R', MKeep R' R0 → (R' 15).toNat = cya → (R' 13).toNat = rpre.head?.getD (binAt k) →
        (R' 12).toNat = sz → R' 11 = R' 12 - R' 14 → AW C.live C.S C.Q 0x800049e0#64 R' Mt := by
      intro R' hkp' v15 v13 v12 v11
      have W' := W.keep hkp'
      have hcmp := lr_cmp v12 W'.a4 (by omega) (by have := W.nb31; omega)
      have h31 : (R' 28).toInt = (31#64).toInt := by
        rw [hkp' 28 (by decide) (by decide) (by decide) (by decide)]; exact toInt_small h28 (by decide)
      rw [← v11] at hcmp
      refine (step% st 0x800049e0) O.live (fun hgt => ?_) (fun hle => ?_)
      · rw [h31] at hgt
        exact bw_split O W' hk1 hk hmem hcy (hcmp.1.1 hgt) hpred v15 v13 v12
          (by rw [v11, BitVec.toNat_sub, v12, W'.a4]; omega)
      · refine (step% st 0x800049e4) O.live (fun hneg => ?_) (fun hnn => ?_)
        · refine ih (cya :: post) _ (by rw [hmem]) (fun z hz sz' hz' => ?_) hkp' v13
          rcases List.mem_cons.mp hz with rfl | hz
          · obtain rfl : sz' = sz := by
              have := HH.chunk_eq hz' hcy rfl; simp at this; exact this
            have := hcmp.2; rw [show ((0#64 : BitVec 64)).toInt = 0 from rfl] at this hneg; omega
          · exact hsm z hz sz' hz'
        · exact bw_take O W' hk1 hk hmem hcy (hcmp.2.1 (Int.not_lt.mp hnn)) hpred v15 v13 v12
    rgn_run O.live at 0x800049e0
    rgn_ld [hr, hbk]
    exact key _ (fun x h11 h12 h13 h15 => by
        simp only [upd_apply, h11, h12, h13, h15, ite_false]; exact hkp x h11 h12 h13 h15)
      h13 (by rw [upd_apply]; rgn_arith) hszv rfl

theorem scanFrom_empty {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} {nb start k : Nat}
    (HH : HeapAt m H (fun e => e ∈ H) top brkv chunks bins) (hsf : ScanFrom chunks bins nb start)
    (hs1 : 1 < start) (hk : start ≤ k) (hkn : k < numBins) (hsm : AllSmall chunks (bins k) nb) :
    bins k = [] := by
  rcases h : bins k with _ | ⟨x, xs⟩
  · rfl
  · exfalso
    have hx : x ∈ bins k := by rw [h]; exact List.mem_cons_self
    have hstart : binIndex nb < start ∨ (binIndex nb ≤ start ∧ start < k) ∨ start = k := by
      rcases hsf with h1 | ⟨y, sy, hy, hfy, hly⟩
      · exact .inl h1
      · by_cases hsk : start = k
        · exact .inr (.inr hsk)
        · refine .inr (.inl ⟨?_, by omega⟩)
          obtain ⟨c, hc, hca, _, hbi⟩ := HH.bin_free start y (by omega) (by omega) hy
          have := HH.chunk_eq hc hfy hca
          subst this
          rw [← hbi (by omega)]
          exact binIndex_mono hly
    rcases hstart with h1 | ⟨h1, h2⟩ | rfl
    · obtain ⟨c, hc, hca, hcf, hbi⟩ := HH.bin_free k x (by omega) hkn hx
      obtain ⟨ca, cs, ci⟩ := c
      simp only at hca hcf hbi
      subst hca hcf
      have hlt := hsm ca hx cs hc
      have := binIndex_mono (Nat.le_of_lt hlt)
      rw [hbi (by omega)] at this; omega
    · obtain ⟨c, hc, hca, hcf, hbi⟩ := HH.bin_free k x (by omega) hkn hx
      obtain ⟨ca, cs, ci⟩ := c
      simp only at hca hcf hbi
      subst hca hcf
      have hlt := hsm ca hx cs hc
      have := binIndex_mono (Nat.le_of_lt hlt)
      rw [hbi (by omega)] at this; omega
    · rcases hsf with h1 | ⟨y, sy, hy, hfy, hly⟩
      · obtain ⟨c, hc, hca, hcf, hbi⟩ := HH.bin_free start x (by omega) hkn hx
        obtain ⟨ca, cs, ci⟩ := c
        simp only at hca hcf hbi
        subst hca hcf
        have hlt := hsm ca hx cs hc
        have := binIndex_mono (Nat.le_of_lt hlt)
        rw [hbi (by omega)] at this; omega
      · exact absurd (hsm y hy sy hfy) (by omega)

end VsaIris.VsaHeap
