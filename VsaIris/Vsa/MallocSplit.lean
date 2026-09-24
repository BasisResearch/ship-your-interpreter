import VsaIris.Vsa.MallocExtend
import VsaIris.Vsa.HeapCarve

/-!
# `_malloc_r`'s splits of a free chunk

A free chunk at least `nb + MINSIZE` large is split: its first `nb` bytes are
returned and the rest becomes the last remainder, the only member of bin 1.

* `lr_split` (`0x80004da0`): the last remainder itself, already bin 1's only
  member, is split.

The heap edit is `PHeapAt.splitFree` (`HeapCarve.lean`).
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- Every byte of a free chunk from its header to the next chunk's header is
allocator footprint. -/
theorem foot_free_span {m : Mem} {H : List (Nat × Nat)} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (B : BlockHeapAt m H top brkv chunks bins) {c : Chunk}
    (hc : c ∈ chunks) (hf : c.inuse = false) :
    ∀ a, c.addr + 8 ≤ a → a < c.addr + c.size + 16 → vsaFoot H a := by
  have hb := B.heap.walk.chunk_bounds
  have hs := B.heap.walk.chunk_sep
  have hroom := B.top_room
  have hbrk := B.heap.brk_le
  have hle := B.heap.walk.le
  have hbc := hb c hc
  intro a h1 h2
  by_cases hh : a < c.addr + 16
  · have := foot_header B (.inr ⟨c, hc, rfl⟩) (a - (c.addr + 8)) (by omega)
    rwa [show c.addr + 8 + (a - (c.addr + 8)) = a by omega] at this
  by_cases ht : c.addr + c.size + 8 ≤ a
  · have := foot_header B (B.heap.end_bnd hc |>.elim .inl .inr) (a - (c.addr + c.size + 8))
      (by omega)
    rwa [show c.addr + c.size + 8 + (a - (c.addr + c.size + 8)) = a by omega] at this
  refine foot_of_arena B.heap (by unfold heapStart at *; omega) (by omega) ?_
  intro c' hc' hu hin
  have := hb c' hc'
  rcases hs c' hc' c hc with rfl | h3 | h3
  · rw [hu] at hf; cases hf
  · omega
  · omega

/-- **What a split of the last remainder owes the caller.** The machine's
eight stores (`v`'s header, bin 1's links, the remainder's links, header and
footer, and the spill of `v`), with the stored words named by their values,
leave the heap with the block `(v + 16, n)` live. -/
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
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have hbnd := HH.walk.chunk_bounds _ hfree
  have htle := HH.top_le; have hbrk := HH.brk_le
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hv16 := hal0 _ hfree
  have hsz16 := (walk_sizes HH.walk _ hfree).1
  simp only at hbnd hv16 hsz16
  unfold heapStart at hbnd; unfold heapEnd at hbrk
  have hnb16 := hnb.al; have hnb32 := hnb.lo
  have hn8 := hnb.fits
  have hslo := hsp.lo
  unfold mHead Vsa.Sim.tohostAddr at hslo
  have hFV := foot_free_span B hfree rfl
  simp only at hFV
  have hoff := Hp.off_stack_w (a := v + 8) (w := sz + 8) (by omega)
    (fun k hk => hFV _ (by omega) (by omega))
  have hg1 := binAt_geo 1 (by unfold numBins; decide)
  have hbw : ∀ k, k < 16 → vsaFoot C.H (binAt 1 + 16 + k) :=
    fun k hk => .inl (.inl ⟨by omega, by omega⟩)
  have hoffb := Hp.off_stack_w (a := binAt 1 + 16) (w := 16) (by omega) hbw
  unfold mHead at hoff hoffb
  have hns : ∀ a, vsaFoot C.H a → a < C.s.toNat - 256 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => Hp.disj a (by unfold mHead; omega) (by omega) ha
  obtain ⟨cs₁, cs₂, hsp⟩ := List.append_of_mem hfree
  have Hp0 := Hp.heap
  rw [hsp] at Hp0
  have Hs := Hp0.splitFree (i := 1) (by decide) (by unfold numBins; decide) (pre := []) (post := [])
    (by rw [hbin]; rfl) hnb16 hnb32 hle (n := C.n.toNat) hn8 (by rw [updBins_same]; rfl)
    (pred := binAt 1) (succ := binAt 1) rfl rfl (fun h => absurd rfl h) (fun h => absurd rfl h)
    (m' := writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog Mt
      [(v + 8, 8, w1)]) [(binAt 1 + 24, 8, w2)]) [(binAt 1 + 16, 8, w2)])
      [(v + nb + 24, 8, w4)]) [(v + nb + 16, 8, w4)]) [(v + nb + 8, 8, w6)])
      [(v + sz, 8, w7)]) [(C.s.toNat - 96 + 8, 8, w8)])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  rotate_left 1
  · simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [h1]
  · simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [h6]
  · show read64 _ (v + nb + 16) = _
    simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [h4]
  · show read64 _ (v + nb + 24) = _
    simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [h4]
  · show read64 _ (binAt 1 + 16) = _
    simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [h2]
  · show read64 _ (binAt 1 + 24) = _
    simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [h2]
  · simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [h7]
  · simp (disch := omega) only [read64_miss]
  · intro a ha hT hC
    unfold TakeW at hT; unfold CarveW at hC
    have := hns a ha
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  obtain ⟨hfr, hal16⟩ := PHeapAt.take_fresh Hp.heap hfree rfl (n := C.n.toNat) (by simp only; omega)
  refine ⟨hfr, hal16, ⟨_, _, _, _, Hs, by omega, Hp.live.split hsp _ _⟩,
    pres_store (pres_store (pres_store (pres_store (pres_store (pres_store (pres_store
      (pres_store Hp.pres))))))), ?_⟩
  have hw : ∀ a w, v + 8 ≤ a → a + w ≤ v + sz + 16 → ∀ b, a ≤ b → b < a + w → MWin C.H C.s b :=
    fun a w h1 h2 b hb1 hb2 => .inl (hFV b (by omega) (by omega))
  have hwb : ∀ b, binAt 1 + 16 ≤ b → b < binAt 1 + 32 → MWin C.H C.s b :=
    fun b hb1 hb2 => .inl (hbw (b - (binAt 1 + 16)) (by omega) |> fun h => by
      rwa [show binAt 1 + 16 + (b - (binAt 1 + 16)) = b by omega] at h)
  exact frame_store (win_stack (by unfold mHead; omega) (by omega))
    (frame_store (hw _ _ (by omega) (by omega)) (frame_store (hw _ _ (by omega) (by omega))
      (frame_store (hw _ _ (by omega) (by omega)) (frame_store (hw _ _ (by omega) (by omega))
        (frame_store (fun b h1 h2 => hwb b (by omega) (by omega))
          (frame_store (fun b h1 h2 => hwb b (by omega) (by omega))
            (frame_store (hw _ _ (by omega) (by omega)) Hp.frame)))))))

/-- **Split the last remainder** (`0x80004da0`): bin 1's only member `v`, of
size `sz ≥ nb + MINSIZE`, gives its first `nb` bytes to the request and its
rest becomes the new last remainder. -/
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
  -- `ori a2,a4,1; sd a2,8(a5)`: `v`'s header
  refine st_80004da0 O.live ?_
  refine st_80004da4 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm
  -- `add a4,a5,a4; sd a4,40(a6); sd a4,32(a6)`: bin 1's links
  refine st_80004da8 O.live ?_
  refine st_80004dac O.live ?_ ?_ ?_
  · sx_norm; rw [ha6]; decide
  · sx_norm; rw [ha6]; exact O.bin_link (j := 1) (by unfold numBins; decide) (.inr (by rw [hb1]; decide))
  sx_norm
  refine st_80004db0 O.live ?_ ?_ ?_
  · sx_norm; rw [ha6]; decide
  · sx_norm; rw [ha6]; exact O.bin_link (j := 1) (by unfold numBins; decide) (.inl (by rw [hb1]; decide))
  sx_norm
  -- `ori a2,a3,1; add t1,a5,t1; sd t4,24(a4); sd t4,16(a4); sd a2,8(a4)`: the remainder
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
  -- `mv a0,s0; sd a3,0(t1)`: the remainder's footer
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
