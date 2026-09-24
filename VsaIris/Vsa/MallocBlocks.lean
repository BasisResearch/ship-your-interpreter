import VsaIris.Vsa.MallocChain
import VsaIris.Vsa.HeapClear

/-!
# `_malloc_r`'s block walk

`0x80004978` searches the bins from the request's index up, a block of four
bins at a time, for the smallest chunk that fits:

* the bitmap `binblocks` names the blocks that may hold chunks; the walk finds
  the next set bit (`0x80004978`-`0x800049a0`, and `0x80004e64` onwards);
* within a block, each bin is scanned from its smallest member through `bk`
  (`0x800049c8`); a chunk within `MINSIZE` of `nb` is taken whole
  (`0x800049e8`), a larger one is split with the rest becoming the last
  remainder (`0x80004d14`);
* a block found empty has its bit cleared (`0x80004e54`) once the bins below
  the scan's start are checked empty too (`0x80004e3c`); with no set bit left
  above, the walk goes to the top (`0x80004a2c`).

The heap edits are `PHeapAt.take` (`take_ret`), `PHeapAt.splitFree` and
`PHeapAt.clearBlock`.
-/

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The nodes around member `x` of bin `k` and their words, named. -/
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

/-- **What the block walk's take owes the caller**: its four stores (the next
header with `PREV_INUSE`, the successor's `bk`, the predecessor's `fd`, the
spill), with the stored words named by their values. -/
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
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have N := binNbrs Hp hk0 hk hmem hfree hpred hsucc
  have hp16 := N.pred16; have hs16 := N.succ16; have hbp := N.predNx; have hbs := N.succNx
  have hlo := hsp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hb := HH.walk.chunk_bounds _ hfree
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapStart at hb; unfold heapEnd at hbrk
  simp only at hb
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hx16 := hal0 _ hfree
  have hsz16 := (walk_sizes HH.walk _ hfree).1
  simp only at hx16 hsz16
  have hnxf := foot_header B (HH.end_bnd hfree)
  simp only at hnxf
  have hns : ∀ a, vsaFoot C.H a → a < C.s.toNat - 256 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => Hp.disj a (by unfold mHead; omega) (by omega) ha
  have hoN := hns _ (hnxf 0 (by omega))
  have hoS := hns (succ + 24) (by have := N.succFoot 24 (by omega) (by omega); simpa using this)
  have hoP := hns (pred + 16) (by have := N.predFoot 16 (by omega) (by omega); simpa using this)
  simp only [Nat.add_zero] at hoN
  refine take_ret Hp hnb hk0 hk hmem hfree hle hpred hsucc ?_ ?_ ?_ ?_ ?_ ?_
  · show read64 _ (pred + 16) = _
    rw [read64_store_miss _ _ (by omega), read64_store_hit, h3]
  · show read64 _ (succ + 24) = _
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega), read64_store_hit, h2]
  · intro hd' hd'r
    rw [hdr] at hd'r; cases hd'r
    rw [read64_store_miss _ _ (by omega), read64_store_miss _ _ (by omega),
      read64_store_miss _ _ (by omega), read64_store_hit, h1]
  · intro a ha hna
    unfold TakeW at hna
    have := hns a ha
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  · intro a ha
    exact writeLog_present _ _ _ (writeLog_present _ _ _ (writeLog_present _ _ _
      (writeLog_present _ _ _ (Hp.pres a ha))))
  · exact frame_store (win_stack (by unfold mHead; omega) (by omega))
      (frame_store (win_foot (fun k hk => by
        have := N.predFoot (16 + k) (by omega) (by omega)
        rwa [show pred + (16 + k) = pred + 16 + k by omega] at this))
        (frame_store (win_foot (fun k hk => by
          have := N.succFoot (24 + k) (by omega) (by omega)
          rwa [show succ + (24 + k) = succ + 24 + k by omega] at this))
          (frame_store (win_foot hnxf) Hp.frame)))

/-- **What the block walk's split owes the caller**: its ten stores (the
victim's header, the unlink, bin 1's links, the remainder's links and header,
its footer, and the spill), with the stored words named by their values. -/
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
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have N := binNbrs Hp (by omega) hk hmem hfree hpred hsucc
  have hp16 := N.pred16; have hs16 := N.succ16; have hpsep := N.predSep; have hssep := N.succSep
  have hploc := N.predLoc; have hsloc := N.succLoc
  have hlo := hsp.lo; unfold mHead Vsa.Sim.tohostAddr at hlo
  have hxb := HH.walk.chunk_bounds _ hfree
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapStart at hxb; unfold heapEnd at hbrk
  simp only at hxb
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hx16 := hal0 _ hfree
  have hsz16 := (walk_sizes HH.walk _ hfree).1
  simp only at hx16 hsz16
  have hnb16 := hnb.al; have hnb32 := hnb.lo; have hn8 := hnb.fits
  have hgk := binAt_geo k hk
  have hg1 := binAt_geo 1 (by unfold numBins; decide)
  unfold binAt avAddr at hgk hg1 hploc hsloc
  have hFV := foot_free_span B hfree rfl
  simp only at hFV
  have hoff := Hp.off_stack_w (a := x + 8) (w := sz + 8) (by omega)
    (fun k hk => hFV _ (by omega) (by omega))
  have hns : ∀ a, vsaFoot C.H a → a < C.s.toNat - 256 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => Hp.disj a (by unfold mHead; omega) (by omega) ha
  have hoS := hns (succ + 24) (by have := N.succFoot 24 (by omega) (by omega); simpa using this)
  have hoP := hns (pred + 16) (by have := N.predFoot 16 (by omega) (by omega); simpa using this)
  have hoB := hns (0x8001ad10 + 16 * 1 + 16) (.inl (.inl ⟨by omega, by omega⟩))
  unfold mHead at hoff
  obtain ⟨cs₁, cs₂, hsp'⟩ := List.append_of_mem hfree
  have Hp0 := Hp.heap
  rw [hsp'] at Hp0
  have Hs := Hp0.splitFree (i := k) (by omega) hk hmem hnb16 hnb32 hle (n := C.n.toNat) (by omega)
    (by rw [updBins_other _ _ (by omega : (1 : Nat) ≠ k)]; exact hb1) hpred hsucc
    (m' := writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog (writeLog
      (writeLog (writeLog Mt [(x + 8, 8, wh)]) [(succ + 24, 8, wp)]) [(pred + 16, 8, ws)])
      [(binAt 1 + 24, 8, wr)]) [(binAt 1 + 16, 8, wr)]) [(x + nb + 24, 8, wb)])
      [(x + nb + 16, 8, wb)]) [(x + nb + 8, 8, wrh)]) [(x + sz, 8, wf)])
      [(C.s.toNat - 96 + 8, 8, wx)])
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  rotate_left 1
  · intro _; show read64 _ (pred + 16) = _
    unfold binAt avAddr; simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [hs]
  · intro _; show read64 _ (succ + 24) = _
    unfold binAt avAddr; simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [hp]
  · unfold binAt avAddr; simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [hh]
  · unfold binAt avAddr; simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [hrh]
  · show read64 _ (x + nb + 16) = _
    unfold binAt avAddr; simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [hb]; rfl
  · show read64 _ (x + nb + 24) = _
    unfold binAt avAddr; simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [hb]; rfl
  · show read64 _ (binAt 1 + 16) = _
    unfold binAt avAddr; simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [hr]
  · show read64 _ (binAt 1 + 24) = _
    unfold binAt avAddr; simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [hr]
  · unfold binAt avAddr; simp (disch := omega) only [read64_hit_eq, read64_miss]; rw [hf]
  · unfold binAt avAddr; simp (disch := omega) only [read64_miss]
  · intro a ha hT hC
    unfold TakeW at hT; unfold CarveW at hC
    unfold binAt avAddr at *
    have := hns a ha
    rw [writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out, writeLog_out,
      writeLog_out, writeLog_out, writeLog_out, writeLog_out] <;> simp only [OutL, and_true] <;> omega
  obtain ⟨hfr, hal16⟩ := PHeapAt.take_fresh Hp.heap hfree rfl (n := C.n.toNat) (by simp only; omega)
  refine ⟨hfr, hal16, ⟨_, _, _, _, Hs, by omega⟩, fun a ha => ?_, ?_⟩
  · repeat (apply writeLog_present)
    exact Hp.pres a ha
  have hw : ∀ a w, x + 8 ≤ a → a + w ≤ x + sz + 16 → ∀ b, a ≤ b → b < a + w → MWin C.H C.s b :=
    fun a w h1 h2 b hb1 hb2 => .inl (hFV b (by omega) (by omega))
  have hwb : ∀ b, binAt 1 + 16 ≤ b → b < binAt 1 + 32 → MWin C.H C.s b :=
    fun b hb1 hb2 => .inl (.inl (.inl ⟨by unfold binAt avAddr at hb1; omega,
      by unfold binAt avAddr at hb2; omega⟩))
  have hwp : ∀ b, pred + 16 ≤ b → b < pred + 16 + 8 → MWin C.H C.s b := fun b h1 h2 => .inl (by
    have := N.predFoot (b - pred) (by omega) (by omega)
    rwa [show pred + (b - pred) = b by omega] at this)
  have hws : ∀ b, succ + 24 ≤ b → b < succ + 24 + 8 → MWin C.H C.s b := fun b h1 h2 => .inl (by
    have := N.succFoot (b - succ) (by omega) (by omega)
    rwa [show succ + (b - succ) = b by omega] at this)
  exact frame_store (win_stack (by unfold mHead; omega) (by omega))
    (frame_store (hw _ _ (by omega) (by omega)) (frame_store (hw _ _ (by omega) (by omega))
      (frame_store (hw _ _ (by omega) (by omega)) (frame_store (hw _ _ (by omega) (by omega))
          (frame_store (fun b h1 h2 => hwb b (by omega) (by omega))
            (frame_store (fun b h1 h2 => hwb b (by omega) (by omega))
              (frame_store hwp (frame_store hws
                (frame_store (hw _ _ (by omega) (by omega)) Hp.frame)))))))))

end VsaIris.VsaHeap
