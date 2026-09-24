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

/-- The block walk's invariant registers: the heap (with bin 1 empty), the
request `nb` in `a4`, `__malloc_av_` in `a6`, bin 1's header in `t4`, and the
reentrancy structure in `s0`. -/
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

/-- **The block walk's take** (`0x800049e8`): member `x` of bin `k` (its
predecessor in `a3`, its size in `a2`) fits within `MINSIZE`; unlink it, set
`PREV_INUSE` after it, and return `x + 16`. -/
theorem bw_take {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb k x sz pred : Nat} {pre post : List Nat}
    (W : BW C Mt brkv chunks bins nb R) (hk1 : 1 < k) (hk : k < numBins)
    (hmem : bins k = pre ++ x :: post) (hfree : FreeAt chunks x sz) (hle : nb ≤ sz)
    (hpred : (binAt k :: pre).getLast? = some pred)
    (h15 : (R 15).toNat = x) (h13 : (R 13).toNat = pred) (h12 : (R 12).toNat = sz) :
    AW C.live C.S C.Q 0x800049e8#64 R Mt := by
  have HH := W.heap.heap.heap.heap
  have B := W.heap.heap.heap
  obtain ⟨succ, hsucc⟩ : ∃ q, (post ++ [binAt k]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have N := binNbrs W.heap (by omega) hk hmem hfree hpred hsucc
  have hp16 := N.pred16; have hs16 := N.succ16; have hpsep := N.predSep; have hssep := N.succSep
  have hploc := N.predLoc; have hsloc := N.succLoc
  have hxb := HH.walk.chunk_bounds _ hfree
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapStart at hxb; unfold heapEnd at hbrk
  simp only at hxb
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hx16 := hal0 _ hfree
  have hsz16 := (walk_sizes HH.walk _ hfree).1
  simp only at hx16 hsz16
  have hgk := binAt_geo k hk
  unfold binAt avAddr at hgk hploc hsloc
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := W.frame.sp
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [hs2]; sx_addr
  have hring := (binList_iff_ring.1 (HH.bins_list k (by omega) hk)).1
  rw [hmem] at hring
  have hfd := (ring_member hring hpred hsucc).1
  have hsuccl := Vsa.Sim.read64_lt _ _ _ hfd
  obtain ⟨_, ⟨hd, hdr, hdp⟩⟩ := HH.headers hfree
  simp only at hdr hdp
  have hdlt := Vsa.Sim.read64_lt _ _ _ hdr
  have hdev : hd % 2 = 0 := by
    unfold prevInuse at hdp; simp only [beq_eq_false_iff_ne, ne_eq] at hdp; omega
  have hnxf := foot_header B (HH.end_bnd hfree)
  simp only at hnxf
  have hvf := foot_free_span B hfree rfl
  simp only at hvf
  have hns : ∀ a, vsaFoot C.H a → a < C.s.toNat - 256 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => W.heap.disj a (by unfold mHead; omega) (by omega) ha
  have hoN := hns _ (hnxf 0 (by omega))
  have hoS := hns (succ + 24) (by have := N.succFoot 24 (by omega) (by omega); simpa using this)
  have hoP := hns (pred + 16) (by have := N.predFoot 16 (by omega) (by omega); simpa using this)
  simp only [Nat.add_zero] at hoN
  -- `add a2,a5,a2; ld a4,8(a2)`: the next header
  refine st_800049e8 O.live ?_
  sx_norm
  have hEn : (R 15 + R 12 + 8#64).toNat = x + sz + 8 := by sx_addr
  refine st_800049ec O.live ?_ ?_ ?_
  · sx_norm; rw [hEn]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEn]; exact O.foot_at hnxf _ rfl
  sx_norm
  rw [ldv_at hdr _ hEn]
  -- `ld a1,16(a5)`: the successor
  have hEf : (R 15 + 16#64).toNat = x + 16 := by sx_addr
  refine st_800049f0 O.live ?_ ?_ ?_
  · sx_norm; rw [hEf]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEf]; exact O.foot (fun k hk => hvf _ (by omega) (by omega))
  sx_norm
  rw [ldv_at hfd _ hEf]
  refine st_800049f4 O.live ?_
  refine st_800049f8 O.live ?_
  -- `sd a4,8(a2)`: `PREV_INUSE`
  refine st_800049fc O.live ?_ ?_ ?_
  · sx_norm; rw [hEn]; unfold StOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEn]; exact O.foot_at hnxf _ rfl
  sx_norm
  rw [hEn]
  -- `sd a3,24(a1); sd a1,16(a3)`: the unlink
  have hEs : (BitVec.ofNat 64 succ + 24#64).toNat = succ + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuccl]; simp; omega
  refine st_80004a00 O.live ?_ ?_ ?_
  · sx_norm; rw [hEs]; unfold StOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEs]; exact O.foot (fun k hk => by
      have := N.succFoot (24 + k) (by omega) (by omega)
      rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
  sx_norm
  rw [hEs]
  have hEp : (R 13 + 16#64).toNat = pred + 16 := by sx_addr
  refine st_80004a04 O.live ?_ ?_ ?_
  · sx_norm; rw [hEp]; unfold StOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEp]; exact O.foot (fun k hk => by
      have := N.predFoot (16 + k) (by omega) (by omega)
      rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
  sx_norm
  rw [hEp]
  sx_run [8] O.live at 0x8000484c
  rw [show (R 2 + 8#64).toNat = C.s.toNat - 96 + 8 by sx_addr]
  have hOr : (BitVec.ofNat 64 hd ||| 1#64).toNat = hd + 1 :=
    or1_toNat (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdlt]) hdev
  refine epi_8000484c O ?F (O.fin_take (v := x) ?_ (bw_take_ret O.sp W.heap W.nbok (by omega) hk hmem
    hfree hle hpred hsucc hdr hOr h13 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuccl])))
  case F =>
    refine MFrame.of_regs ((((W.frame.store (by omega)).store (by omega)).store (by omega)).store
      (by omega)) ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  sx_addr

/-- The block walk's split, second half (`0x80004d34`): the remainder's
links, header and footer, the spill, and the return. -/
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
  have HH := Hp.heap.heap.heap
  have B := Hp.heap.heap
  have N := binNbrs Hp (by omega) hk hmem hfree hpred hsucc
  have hp16 := N.pred16; have hs16 := N.succ16; have hpsep := N.predSep; have hssep := N.succSep
  have hploc := N.predLoc; have hsloc := N.succLoc
  have hxb := HH.walk.chunk_bounds _ hfree
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapStart at hxb; unfold heapEnd at hbrk
  simp only at hxb
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hx16 := hal0 _ hfree
  have hsz16 := (walk_sizes HH.walk _ hfree).1
  simp only at hx16 hsz16
  have hnb16 := hnb.al; have hnb32 := hnb.lo
  have hgk := binAt_geo k hk
  unfold binAt avAddr at hgk hploc hsloc
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := F1.sp
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [hs2]; sx_addr
  have hFV := foot_free_span B hfree rfl
  simp only at hFV
  -- `ori a3,a1,1; add a2,a5,a2; sd t4,24(a4); sd t4,16(a4); sd a3,8(a4)`: the remainder
  refine st_80004d34 O.live ?_
  refine st_80004d38 O.live ?_
  refine st_80004d3c O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm
  refine st_80004d40 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm
  refine st_80004d44 O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm
  -- `mv a0,s0; sd a1,0(a2)`: the footer
  refine st_80004d48 O.live ?_
  refine st_80004d4c O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm
  have e4 : (R 14 + 24#64).toNat = x + nb + 24 := by sx_addr
  have e5 : (R 14 + 16#64).toNat = x + nb + 16 := by sx_addr
  have e6 : (R 14 + 8#64).toNat = x + nb + 8 := by sx_addr
  have e7 : (R 15 + R 12).toNat = x + sz := by sx_addr
  rw [e4, e5, e6, e7]
  sx_run [8] O.live at 0x8000484c
  rw [show (R 2 + 8#64).toNat = C.s.toNat - 96 + 8 by sx_addr]
  have hoff := Hp.off_stack_w (a := x + 8) (w := sz + 8) (by omega)
    (fun k hk => hFV _ (by omega) (by omega))
  have hns : ∀ a, vsaFoot C.H a → a < C.s.toNat - 256 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => Hp.disj a (by unfold mHead; omega) (by omega) ha
  have hoS := hns (succ + 24) (by have := N.succFoot 24 (by omega) (by omega); simpa using this)
  have hoP := hns (pred + 16) (by have := N.predFoot 16 (by omega) (by omega); simpa using this)
  unfold mHead at hoff
  refine epi_8000484c O ?F (O.fin_take (v := x) ?_ (bw_split_ret O.sp Hp hnb hk1 hk hb1
    hmem hfree hle hpred hsucc hh hp hs h14 ht4 (or1_toNat h11 (by omega)) h11))
  case F =>
    refine MFrame.of_regs (((((F1.store (by omega)).store (by omega)).store (by omega)).store
      (by omega)).store (by omega)) ?_ ?_ ?_ ?_ <;> simp only [upd_apply, Nat.reduceEqDiff, ite_false]
  simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
  sx_addr


/-- **The block walk's split** (`0x80004d14`): member `x` of bin `k` (its
predecessor in `a3`, its size in `a2`, the remainder `sz - nb ≥ MINSIZE` in
`a1`) is unlinked and split; its first `nb` bytes are returned and the rest
becomes the last remainder. -/
theorem bw_split {C : MCtx} (O : MOK C) {R : Nat → BitVec 64} {Mt : Mem} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} {nb k x sz pred : Nat} {pre post : List Nat}
    (W : BW C Mt brkv chunks bins nb R) (hk1 : 1 < k) (hk : k < numBins)
    (hmem : bins k = pre ++ x :: post) (hfree : FreeAt chunks x sz) (hle : nb + 32 ≤ sz)
    (hpred : (binAt k :: pre).getLast? = some pred)
    (h15 : (R 15).toNat = x) (h13 : (R 13).toNat = pred) (h12 : (R 12).toNat = sz)
    (h11 : (R 11).toNat = sz - nb) :
    AW C.live C.S C.Q 0x80004d14#64 R Mt := by
  have HH := W.heap.heap.heap.heap
  have B := W.heap.heap.heap
  obtain ⟨succ, hsucc⟩ : ∃ q, (post ++ [binAt k]).head? = some q := by
    rcases post with _ | ⟨z, zs⟩ <;> simp
  have N := binNbrs W.heap (by omega) hk hmem hfree hpred hsucc
  have hp16 := N.pred16; have hs16 := N.succ16; have hpsep := N.predSep; have hssep := N.succSep
  have hploc := N.predLoc; have hsloc := N.succLoc
  have hxb := HH.walk.chunk_bounds _ hfree
  have htle := HH.top_le; have hbrk := HH.brk_le
  unfold heapStart at hxb; unfold heapEnd at hbrk
  simp only at hxb
  obtain ⟨hal0, htop16⟩ := HH.aligned
  have hx16 := hal0 _ hfree
  have hsz16 := (walk_sizes HH.walk _ hfree).1
  simp only at hx16 hsz16
  have hnb16 := W.nbok.al; have hnb32 := W.nbok.lo
  have ha4 := W.a4; have ha6 := W.a6; have ht4 := W.t4
  have hgk := binAt_geo k hk
  have hg1 := binAt_geo 1 (by unfold numBins; decide)
  have hb1 : binAt 1 = 2147593504 := by unfold binAt avAddr; rfl
  unfold binAt avAddr at hgk hploc hsloc
  have hlo := O.sp.lo; have hhi := O.sp.hi; have hsal := O.sp.align
  unfold mHead Vsa.Sim.tohostAddr at hlo
  have hs2 := W.frame.sp
  have hs2n : (R 2).toNat = C.s.toNat - 96 := by rw [hs2]; sx_addr
  have hring := (binList_iff_ring.1 (HH.bins_list k (by omega) hk)).1
  rw [hmem] at hring
  have hfd := (ring_member hring hpred hsucc).1
  have hsuccl := Vsa.Sim.read64_lt _ _ _ hfd
  have hFV := foot_free_span B hfree rfl
  simp only at hFV
  -- `ld a0,16(a5)`: the successor
  have hEf : ((R 15) + sign_extend (m := 64) (0x010#12)).toNat = x + 16 := by sx_addr
  refine st_80004d14 O.live ?_ ?_ ?_
  · rw [hEf]; unfold LdOK Vsa.Sim.tohostAddr; omega
  · rw [hEf]; exact O.foot (fun k hk => hFV _ (by omega) (by omega))
  rw [ldv_at hfd _ hEf]
  -- `ori a7,a4,1; sd a7,8(a5)`: the victim's header
  refine st_80004d18 O.live ?_
  refine st_80004d1c O.live ?_ ?_ ?_
  · sx_norm; sx_addr
  · sx_norm; exact O.foot (fun k hk => hFV _ (by sx_addr) (by sx_addr))
  sx_norm
  -- `sd a3,24(a0); sd a0,16(a3)`: the unlink
  have hEs : (BitVec.ofNat 64 succ + 24#64).toNat = succ + 24 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuccl]; simp; omega
  refine st_80004d20 O.live ?_ ?_ ?_
  · sx_norm; rw [hEs]; unfold StOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEs]; exact O.foot (fun k hk => by
      have := N.succFoot (24 + k) (by omega) (by omega)
      rwa [show succ + (24 + k) = succ + 24 + k by omega] at this)
  sx_norm
  have hEp : (R 13 + 16#64).toNat = pred + 16 := by sx_addr
  refine st_80004d24 O.live ?_ ?_ ?_
  · sx_norm; rw [hEp]; unfold StOK Vsa.Sim.tohostAddr; omega
  · sx_norm; rw [hEp]; exact O.foot (fun k hk => by
      have := N.predFoot (16 + k) (by omega) (by omega)
      rwa [show pred + (16 + k) = pred + 16 + k by omega] at this)
  sx_norm
  -- `add a4,a5,a4; sd a4,40(a6); sd a4,32(a6)`: bin 1's links
  refine st_80004d28 O.live ?_
  refine st_80004d2c O.live ?_ ?_ ?_
  · sx_norm; rw [ha6]; decide
  · sx_norm; rw [ha6]; exact O.bin_link (j := 1) (by unfold numBins; decide) (.inr (by rw [hb1]; decide))
  sx_norm
  refine st_80004d30 O.live ?_ ?_ ?_
  · sx_norm; rw [ha6]; decide
  · sx_norm; rw [ha6]; exact O.bin_link (j := 1) (by unfold numBins; decide) (.inl (by rw [hb1]; decide))
  sx_norm
  have e1 : (R 15 + 8#64).toNat = x + 8 := by sx_addr
  have e2 : (R 16 + 40#64).toNat = binAt 1 + 24 := by rw [ha6, hb1]; rfl
  have e3 : (R 16 + 32#64).toNat = binAt 1 + 16 := by rw [ha6, hb1]; rfl
  rw [e1, e2, e3, hEs, hEp]
  have hoV := W.heap.off_stack_w (a := x + 8) (w := sz + 8) (by omega)
    (fun k hk => hFV _ (by omega) (by omega))
  have hns : ∀ a, vsaFoot C.H a → a < C.s.toNat - 256 ∨ C.s.toNat ≤ a := fun a ha =>
    Classical.byContradiction fun hc => W.heap.disj a (by unfold mHead; omega) (by omega) ha
  have hoS := hns (succ + 24) (by have := N.succFoot 24 (by omega) (by omega); simpa using this)
  have hoP := hns (pred + 16) (by have := N.predFoot 16 (by omega) (by omega); simpa using this)
  unfold mHead at hoV
  exact bw_split2 O W.heap W.nbok W.b1 (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact ht4)
    hk1 hk hmem hfree hle hpred hsucc rfl
    ((((((W.frame.store (by omega)).store (by omega)).store (by omega)).store
      (by unfold binAt avAddr; omega)).store (by unfold binAt avAddr; omega)).of_regs
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false])
      (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]))
    (or1_toNat ha4 (by omega)) h13 (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuccl])
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h15)
    (by simp only [upd_apply, ite_true]; sx_addr)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h12)
    (by simp only [upd_apply, Nat.reduceEqDiff, ite_false]; exact h11)

/-- The registers a member walk leaves alone agree with the reference `R0`. -/
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

/-- A bin's members smaller than `nb`. -/
abbrev AllSmall (chunks : List Chunk) (l : List Nat) (nb : Nat) : Prop :=
  ∀ x ∈ l, ∀ sz, FreeAt chunks x sz → sz < nb

/-- **The member walk** (`0x800049c8`) over bin `k`, from its last member
backwards: a member at least `nb + MINSIZE` is split, one within `MINSIZE`
of `nb` taken, a smaller one passed; reaching the header exhausts the bin
(`0x80004cfc`), all of its members smaller than `nb`. -/
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
    refine st_800049c8 O.live (fun _ => hex R (hmem ▸ hsm) hkp h13) (fun hne => absurd ?_ hne)
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
    have hyb := HH.walk.chunk_bounds _ hcy
    have htle := HH.top_le; have hbrk := HH.brk_le
    unfold heapStart at hyb; unfold heapEnd at hbrk
    simp only at hyb
    have hyne : cya ≠ binAt k := hbne _ hy
    have hfoot : ∀ o, 8 ≤ o → o < 32 → vsaFoot C.H (cya + o) := by
      intro o h1 h2
      by_cases ho : o < 16
      · have := foot_header B (.inr ⟨_, hcy, rfl⟩) (o - 8) (by omega)
        rwa [show cya + 8 + (o - 8) = cya + o by omega] at this
      · exact B.node_foot (by omega) hk (.inr hy) o (by omega) h2
    obtain ⟨⟨h, hr, hs, _⟩, _⟩ := HH.headers hcy
    simp only at hr hs
    have hhlt := Vsa.Sim.read64_lt _ _ _ hr
    -- `bk y`: the next node back
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
    have h14 := (W.keep hkp).a4
    have h6' : (R 6).toNat = binAt k := by rw [hkp 6 (by decide) (by decide) (by decide) (by decide)]; exact h6
    have h28' : (R 28).toNat = 31 := by rw [hkp 28 (by decide) (by decide) (by decide) (by decide)]; exact h28
    refine st_800049c8 O.live (fun he => absurd he ?_) (fun _ => ?_)
    · intro he; apply hyne
      have := congrArg BitVec.toNat he; rw [h6', h13] at this; exact this.symm
    have hEh : ((R 13) + sign_extend (m := 64) (0x008#12)).toNat = cya + 8 := by sx_addr
    refine st_800049cc O.live ?_ ?_ ?_
    · rw [hEh]; unfold LdOK Vsa.Sim.tohostAddr; omega
    · rw [hEh]; exact O.foot (fun k hk => by
        have := hfoot (8 + k) (by omega) (by omega)
        rwa [show cya + (8 + k) = cya + 8 + k by omega] at this)
    rw [ldv_at hr _ hEh]
    refine st_800049d0 O.live ?_
    sx_norm
    have hEb : (R 13 + 24#64).toNat = cya + 24 := by sx_addr
    refine st_800049d4 O.live ?_ ?_ ?_
    · sx_norm; rw [hEb]; unfold LdOK Vsa.Sim.tohostAddr; omega
    · sx_norm; rw [hEb]; exact O.foot (fun k hk => by
        have := hfoot (24 + k) (by omega) (by omega)
        rwa [show cya + (24 + k) = cya + 24 + k by omega] at this)
    sx_norm
    rw [hEb, ldv_at hbk _ rfl]
    refine st_800049d8 O.live ?_
    refine st_800049dc O.live ?_
    sx_norm
    have hszv : (BitVec.ofNat 64 h &&& 18446744073709551612#64).toNat = sz := by
      rw [toNat_and_m4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hhlt, ← hs]; rfl
    have hcmp := lr_cmp hszv h14 (by omega) (by have := W.nb31; omega)
    have h31 : (R 28).toInt = (31 : Int) := toInt_small h28' (by decide)
    have h31' : ((31#64 : BitVec 64)).toInt = (31 : Int) := by decide
    have hkp' : MKeep (upd (upd (upd (upd (upd R 12 (BitVec.ofNat 64 h)) 15 (R 13)) 13
        (BitVec.ofNat 64 (rpre.head?.getD (binAt k)))) 12
        (BitVec.ofNat 64 h &&& 18446744073709551612#64)) 11
        ((BitVec.ofNat 64 h &&& 18446744073709551612#64) - R 14)) R0 :=
      fun x h11 h12 h13 h15 => by
        simp only [upd_apply, h11, h12, h13, h15, ite_false]; exact hkp x h11 h12 h13 h15
    have hvals : (upd (upd (upd (upd (upd R 12 (BitVec.ofNat 64 h)) 15 (R 13)) 13
        (BitVec.ofNat 64 (rpre.head?.getD (binAt k)))) 12
        (BitVec.ofNat 64 h &&& 18446744073709551612#64)) 11
        ((BitVec.ofNat 64 h &&& 18446744073709551612#64) - R 14) 15).toNat = cya ∧
        (upd (upd (upd (upd (upd R 12 (BitVec.ofNat 64 h)) 15 (R 13)) 13
        (BitVec.ofNat 64 (rpre.head?.getD (binAt k)))) 12
        (BitVec.ofNat 64 h &&& 18446744073709551612#64)) 11
        ((BitVec.ofNat 64 h &&& 18446744073709551612#64) - R 14) 13).toNat =
          rpre.head?.getD (binAt k) ∧
        (upd (upd (upd (upd (upd R 12 (BitVec.ofNat 64 h)) 15 (R 13)) 13
        (BitVec.ofNat 64 (rpre.head?.getD (binAt k)))) 12
        (BitVec.ofNat 64 h &&& 18446744073709551612#64)) 11
        ((BitVec.ofNat 64 h &&& 18446744073709551612#64) - R 14) 12).toNat = sz := by
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false]
      exact ⟨h13, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbklt], hszv⟩
    refine st_800049e0 O.live (fun hgt => ?_) (fun hle => ?_)
    · -- at least `MINSIZE` over: split
      simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h31] at hgt
      rw [← h31'] at hgt
      have hbig := hcmp.1.1 hgt
      exact bw_split O (W.keep hkp') hk1 hk hmem hcy hbig hpred hvals.1 hvals.2.1 hvals.2.2
        (by simp only [upd_apply, ite_true]; rw [BitVec.toNat_sub, hszv, h14]; omega)
    · simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h31] at hle
      refine st_800049e4 O.live (fun hneg => ?_) (fun hnn => ?_)
      · -- too small: on to the previous member
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hneg
        have hsm' : sz < nb := by
          have := hcmp.2; rw [show ((0#64 : BitVec 64)).toInt = 0 from rfl] at this hneg; omega
        refine ih (cya :: post) _ (by rw [hmem]) (fun z hz sz' hz' => ?_) hkp' hvals.2.1
        rcases List.mem_cons.mp hz with rfl | hz
        · obtain rfl : sz' = sz := by
            have := HH.chunk_eq hz' hcy rfl; simp at this; exact this
          exact hsm'
        · exact hsm z hz sz' hz'
      · -- a fit: take
        simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false] at hnn
        have hfit : nb ≤ sz := hcmp.2.1 (by rw [show ((0#64 : BitVec 64)).toInt = 0 from rfl] at hnn ⊢; omega)
        exact bw_take O (W.keep hkp') hk1 hk hmem hcy hfit hpred hvals.1 hvals.2.1 hvals.2.2

end VsaIris.VsaHeap
