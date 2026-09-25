import Vsa.Sim.Boot.Store
import Vsa.Sim.DlHeap

/-!
# The dlmalloc heap shape from a byte view

`heapCheck` decides every field of `DlHeap.HeapAt` over a partial byte view,
for generated witnesses: the chunk walk from `_end` to the top chunk, the bin
lists (`binsL`, one list per bin), the live extents and the exact (realloc)
extents. `heapAt_of_check` turns a passing check into `HeapAt`.
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr Vsa.Sim.DlHeap

/-- `read64` over a view. -/
abbrev r64 (v : Nat → Option (BitVec 8)) (a : Nat) : Option Nat := readLEv v a 8

theorem PartialView.read64 {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v)
    {a x : Nat} (hr : r64 v a = some x) : Vsa.MemRepr.read64 m a = some x := h.readLE hr

/-! ## The chunk walk -/

/-- The walk from `p` to `top` is `cs`. -/
def walkCheck (v : Nat → Option (BitVec 8)) (top : Nat) : Nat → List Chunk → Bool
  | p, [] => p == top
  | p, c :: cs =>
    c.addr == p &&
    (match r64 v (p + 8), r64 v (p + c.size + 8) with
     | some h, some h' =>
       decide (h % 4 < 2) && chunkSize h == c.size && decide (32 ≤ c.size) &&
       c.size % 16 == 0 && prevInuse h' == c.inuse
     | _, _ => false) &&
    walkCheck v top (p + c.size) cs

theorem walkCheck_sound {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v)
    {top : Nat} : ∀ {cs p}, walkCheck v top p cs = true → ChunkWalk m p top cs := by
  intro cs
  induction cs with
  | nil =>
    intro p hc
    simp only [walkCheck, beq_iff_eq] at hc
    subst hc
    exact .top
  | cons c cs ih =>
    intro p hc
    obtain ⟨addr, size, inuse⟩ := c
    simp only [walkCheck, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨rfl, hr⟩, hrest⟩ := hc
    cases h1 : r64 v (addr + 8) with
    | none => rw [h1] at hr; cases hr
    | some hd =>
      cases h2 : r64 v (addr + size + 8) with
      | none => rw [h1, h2] at hr; cases hr
      | some hd' =>
        rw [h1, h2] at hr
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
        obtain ⟨⟨⟨⟨hlow, hsz⟩, hmin⟩, hal⟩, hin⟩ := hr
        subst hsz hin
        exact .chunk (h.read64 h1) hlow hmin (by omega) (h.read64 h2) (ih hrest)

/-! ## Bins -/

/-- Bin `b`'s circular list from `q` (predecessor `prev`) is `qs`. -/
def chainCheck (v : Nat → Option (BitVec 8)) (b : Nat) : Nat → Nat → List Nat → Bool
  | q, prev, [] => q == b && r64 v (b + 24) == some prev
  | q, prev, q' :: qs =>
    q' == q && q != b && r64 v (q + 24) == some prev &&
    (match r64 v (q + 16) with
     | some nxt => chainCheck v b nxt q qs
     | none => false)

theorem chainCheck_sound {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v)
    {b : Nat} : ∀ {qs q prev}, chainCheck v b q prev qs = true → BinChain m b q prev qs := by
  intro qs
  induction qs with
  | nil =>
    intro q prev hc
    simp only [chainCheck, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, hp⟩ := hc
    exact .close (h.read64 hp)
  | cons q' qs ih =>
    intro q prev hc
    simp only [chainCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨rfl, hne⟩, hp⟩, hn⟩ := hc
    cases hx : r64 v (q' + 16) with
    | none => rw [hx] at hn; cases hn
    | some nxt =>
      rw [hx] at hn
      exact .link hne (h.read64 hp) (h.read64 hx) (ih hn)

/-- Bin `i`'s list. -/
def binList (v : Nat → Option (BitVec 8)) (i : Nat) (qs : List Nat) : Bool :=
  match r64 v (binAt i + 16) with
  | some first => chainCheck v (binAt i) first (binAt i) qs
  | none => false

theorem binList_sound {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v)
    {i : Nat} {qs : List Nat} (hc : binList v i qs = true) : BinList m i qs := by
  unfold binList at hc
  cases hf : r64 v (binAt i + 16) with
  | none => rw [hf] at hc; cases hc
  | some first =>
    rw [hf] at hc
    exact ⟨first, h.read64 hf, chainCheck_sound h hc⟩

/-- Bin lists, one per bin index (missing indices are empty). -/
def binsOf (L : List (List Nat)) (i : Nat) : List Nat := L.getD i []

/-! ## The whole shape -/

/-- Consecutive chunks are never both free. -/
def coalescedCheck : List Chunk → Bool
  | c :: d :: cs => (c.inuse || d.inuse) && coalescedCheck (d :: cs)
  | _ => true

theorem coalescedCheck_sound : ∀ {cs : List Chunk}, coalescedCheck cs = true →
    ∀ i (hi : i + 1 < cs.length), cs[i].inuse = true ∨ cs[i + 1].inuse = true := by
  intro cs
  induction cs with
  | nil => intro _ i hi; simp at hi
  | cons c cs ih =>
    intro hc i hi
    cases cs with
    | nil => simp at hi
    | cons d cs =>
      simp only [coalescedCheck, Bool.and_eq_true, Bool.or_eq_true] at hc
      cases i with
      | zero => simpa using hc.1
      | succ i =>
        have := ih hc.2 i (by simp at hi ⊢; omega)
        simpa using this

/-- The bin indices `1 … 127`. -/
def binIdxs : List Nat := (List.range 127).map (· + 1)

theorem mem_binIdxs {i : Nat} (h0 : 0 < i) (h1 : i < numBins) : i ∈ binIdxs := by
  unfold binIdxs numBins at *
  simp only [List.mem_map, List.mem_range]
  exact ⟨i - 1, by omega, by omega⟩

/-- Every field of `HeapAt` over the view. -/
def heapCheck (v : Nat → Option (BitVec 8)) (exts exact : List (Nat × Nat)) (top brkv : Nat)
    (chunks : List Chunk) (L : List (List Nat)) : Bool :=
  r64 v sbrkBaseAddr == some heapStart &&
  r64 v brkAddr == some brkv &&
  decide (brkv ≤ heapEnd) &&
  r64 v topAddr == some top &&
  decide (top ≤ brkv) &&
  (brkv - top) % 16 == 0 &&
  r64 v (top + 8) == some (brkv - top + 1) &&
  r64 v topPadAddr == some 0 &&
  (r64 v maxSbrkedAddr).isSome &&
  (r64 v mallinfoAddr).isSome &&
  (r64 v (heapStart + 8)).any (fun h => h % 2 == 1) &&
  walkCheck v top heapStart chunks &&
  coalescedCheck chunks &&
  chunks.all (fun c => c.inuse || r64 v (c.addr + c.size) == some c.size) &&
  binIdxs.all (fun i => binList v i (binsOf L i)) &&
  L.all (fun l => l.Nodup) &&
  (binsOf L 0).isEmpty &&
  binIdxs.all (fun i => (binsOf L i).all fun q =>
    chunks.any fun c => c.addr == q && !c.inuse && (i ≤ 1 || binIndex c.size == i)) &&
  chunks.all (fun c => c.inuse ||
    ((binIdxs.filter fun i => (binsOf L i).contains c.addr).length == 1)) &&
  decide ((binsOf L 1).length ≤ 1) &&
  (match r64 v binblocksAddr with
   | some bb => binIdxs.all fun i => i ≤ 1 || (binsOf L i).isEmpty || bb / 2 ^ (i / 4) % 2 == 1
   | none => false) &&
  exts.all (fun e => chunks.any fun c =>
    c.inuse && decide (c.addr + 16 ≤ e.1) && decide (e.1 + e.2 ≤ c.addr + c.size + 8)) &&
  exact.all (fun e => chunks.any fun c =>
    c.inuse && c.addr + 16 == e.1 && decide (e.2 + 8 ≤ c.size))

/-- A passing `heapCheck` is the heap shape; realloc extents must be among `exact`. -/
theorem heapAt_of_check {m : Mem} {v : Nat → Option (BitVec 8)} (h : PartialView m v)
    {exts exact : List (Nat × Nat)} {reallocs : Nat × Nat → Prop} {top brkv : Nat}
    {chunks : List Chunk} {L : List (List Nat)}
    (hc : heapCheck v exts exact top brkv chunks L = true)
    (hr : ∀ e ∈ exts, reallocs e → e ∈ exact) :
    HeapAt m exts reallocs top brkv chunks (binsOf L) := by
  simp only [heapCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsbrk, hbrk⟩, hbrkle⟩, htop⟩, htople⟩, htopsz⟩, htoph⟩,
    hpad⟩, hmax⟩, hmall⟩, hfirst⟩, hwalk⟩, hcoal⟩, hfoot⟩, hbins⟩, hnodup⟩, hbin0⟩,
    hfree⟩, hbinned⟩, hrem⟩, hbb⟩, hlive⟩, hexact⟩ := hc
  have hsome : ∀ {a}, (r64 v a).isSome = true → (Vsa.MemRepr.read64 m a).isSome = true := by
    intro a ha
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp ha
    rw [h.read64 hx]; rfl
  refine
    { sbrk_base := h.read64 hsbrk
      brk := h.read64 hbrk
      brk_le := hbrkle
      top_ptr := h.read64 htop
      top_le := htople
      top_size := htopsz
      top_header := h.read64 htoph
      top_pad := h.read64 hpad
      max_sbrked := hsome hmax
      mallinfo := hsome hmall
      first_prev := ?_
      walk := walkCheck_sound h hwalk
      coalesced := coalescedCheck_sound hcoal
      footer := ?_
      bins_list := fun i h0 h1 =>
        binList_sound h (List.all_eq_true.mp hbins i (mem_binIdxs h0 h1))
      bins_nodup := ?_
      bin_free := ?_
      free_binned := ?_
      remainder := hrem
      binblocks_present := ?_
      binblocks := ?_
      live := ?_
      exact := ?_ }
  · cases hx : r64 v (heapStart + 8) with
    | none => rw [hx] at hfirst; cases hfirst
    | some x => rw [hx] at hfirst; rw [h.read64 hx]; exact hfirst
  · intro c hc hfree
    have := List.all_eq_true.mp hfoot c hc
    simp only [hfree, Bool.false_or, beq_iff_eq] at this
    exact h.read64 this
  · intro i
    unfold binsOf
    rw [List.getD_eq_getElem?_getD]
    cases hi : L[i]? with
    | none => exact List.nodup_nil
    | some l =>
      have := List.all_eq_true.mp hnodup l (List.mem_of_getElem? hi)
      simpa using this
  · intro i q h0 h1 hq
    have := List.all_eq_true.mp (List.all_eq_true.mp hfree i (mem_binIdxs h0 h1)) q hq
    obtain ⟨c, hc, hcq⟩ := List.any_eq_true.mp this
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true,
      decide_eq_true_eq] at hcq
    obtain ⟨⟨haddr, hin⟩, hidx⟩ := hcq
    exact ⟨c, hc, haddr, hin, fun h1i => hidx.resolve_left (by omega)⟩
  · intro c hc hfree
    have := List.all_eq_true.mp hbinned c hc
    simp only [hfree, Bool.false_or, beq_iff_eq] at this
    obtain ⟨i, hi⟩ := List.length_eq_one_iff.mp this
    have hmem : i ∈ binIdxs.filter fun i => (binsOf L i).contains c.addr := by
      rw [hi]; exact List.mem_singleton_self i
    rw [List.mem_filter] at hmem
    obtain ⟨hib, hic⟩ := hmem
    have hib' := hib
    unfold binIdxs at hib'
    simp only [List.mem_map, List.mem_range] at hib'
    obtain ⟨k, hk, rfl⟩ := hib'
    refine ⟨k + 1, by omega, by unfold numBins; omega, by simpa using hic, ?_⟩
    intro j hj0 hj1 hj
    have hjm : j ∈ binIdxs.filter fun i => (binsOf L i).contains c.addr := by
      rw [List.mem_filter]
      exact ⟨mem_binIdxs hj0 hj1, by simpa using hj⟩
    rw [hi] at hjm
    exact List.mem_singleton.mp hjm
  · cases hx : r64 v binblocksAddr with
    | none => rw [hx] at hbb; cases hbb
    | some x => rw [h.read64 hx]; rfl
  · intro bb hbbr i h1 h2 hne
    cases hx : r64 v binblocksAddr with
    | none => rw [hx] at hbb; cases hbb
    | some x =>
      rw [hx] at hbb
      have hxb : x = bb := Option.some.inj ((h.read64 hx).symm.trans hbbr)
      subst hxb
      have := List.all_eq_true.mp hbb i (mem_binIdxs (by omega) h2)
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff, beq_iff_eq] at this
      rcases this with (h' | h') | h'
      · omega
      · exact absurd h' hne
      · exact h'
  · intro e he
    obtain ⟨c, hc, hce⟩ := List.any_eq_true.mp (List.all_eq_true.mp hlive e he)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hce
    exact ⟨c, hc, hce.1.1, hce.1.2, hce.2⟩
  · intro e he hre
    obtain ⟨c, hc, hce⟩ := List.any_eq_true.mp (List.all_eq_true.mp hexact e (hr e he hre))
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hce
    exact ⟨c, hc, hce.1.1, hce.1.2, hce.2⟩

end Vsa.Sim.Boot
