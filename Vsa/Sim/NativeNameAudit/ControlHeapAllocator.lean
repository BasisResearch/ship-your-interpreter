import Vsa.Sim.NativeNameAudit.ControlLedger

/-! The heap control's dlmalloc heap: eight in-use chunks from `_end` to the
top chunk, empty bins, and room for the program's terminating derivations. -/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Machine

namespace Vsa.Sim.NativeNameAudit.Control
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance Vsa.Sim.DlHeap
open Vsa.Sim.RuntimeOwnership Vsa.While.LoadedOutputAlias

/-- Words written by the small log. -/
local macro "small_read" : tactic =>
  `(tactic| (simp only [read32, read64, readLE, smallLookup]; decide +kernel))

/-- Every chunk from `_end` to the top chunk. -/
def heapChunks : List Chunk :=
  [⟨0x8001c170, 0xfe3e80, true⟩, ⟨0x80fffff0, 0x40, true⟩, ⟨0x81000030, 0x50, true⟩,
   ⟨0x81000080, 0x70, true⟩, ⟨0x810000f0, 0xd0, true⟩, ⟨0x810001c0, 0x80, true⟩,
   ⟨0x81000240, 0xfffdb0, true⟩, ⟨0x81fffff0, 0x210, true⟩]

/-- One in-use chunk whose header is `size + 1`, followed by a header with
`PREV_INUSE` set. -/
theorem walk_step {m : Mem} {p top size h' : Nat} {cs : List Chunk}
    (hh : read64 m (p + 8) = some (size + 1)) (hs : size % 16 = 0) (hmin : 32 ≤ size)
    (hn : read64 m (p + size + 8) = some h') (hbit : h' % 2 = 1)
    (rest : ChunkWalk m (p + size) top cs) :
    ChunkWalk m p top (⟨p, size, true⟩ :: cs) := by
  have hcs : chunkSize (size + 1) = size := by unfold chunkSize; omega
  have hpi : prevInuse h' = true := by unfold prevInuse; simp [hbit]
  have h := ChunkWalk.chunk (m := m) (top := top) (cs := cs) hh (by omega)
    (by rw [hcs]; exact hmin) (by rw [hcs]; exact hs) (by rw [hcs]; exact hn)
    (by rw [hcs]; exact rest)
  rw [hcs, hpi] at h
  exact h

theorem heapWalk : ChunkWalk heapMem heapStart heapTop heapChunks :=
  walk_step (h' := 0x41) (by small_read) (by decide) (by decide) (by small_read) (by decide) <|
  walk_step (h' := 0x51) (by small_read) (by decide) (by decide) (by small_read) (by decide) <|
  walk_step (h' := 0x71) (by small_read) (by decide) (by decide) (by small_read) (by decide) <|
  walk_step (h' := 0xd1) (by small_read) (by decide) (by decide) (by small_read) (by decide) <|
  walk_step (h' := 0x81) (by small_read) (by decide) (by decide) (by small_read) (by decide) <|
  walk_step (h' := 0xfffdb1) (by small_read) (by decide) (by decide) (by small_read)
    (by decide) <|
  walk_step (h' := 0x211) (by small_read) (by decide) (by decide) (by small_read) (by decide) <|
  walk_step (h' := 0xe01) (by small_read) (by decide) (by decide) (by small_read) (by decide) <|
  .top

theorem all_inuse : ∀ c ∈ heapChunks, c.inuse = true := by decide

theorem realloc_extent {e : Extent} {fa : Nat}
    (h : Allocated alloc (.names fa) e.1 e.2 ∨ Allocated alloc (.values fa) e.1 e.2) :
    e = (0x81000040, 64) ∨ e = (0x81000100, 192) := by
  obtain ⟨p, n⟩ := e
  rcases h with h | h
  · by_cases hf : fa = 0
    · subst fa
      have he : (0x81000040, 64) = (p, n) := by
        simpa [Allocated, alloc, Allocations.insert] using h
      exact Or.inl he.symm
    · simp [Allocated, alloc, Allocations.insert, hf] at h
  · by_cases hf : fa = 0
    · subst fa
      have he : (0x81000100, 192) = (p, n) := by
        simpa [Allocated, alloc, Allocations.insert] using h
      exact Or.inr he.symm
    · simp [Allocated, alloc, Allocations.insert, hf] at h

theorem heapAt : HeapAt heapMem exts (ReallocExtent alloc) heapTop heapBrk heapChunks
    (fun _ => []) where
  sbrk_base := by small_read
  brk := by small_read
  brk_le := by decide
  top_ptr := heapTopPtr
  top_le := by decide
  top_size := by decide
  top_header := by small_read
  top_pad := heapTopPad
  max_sbrked := by rw [heapMaxSbrked]; rfl
  mallinfo := by rw [heapMallinfo]; rfl
  first_prev := by
    rw [show read64 heapMem (heapStart + 8) = some 0xfe3e81 by small_read]
    rfl
  walk := heapWalk
  coalesced := by
    intro i hi
    left
    exact all_inuse _ (List.getElem_mem (by omega))
  footer := by
    intro c hc hf
    rw [all_inuse c hc] at hf
    cases hf
  bins_list := fun i h0 h1 =>
    ⟨binAt i, (heapBins i h0 h1).1, BinChain.close (heapBins i h0 h1).2⟩
  bins_nodup := fun _ => List.nodup_nil
  bin_free := by
    intro i q _ _ hq
    cases hq
  free_binned := by
    intro c hc hf
    rw [all_inuse c hc] at hf
    cases hf
  remainder := Nat.zero_le 1
  binblocks_present := by rw [heapBinblocks]; rfl
  binblocks := fun _ _ _ _ _ h => (h rfl).elim
  live := by decide
  exact := by
    intro e _ hr
    obtain ⟨fa, hr⟩ := hr
    rcases realloc_extent hr with rfl | rfl <;> decide

/-- Each `println()` statement allocates nothing and keeps the store. -/
theorem printLine_cost {st st' : Vsa.While.St} {status : Status} {n : Nat}
    (hs : st.store = initSt.store) (h : ExecSCost st 0 0 printLine st' status n) :
    n = 0 ∧ st'.store = initSt.store ∧ status = .normal := by
  cases h with
  | expr _ _ _ _ _ _ _ he =>
    cases he with
    | call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf _ ha hc =>
      cases hf with
      | var _ _ _ _ _ hget =>
        cases ha with
        | nil =>
          rw [hs] at hget
          have hfv := Option.some.inj
            (hget.symm.trans (by decide : initSt.store.get? 0 "println" = some (.native .println)))
          subst hfv
          cases hc with
          | println => exact ⟨rfl, hs, rfl⟩

theorem program_cost {st' : Vsa.While.St} {n : Nat}
    (h : ExecSeqCost initSt 0 0 nativeNameProgram st' .normal n) : n = 0 := by
  cases h with
  | consNormal _ _ _ _ _ _ _ _ n1 n2 h1 hrest =>
    obtain ⟨hn1, hs1, -⟩ := printLine_cost rfl h1
    cases hrest with
    | consNormal _ _ _ _ _ _ _ _ m1 m2 h2 hnil =>
      obtain ⟨hm1, -, -⟩ := printLine_cost hs1 h2
      cases hnil with
      | nil => omega
    | consAbrupt _ _ _ _ _ _ _ _ _ hne => exact absurd rfl hne
  | consAbrupt _ _ _ _ _ _ _ _ _ hne => exact absurd rfl hne

theorem heapCapacity : ∀ p : Program, ProgramRepr heapMem 0x82000000 2 p →
    ∀ st' n, ExecSeqCost initSt 0 0 p st' .normal n →
      2 * n + extendSlack ≤ heapEnd - heapTop := by
  intro p hp st' n hn
  rw [heapAstReads.program_unique hp] at hn
  rw [program_cost hn]
  decide

theorem heapAllocator :
    InitialAllocator heapMem exts (ReallocExtent alloc) 0x82000000 2 :=
  ⟨heapTop, heapBrk, heapChunks, fun _ => [], heapAt, heapCapacity⟩

#print axioms heapWalk
#print axioms heapAt
#print axioms program_cost
#print axioms heapAllocator

end Vsa.Sim.NativeNameAudit.Control
