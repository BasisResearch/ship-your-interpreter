import Vsa.Sim.NativeNameAudit.ControlHeapAllocator
import VsaIris.Vsa.HeapShape

/-!
# The eb73d8c control heap against the live-relative frame

`PROOF_CLOSURE_PLAN.md` §2 records the obstruction to `MallocContract`: on the
admitted control heap (top chunk `0x82000200`, `Control.heapMem`),
`malloc(32)` writes the new top header at `0x82000238`, and `malloc(64)` from
the same state returns `[0x82000210, 0x82000250)`, which contains it.
`VsaIris.no_fixed_privFoot` proves no state-independent footprint frames both.

This module checks the concrete case against `vsaLayout`, at the actual
control memory rather than an abstract layout:

* `control_shape`: the control heap has the Iris heap shape, with the eight
  in-use chunk payloads as its live blocks (`controlBlocks`), and every VSA
  ledger extent lies in one of them (`control_exts_covered`);
* `m32`/`m64`: the memories after `_malloc_r`'s top-split path
  (`experiments/disasm.txt`, `0x80004b7c`-`0x80004bac`: store the new top
  pointer, the victim's header with `PREV_INUSE`, and the remainder's header)
  for requests 32 and 64;
* `live_relative_frame_admits_both`: both calls write only `vsaFoot
  controlBlocks`, both post-states have the block-heap shape with the returned
  block live, the 64-byte block is fresh, and it contains the byte the 32-byte
  call wrote. So the live-relative frame accepts exactly the two behaviours
  the fixed `privFoot` cannot.

The post-state memories are computed from the disassembly, not from a run of
the Sail model: this is a consistency check of the specification relation,
not a proof about `_malloc_r`.
-/

namespace VsaIris.VsaHeap.Control

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap Vsa.Sim.NativeNameAudit.Control

/-- The live blocks of the control heap: every in-use chunk payload. -/
def controlBlocks : List (Nat × Nat) := inuseBlocks heapChunks

theorem controlBlocks_eq : controlBlocks =
    [(0x8001c180, 0xfe3e78), (0x81000000, 0x38), (0x81000040, 0x48), (0x81000090, 0x68),
     (0x81000100, 0xc8), (0x810001d0, 0x78), (0x81000250, 0xfffda8),
     (0x82000000, 0x208)] := by
  decide

theorem control_blockHeapAt :
    BlockHeapAt heapMem controlBlocks heapTop heapBrk heapChunks (fun _ => []) :=
  (blockHeapAt_of_heapAt heapAt (by decide)).1

/-- Every VSA ledger extent of the control lies in a live block. -/
theorem control_exts_covered :
    ∀ e ∈ exts, ∃ b ∈ controlBlocks, ∀ a, InExt e a → InExt b a :=
  (blockHeapAt_of_heapAt heapAt (by decide)).2

/-- The control memory's total byte image (`readByte`). -/
def img0 (a : Nat) : BitVec 8 := (heapMem[a]?).getD 0

theorem foot_ram {H : List (Nat × Nat)} {a : Nat} (h : vsaFoot H a) :
    0x80000000 ≤ a ∧ a < 0x88000000 := by
  rcases h with hg | ⟨h1, h2, _⟩
  · unfold allocGlobal InRange at hg; omega
  · unfold heapStart at h1; unfold heapEnd at h2; omega

/-- **The control heap has the Iris heap shape**, read off its owned image. -/
theorem control_shape : vsaLayout.Shape img0 controlBlocks :=
  (imgShape_iff (imgOn_of_getD
    (fun a ha => by
      obtain ⟨b, hb⟩ := heap_present a (foot_ram ha).1 (foot_ram ha).2
      rw [hb]; rfl)
    (fun _ _ => rfl))).2 ⟨_, _, _, _, control_blockHeapAt⟩

/-! ## The two calls' post-states -/

/-- `malloc(32)`: an 48-byte victim at the old top; the new top at
`0x82000230`, whose header is at `0x82000238`. -/
def w32 : List WEntry :=
  [(topAddr, 8, 0x82000230#64), (0x82000208, 8, 0x31#64), (0x82000238, 8, 0xdd1#64)]

/-- `malloc(64)`: an 80-byte victim at the old top; the new top at
`0x82000250`. -/
def w64 : List WEntry :=
  [(topAddr, 8, 0x82000250#64), (0x82000208, 8, 0x51#64), (0x82000258, 8, 0xdb1#64)]

def m32 : Mem := writeLog heapMem w32
def m64 : Mem := writeLog heapMem w64

def H32 : List (Nat × Nat) := (0x82000210, 32) :: controlBlocks
def H64 : List (Nat × Nat) := (0x82000210, 64) :: controlBlocks

def chunks32 : List Chunk := heapChunks ++ [⟨0x82000200, 0x30, true⟩]
def chunks64 : List Chunk := heapChunks ++ [⟨0x82000200, 0x50, true⟩]

theorem lookup_post (w : List WEntry) (a : Nat) :
    (writeLog heapMem w)[a]? = logRead (fun k => logRead (fun k' => avMem[k']?) smallLog k) w a := by
  rw [writeLog_getElem?_logRead]
  congr 1
  funext k
  exact smallLookup k

/-- Words the small log or the post log writes. -/
local macro "post_read" : tactic =>
  `(tactic| (simp only [m32, m64, w32, w64, read64, readLE, lookup_post]; decide +kernel))

theorem read64_off {m : Mem} {w : List WEntry} {a : Nat} (h : ∀ k, k < 8 → OutL w (a + k)) :
    read64 (writeLog m w) a = read64 m a :=
  (read64_agreeP (P := OutL w) (fun k hk => (writeLog_out m w k hk).symm) h).symm

theorem outL3 {e1 e2 e3 : WEntry} {k : Nat} (h1 : k < e1.1 ∨ e1.1 + e1.2.1 ≤ k)
    (h2 : k < e2.1 ∨ e2.1 + e2.2.1 ≤ k) (h3 : k < e3.1 ∨ e3.1 + e3.2.1 ≤ k) :
    OutL [e1, e2, e3] k := ⟨h1, h2, h3, trivial⟩

/-- A global the post logs do not touch reads as before. -/
theorem read64_global {w : List WEntry} (hw : w = w32 ∨ w = w64) {a : Nat}
    (ha : topAddr + 8 ≤ a ∧ a + 8 ≤ 0x80000000 + 0x1000000 ∨ a + 8 ≤ topAddr) :
    read64 (writeLog heapMem w) a = read64 heapMem a := by
  simp only [topAddr, avAddr] at ha
  refine read64_off fun k hk => ?_
  rcases hw with rfl | rfl <;>
    exact outL3 (by simp only [topAddr, avAddr]; omega) (by simp only; omega)
      (by simp only; omega)

theorem bins_post {w : List WEntry} (hw : w = w32 ∨ w = w64) (i : Nat) (h0 : 0 < i)
    (hi : i < numBins) : BinList (writeLog heapMem w) i [] := by
  have hb := heapBins i h0 hi
  have hlo : topAddr + 8 ≤ binAt i + 16 := by
    simp only [topAddr, binAt, avAddr]; omega
  have hhi : binAt i + 24 + 8 ≤ 0x80000000 + 0x1000000 := by
    simp only [binAt, avAddr]; unfold numBins at hi; omega
  refine ⟨binAt i, ?_, BinChain.close ?_⟩
  · rw [read64_global hw (.inl ⟨hlo, by omega⟩)]; exact hb.1
  · rw [read64_global hw (.inl ⟨by omega, hhi⟩)]; exact hb.2

theorem walk32 : ChunkWalk m32 heapStart 0x82000230 chunks32 :=
  walk_step (h' := 0x41) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0x51) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0x71) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0xd1) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0x81) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0xfffdb1) (by post_read) (by decide) (by decide) (by post_read)
    (by decide) <|
  walk_step (h' := 0x211) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0x31) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0xdd1) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  .top

theorem walk64 : ChunkWalk m64 heapStart 0x82000250 chunks64 :=
  walk_step (h' := 0x41) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0x51) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0x71) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0xd1) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0x81) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0xfffdb1) (by post_read) (by decide) (by decide) (by post_read)
    (by decide) <|
  walk_step (h' := 0x211) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0x51) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  walk_step (h' := 0xdb1) (by post_read) (by decide) (by decide) (by post_read) (by decide) <|
  .top

theorem inuse32 : ∀ c ∈ chunks32, c.inuse = true := by decide
theorem inuse64 : ∀ c ∈ chunks64, c.inuse = true := by decide

/-- The block-heap shape after `malloc(32)`, with its block live. -/
theorem post32 : BlockHeapAt m32 H32 0x82000230 heapBrk chunks32 (fun _ => []) where
  heap :=
    { sbrk_base := by rw [m32, read64_global (.inl rfl) (by simp only [sbrkBaseAddr, topAddr, avAddr]; omega)]; exact heapAt.sbrk_base
      brk := by rw [m32, read64_global (.inl rfl) (by simp only [brkAddr, topAddr, avAddr]; omega)]; exact heapAt.brk
      brk_le := by decide
      top_ptr := by post_read
      top_le := by decide
      top_size := by decide
      top_header := by post_read
      top_pad := by rw [m32, read64_global (.inl rfl) (by simp only [topPadAddr, topAddr, avAddr]; omega)]; exact heapTopPad
      max_sbrked := by rw [m32, read64_global (.inl rfl) (by simp only [maxSbrkedAddr, topAddr, avAddr]; omega), heapMaxSbrked]; rfl
      mallinfo := by rw [m32, read64_global (.inl rfl) (by simp only [mallinfoAddr, topAddr, avAddr]; omega), heapMallinfo]; rfl
      first_prev := by
        rw [show read64 m32 (heapStart + 8) = some 0xfe3e81 by post_read]
        rfl
      walk := walk32
      coalesced := by
        intro i hi
        left
        exact inuse32 _ (List.getElem_mem (by omega))
      footer := by
        intro c hc hf
        rw [inuse32 c hc] at hf
        cases hf
      bins_list := fun i h0 h1 => bins_post (.inl rfl) i h0 h1
      bins_nodup := fun _ => List.nodup_nil
      bin_free := by
        intro i q _ _ hq
        cases hq
      free_binned := by
        intro c hc hf
        rw [inuse32 c hc] at hf
        cases hf
      remainder := Nat.zero_le 1
      binblocks_present := by
        rw [m32, read64_global (.inl rfl) (.inr (by simp only [binblocksAddr, topAddr, avAddr]; omega)), heapBinblocks]; rfl
      binblocks := fun _ _ _ _ _ h => (h rfl).elim
      live := by decide
      exact := by
        intro e he _
        revert e
        decide }
  top_room := by decide

/-- The block-heap shape after `malloc(64)`, with its block live. -/
theorem post64 : BlockHeapAt m64 H64 0x82000250 heapBrk chunks64 (fun _ => []) where
  heap :=
    { sbrk_base := by rw [m64, read64_global (.inr rfl) (by simp only [sbrkBaseAddr, topAddr, avAddr]; omega)]; exact heapAt.sbrk_base
      brk := by rw [m64, read64_global (.inr rfl) (by simp only [brkAddr, topAddr, avAddr]; omega)]; exact heapAt.brk
      brk_le := by decide
      top_ptr := by post_read
      top_le := by decide
      top_size := by decide
      top_header := by post_read
      top_pad := by rw [m64, read64_global (.inr rfl) (by simp only [topPadAddr, topAddr, avAddr]; omega)]; exact heapTopPad
      max_sbrked := by rw [m64, read64_global (.inr rfl) (by simp only [maxSbrkedAddr, topAddr, avAddr]; omega), heapMaxSbrked]; rfl
      mallinfo := by rw [m64, read64_global (.inr rfl) (by simp only [mallinfoAddr, topAddr, avAddr]; omega), heapMallinfo]; rfl
      first_prev := by
        rw [show read64 m64 (heapStart + 8) = some 0xfe3e81 by post_read]
        rfl
      walk := walk64
      coalesced := by
        intro i hi
        left
        exact inuse64 _ (List.getElem_mem (by omega))
      footer := by
        intro c hc hf
        rw [inuse64 c hc] at hf
        cases hf
      bins_list := fun i h0 h1 => bins_post (.inr rfl) i h0 h1
      bins_nodup := fun _ => List.nodup_nil
      bin_free := by
        intro i q _ _ hq
        cases hq
      free_binned := by
        intro c hc hf
        rw [inuse64 c hc] at hf
        cases hf
      remainder := Nat.zero_le 1
      binblocks_present := by
        rw [m64, read64_global (.inr rfl) (.inr (by simp only [binblocksAddr, topAddr, avAddr]; omega)), heapBinblocks]; rfl
      binblocks := fun _ _ _ _ _ h => (h rfl).elim
      live := by decide
      exact := by
        intro e he _
        revert e
        decide }
  top_room := by decide

/-- Bytes a post log writes are allocator footprint at the entry blocks. -/
theorem writes_in_foot {w : List WEntry} (hw : w = w32 ∨ w = w64) (a : Nat)
    (ha : ¬ OutL w a) : vsaFoot controlBlocks a := by
  have hcases : (topAddr ≤ a ∧ a < topAddr + 8) ∨ (0x82000208 ≤ a ∧ a < 0x82000210) ∨
      (0x82000238 ≤ a ∧ a < 0x82000260) := by
    rcases hw with rfl | rfl <;>
    · simp only [w32, w64, OutL, and_true] at ha
      simp only [topAddr, avAddr] at ha ⊢
      omega
  rcases hcases with h | h | h
  · simp only [topAddr, avAddr] at h
    exact .inl (.inl ⟨by omega, by omega⟩)
  all_goals
    refine .inr ⟨by unfold heapStart; omega, by unfold heapEnd; omega, fun e he hin => ?_⟩
    rw [controlBlocks_eq] at he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    unfold InExt at hin
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at hin <;> omega

/-- Each call changes only the allocator's footprint at the entry blocks. -/
theorem frame_post {w : List WEntry} (hw : w = w32 ∨ w = w64) :
    AgreeP (fun a => ¬ vsaFoot controlBlocks a) heapMem (writeLog heapMem w) := by
  intro a ha
  by_cases ho : OutL w a
  · exact (writeLog_out heapMem w a ho).symm
  · exact absurd (writes_in_foot hw a ho) ha

/-- The 64-byte block is fresh at the control's live blocks. -/
theorem fresh64 : FreshBlock vsaLayout controlBlocks 0x82000210 64 := by
  refine ⟨by decide, by decide, by decide, fun e he a ha hin => ?_⟩
  change e ∈ controlBlocks at he
  rw [controlBlocks_eq] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  unfold InExt at ha hin
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only at ha hin <;> omega

/-- The byte `malloc(32)` writes is the allocator's before the calls, and the
caller's after `malloc(64)`. -/
theorem byte_moves : heapFoot vsaLayout controlBlocks 0x82000238 ∧
    InExt (0x82000210, 64) 0x82000238 ∧ ¬ heapFoot vsaLayout H64 0x82000238 := by
  refine ⟨writes_in_foot (.inl rfl) _ ?_, by unfold InExt; decide, ?_⟩
  · simp only [w32, OutL, topAddr, avAddr]; omega
  · rintro (hg | ⟨_, _, h⟩)
    · unfold vsaLayout allocGlobal InRange at hg; simp only at hg; omega
    · exact h (0x82000210, 64) List.mem_cons_self (by unfold InExt; decide)

/-- **The live-relative frame admits both calls of the obstruction**, named
field by field. -/
structure ObstructionAdmitted : Prop where
  /-- The control heap has the Iris heap shape. -/
  shape : vsaLayout.Shape img0 controlBlocks
  /-- `malloc(32)` changes only the allocator's footprint... -/
  frame32 : AgreeP (fun a => ¬ heapFoot vsaLayout controlBlocks a) heapMem m32
  /-- ...lands in the block-heap shape with its block live... -/
  post32 : BlockHeap m32 H32
  /-- ...and writes the new top header at `0x82000238`. -/
  writes : read64 m32 0x82000238 = some 0xdd1
  /-- `malloc(64)` changes only the allocator's footprint... -/
  frame64 : AgreeP (fun a => ¬ heapFoot vsaLayout controlBlocks a) heapMem m64
  /-- ...lands in the block-heap shape with its block live... -/
  post64 : BlockHeap m64 H64
  /-- ...returns a fresh block... -/
  fresh : FreshBlock vsaLayout controlBlocks 0x82000210 64
  /-- ...that contains the byte `malloc(32)` writes, which then belongs to the
  caller, not the allocator. -/
  moves : heapFoot vsaLayout controlBlocks 0x82000238 ∧
    InExt (0x82000210, 64) 0x82000238 ∧ ¬ heapFoot vsaLayout H64 0x82000238

theorem live_relative_frame_admits_both : ObstructionAdmitted where
  shape := control_shape
  frame32 := frame_post (.inl rfl)
  post32 := ⟨_, _, _, _, post32⟩
  writes := by post_read
  frame64 := frame_post (.inr rfl)
  post64 := ⟨_, _, _, _, post64⟩
  fresh := fresh64
  moves := byte_moves

end VsaIris.VsaHeap.Control
