import Vsa.MemRepr
import Vsa.While.Cost

/-!
# The newlib dlmalloc heap at the interpreter boundary

The fixed binary links newlib's dlmalloc. `__malloc_av_` holds 128 bins; bin
`i` is addressed as a chunk at `avAddr + 16 * i`, so its `fd`/`bk` words sit at
`+16`/`+24`. Bin 0's `fd` word is the top-chunk pointer and its size word is
the `binblocks` bitmap. `_sbrk` (`c/src/htif.c`) grows the heap from `_end`
towards `__heap_end`, recording the break in `brk.0`.

`HeapAt` is the heap shape `_malloc_r` reads: a contiguous chunk walk from
`_end` to the top chunk, top ending at the break, coalesced free chunks with
footers, and every free chunk on exactly one well-formed bin list. Live
ledger extents are payloads of in-use chunks. `InitialAllocatorAt` adds the
per-program capacity: every terminating derivation's modeled allocation fits
below `__heap_end`.
-/

namespace Vsa.Sim.DlHeap

open Vsa.MemRepr Vsa.While

/-- `__malloc_av_`. -/
def avAddr : Nat := 0x8001ad10
/-- Bin 0's size word: the `binblocks` bitmap. -/
def binblocksAddr : Nat := avAddr + 8
/-- Bin 0's `fd` word: the top chunk. -/
def topAddr : Nat := avAddr + 16
def sbrkBaseAddr : Nat := 0x8001b960
def maxSbrkedAddr : Nat := 0x8001b9a0
def topPadAddr : Nat := 0x8001b9a8
/-- `brk.0` in `_sbrk`. -/
def brkAddr : Nat := 0x8001b990
def mallinfoAddr : Nat := 0x8001ba18
/-- `_end`: the first break `_sbrk` returns. -/
def heapStart : Nat := 0x8001c170
/-- `__heap_end`: `_sbrk` fails beyond it. -/
def heapEnd : Nat := 0x87800000
def numBins : Nat := 128

/-- Bin `i`, viewed as a chunk. -/
def binAt (i : Nat) : Nat := avAddr + 16 * i

/-- Chunk size: the header without `PREV_INUSE` and `IS_MMAPPED`. -/
def chunkSize (h : Nat) : Nat := h / 4 * 4

def prevInuse (h : Nat) : Bool := h % 2 == 1

/-- newlib's `bin_index` for a chunk size. -/
def binIndex (sz : Nat) : Nat :=
  if sz / 512 = 0 then sz / 8
  else if sz / 512 ≤ 4 then 56 + sz / 64
  else if sz / 512 ≤ 20 then 91 + sz / 512
  else if sz / 512 ≤ 84 then 110 + sz / 4096
  else if sz / 512 ≤ 340 then 119 + sz / 32768
  else if sz / 512 ≤ 1364 then 124 + sz / 262144
  else 126

/-- One chunk of the walk; `inuse` is the next header's `PREV_INUSE` bit. -/
structure Chunk where
  addr : Nat
  size : Nat
  inuse : Bool

/-- The contiguous chunks from `p` up to the top chunk `top`. -/
inductive ChunkWalk (m : Mem) : Nat → Nat → List Chunk → Prop where
  | top {p : Nat} : ChunkWalk m p p []
  | chunk {p top h h' : Nat} {cs : List Chunk} :
      read64 m (p + 8) = some h → h % 4 < 2 →
      32 ≤ chunkSize h → chunkSize h % 16 = 0 →
      read64 m (p + chunkSize h + 8) = some h' →
      ChunkWalk m (p + chunkSize h) top cs →
      ChunkWalk m p top (⟨p, chunkSize h, prevInuse h'⟩ :: cs)

/-- A bin's circular doubly-linked list, from `q` (predecessor `prev`) back to
the bin head `b`. -/
inductive BinChain (m : Mem) (b : Nat) : Nat → Nat → List Nat → Prop where
  | close {prev : Nat} : read64 m (b + 24) = some prev → BinChain m b b prev []
  | link {q prev nxt : Nat} {qs : List Nat} :
      q ≠ b → read64 m (q + 24) = some prev → read64 m (q + 16) = some nxt →
      BinChain m b nxt q qs → BinChain m b q prev (q :: qs)

/-- The chunks on bin `i`, in `fd` order. -/
def BinList (m : Mem) (i : Nat) (qs : List Nat) : Prop :=
  ∃ first, read64 m (binAt i + 16) = some first ∧
    BinChain m (binAt i) first (binAt i) qs

/-- The heap shape `_malloc_r` reads, at one memory. `reallocs` names the
live extents later passed to `realloc`/`free`; those are exact payloads. -/
structure HeapAt (m : Mem) (exts : List (Nat × Nat)) (reallocs : Nat × Nat → Prop)
    (top brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat) : Prop where
  sbrk_base : read64 m sbrkBaseAddr = some heapStart
  brk : read64 m brkAddr = some brkv
  brk_le : brkv ≤ heapEnd
  top_ptr : read64 m topAddr = some top
  top_le : top ≤ brkv
  top_size : (brkv - top) % 16 = 0
  /-- Top's size reaches the break; its predecessor is in use. -/
  top_header : read64 m (top + 8) = some (brkv - top + 1)
  top_pad : read64 m topPadAddr = some 0
  max_sbrked : (read64 m maxSbrkedAddr).isSome
  mallinfo : (read64 m mallinfoAddr).isSome
  /-- Nothing precedes the first chunk. -/
  first_prev : (read64 m (heapStart + 8)).any (fun h => h % 2 == 1)
  walk : ChunkWalk m heapStart top chunks
  coalesced : ∀ i (hi : i + 1 < chunks.length),
    chunks[i].inuse = true ∨ chunks[i + 1].inuse = true
  footer : ∀ c ∈ chunks, c.inuse = false → read64 m (c.addr + c.size) = some c.size
  bins_list : ∀ i, 0 < i → i < numBins → BinList m i (bins i)
  bins_nodup : ∀ i, (bins i).Nodup
  bin_free : ∀ i q, 0 < i → i < numBins → q ∈ bins i →
    ∃ c ∈ chunks, c.addr = q ∧ c.inuse = false ∧ (1 < i → binIndex c.size = i)
  free_binned : ∀ c ∈ chunks, c.inuse = false →
    ∃ i, 0 < i ∧ i < numBins ∧ c.addr ∈ bins i ∧
      ∀ j, 0 < j → j < numBins → c.addr ∈ bins j → j = i
  /-- The last-remainder bin holds at most one chunk. -/
  remainder : (bins 1).length ≤ 1
  binblocks_present : (read64 m binblocksAddr).isSome
  binblocks : ∀ bb, read64 m binblocksAddr = some bb →
    ∀ i, 1 < i → i < numBins → bins i ≠ [] → bb / 2 ^ (i / 4) % 2 = 1
  /-- Every live extent lies in an in-use chunk's usable payload. -/
  live : ∀ e ∈ exts, ∃ c ∈ chunks, c.inuse = true ∧
    c.addr + 16 ≤ e.1 ∧ e.1 + e.2 ≤ c.addr + c.size + 8
  /-- Reallocated extents are exactly an in-use chunk's payload. -/
  exact : ∀ e ∈ exts, reallocs e →
    ∃ c ∈ chunks, c.inuse = true ∧ c.addr + 16 = e.1 ∧ e.2 + 8 ≤ c.size

/-- Slack for `malloc_extend_top`: page rounding, its alignment correction,
and the minimum remainder. -/
def extendSlack : Nat := 8192 + 64

/-- The boundary allocator: the heap shape plus room for every terminating
derivation of the represented program. Each modeled charge is at least one
16-byte granule per request and `physSize` is at most twice it, so twice the
modeled cost bounds the chunk bytes requested. -/
structure InitialAllocatorAt (m : Mem) (exts : List (Nat × Nat))
    (reallocs : Nat × Nat → Prop) (stmts count : Nat)
    (top brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat) : Prop where
  heap : HeapAt m exts reallocs top brkv chunks bins
  capacity : ∀ p : Program, ProgramRepr m stmts count p →
    ∀ st' n, ExecSeqCost initSt 0 0 p st' .normal n →
      2 * n + extendSlack ≤ heapEnd - top

def InitialAllocator (m : Mem) (exts : List (Nat × Nat)) (reallocs : Nat × Nat → Prop)
    (stmts count : Nat) : Prop :=
  ∃ top brkv chunks bins, InitialAllocatorAt m exts reallocs stmts count top brkv chunks bins

theorem ChunkWalk.le {m : Mem} {p top : Nat} {cs : List Chunk}
    (h : ChunkWalk m p top cs) : p ≤ top := by
  induction h with
  | top => exact Nat.le_refl _
  | chunk _ _ _ _ _ _ ih => omega

/-- A heap whose top chunk has no readable header is not admitted. -/
theorem HeapAt.top_header_present {m : Mem} {exts : List (Nat × Nat)}
    {reallocs : Nat × Nat → Prop} {top brkv : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : HeapAt m exts reallocs top brkv chunks bins) : (read64 m (top + 8)).isSome := by
  rw [h.top_header]
  rfl

theorem not_initialAllocator_of_top {m : Mem} {exts : List (Nat × Nat)}
    {reallocs : Nat × Nat → Prop} {stmts count t : Nat} (htop : read64 m topAddr = some t)
    (hnone : read64 m (t + 8) = none) : ¬ InitialAllocator m exts reallocs stmts count := by
  rintro ⟨top, brkv, chunks, bins, h⟩
  have ht := h.heap.top_ptr
  rw [htop] at ht
  cases ht
  have hs := h.heap.top_header_present
  rw [hnone] at hs
  exact absurd hs (by decide)

#print axioms ChunkWalk.le
#print axioms HeapAt.top_header_present
#print axioms not_initialAllocator_of_top

end Vsa.Sim.DlHeap
