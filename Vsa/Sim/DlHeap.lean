import Vsa.MemRepr
import Vsa.While.Cost

namespace Vsa.Sim.DlHeap

open Vsa.MemRepr Vsa.While

def avAddr : Nat := 0x8001ad10

def binblocksAddr : Nat := avAddr + 8

def topAddr : Nat := avAddr + 16
def sbrkBaseAddr : Nat := 0x8001b960
def maxSbrkedAddr : Nat := 0x8001b9a0
def topPadAddr : Nat := 0x8001b9a8

def brkAddr : Nat := 0x8001b990
def mallinfoAddr : Nat := 0x8001ba18

def heapStart : Nat := 0x8001c170

def heapEnd : Nat := 0x87800000
def numBins : Nat := 128

def binAt (i : Nat) : Nat := avAddr + 16 * i

def chunkSize (h : Nat) : Nat := h / 4 * 4

def prevInuse (h : Nat) : Bool := h % 2 == 1

def binIndex (sz : Nat) : Nat :=
  if sz / 512 = 0 then sz / 8
  else if sz / 512 ≤ 4 then 56 + sz / 64
  else if sz / 512 ≤ 20 then 91 + sz / 512
  else if sz / 512 ≤ 84 then 110 + sz / 4096
  else if sz / 512 ≤ 340 then 119 + sz / 32768
  else if sz / 512 ≤ 1364 then 124 + sz / 262144
  else 126

structure Chunk where
  addr : Nat
  size : Nat
  inuse : Bool

inductive ChunkWalk (m : Mem) : Nat → Nat → List Chunk → Prop where
  | top {p : Nat} : ChunkWalk m p p []
  | chunk {p top h h' : Nat} {cs : List Chunk} :
      read64 m (p + 8) = some h → h % 4 < 2 →
      32 ≤ chunkSize h → chunkSize h % 16 = 0 →
      read64 m (p + chunkSize h + 8) = some h' →
      ChunkWalk m (p + chunkSize h) top cs →
      ChunkWalk m p top (⟨p, chunkSize h, prevInuse h'⟩ :: cs)

inductive BinChain (m : Mem) (b : Nat) : Nat → Nat → List Nat → Prop where
  | close {prev : Nat} : read64 m (b + 24) = some prev → BinChain m b b prev []
  | link {q prev nxt : Nat} {qs : List Nat} :
      q ≠ b → read64 m (q + 24) = some prev → read64 m (q + 16) = some nxt →
      BinChain m b nxt q qs → BinChain m b q prev (q :: qs)

def BinList (m : Mem) (i : Nat) (qs : List Nat) : Prop :=
  ∃ first, read64 m (binAt i + 16) = some first ∧
    BinChain m (binAt i) first (binAt i) qs

structure HeapAt (m : Mem) (exts : List (Nat × Nat)) (reallocs : Nat × Nat → Prop)
    (top brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat) : Prop where
  sbrk_base : read64 m sbrkBaseAddr = some heapStart
  brk : read64 m brkAddr = some brkv
  brk_le : brkv ≤ heapEnd
  top_ptr : read64 m topAddr = some top
  top_le : top ≤ brkv
  top_size : (brkv - top) % 16 = 0

  top_header : read64 m (top + 8) = some (brkv - top + 1)
  top_pad : read64 m topPadAddr = some 0
  max_sbrked : (read64 m maxSbrkedAddr).isSome
  mallinfo : (read64 m mallinfoAddr).isSome

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

  remainder : (bins 1).length ≤ 1
  binblocks_present : (read64 m binblocksAddr).isSome
  binblocks : ∀ bb, read64 m binblocksAddr = some bb →
    ∀ i, 1 < i → i < numBins → bins i ≠ [] → bb / 2 ^ (i / 4) % 2 = 1

  live : ∀ e ∈ exts, ∃ c ∈ chunks, c.inuse = true ∧
    c.addr + 16 ≤ e.1 ∧ e.1 + e.2 ≤ c.addr + c.size + 8

  exact : ∀ e ∈ exts, reallocs e →
    ∃ c ∈ chunks, c.inuse = true ∧ c.addr + 16 = e.1 ∧ e.2 + 8 ≤ c.size

def extendSlack : Nat := 8192 + 64

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

end Vsa.Sim.DlHeap
