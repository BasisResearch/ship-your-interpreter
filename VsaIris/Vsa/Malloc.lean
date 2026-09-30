import VsaIris.MallocRun
import VsaIris.Vsa.Instance
import VsaIris.Vsa.HeapShape
import Vsa.AllocResource

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst

def vsaClob : List Nat := [5, 6, 7, 11, 12, 13, 14, 15, 16, 17, 28, 29, 30, 31]

def vsaSaved : List Nat := [8, 9, 18, 19]

theorem vsaAllocRegs_nodup : (allocRegs vsaClob vsaSaved).Nodup := by
  unfold allocRegs vsaClob vsaSaved PC ra a0 sp
  decide

def mallocEntryBV : BitVec 64 := BitVec.ofNat 64 Vsa.Alloc.mallocEntry
def freeEntryBV : BitVec 64 := BitVec.ofNat 64 Vsa.Alloc.freeEntry

structure TopReserve (m : Mem) (exts : List (Nat × Nat)) (maxReq k top bytes : Nat) : Prop where
  request_fits : physSize maxReq < 2 ^ 31
  top_pointer : read64 m topAddr = some top
  size_header : read64 m (top + 8) = some (bytes + 1)
  top_aligned : top % 16 = 0
  size_aligned : bytes % 16 = 0
  arena_lo : heapStart ≤ top
  arena_hi : top + bytes ≤ heapEnd
  capacity : k * physSize maxReq + 32 ≤ bytes
  disjoint : ∀ e ∈ exts, e.1 + e.2 ≤ top + 8 ∨ top + bytes ≤ e.1

def Reserve (m : Mem) (exts : List (Nat × Nat)) (maxReq k : Nat) : Prop :=
  0 < k → ∃ top bytes, TopReserve m exts maxReq k top bytes

theorem Reserve.zero (m : Mem) (exts : List (Nat × Nat)) (maxReq : Nat) :
    Reserve m exts maxReq 0 := fun h => absurd h (Nat.lt_irrefl 0)

end VsaIris.VsaHeap
