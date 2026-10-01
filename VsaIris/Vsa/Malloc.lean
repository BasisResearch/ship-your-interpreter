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


end VsaIris.VsaHeap
