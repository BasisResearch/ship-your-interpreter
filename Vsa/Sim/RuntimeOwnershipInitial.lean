import Vsa.Sim.RuntimeOwnershipAllocation
import Vsa.MemReprWithin
import Vsa.Sim.Regions
import Vsa.Sim.DlHeap

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

def InitialWriteByte (SL : StackLayout) (k : Nat) : Prop :=
  (0x8001ad00 ≤ k ∧ k < 0x8001c168) ∨ (SL.lo ≤ k ∧ k < SL.hi)

def InitialReadableByte (k : Nat) : Prop :=
  0x80000000 ≤ k ∧ k < 0x100000000

structure InitialOwnershipData where
  exts : List Extent
  allocations : Allocations
  shared : Nat → Prop

structure StoreArraysReady (m : Mem) (phiF : Addr → Nat) (s : Store) : Prop where
  namesAligned : ∀ fa, fa < s.frames.size → ∀ pn,
    read64 m (phiF fa + 8) = some pn → pn % 8 = 0
  valuesAligned : ∀ fa, fa < s.frames.size → ∀ pv,
    read64 m (phiF fa + 16) = some pv → pv % 8 = 0
  valueWords : ∀ fa, (hf : fa < s.frames.size) → ∀ pv,
    read64 m (phiF fa + 16) = some pv →
    ∀ i, i < s.frames[fa].vars.length → ValueWordsTotal m (pv + 24 * i)

def ReallocExtent (alloc : Allocations) (e : Extent) : Prop :=
  ∃ fa, Allocated alloc (.names fa) e.1 e.2 ∨ Allocated alloc (.values fa) e.1 e.2

structure InitialOwned (m : Mem) (A : Arena) (SL : StackLayout)
    (phiF phiC : Addr → Nat) (stmts count : Nat) (D : InitialOwnershipData) : Prop where
  heapLower : 0x8001c170 ≤ A.lo
  heapUpper : A.hi ≤ SL.lo
  heap : HeapOwned A D.exts m phiF phiC D.allocations D.shared
    InitialReadableByte (InitialWriteByte SL) initSt.store
  arrays : StoreArraysReady m phiF initSt.store
  program : ∀ p : Program, ProgramRepr m stmts count p →
    ProgramReprWithin m D.shared stmts count p
  allocator : DlHeap.InitialAllocator m D.exts (ReallocExtent D.allocations) stmts count

  arenaHeap : A.lo = DlHeap.heapStart ∧ A.hi = DlHeap.heapEnd

end Vsa.Sim.RuntimeOwnership
