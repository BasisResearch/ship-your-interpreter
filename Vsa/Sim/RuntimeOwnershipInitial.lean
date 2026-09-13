import Vsa.Sim.RuntimeOwnershipAllocation
import Vsa.MemReprWithin
import Vsa.Sim.Regions
import Vsa.Sim.DlHeap

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- Writable ELF sections and the complete runtime stack. Heap writes are
tracked separately by allocation roles. -/
def InitialWriteByte (SL : StackLayout) (k : Nat) : Prop :=
  (0x8001ad00 ≤ k ∧ k < 0x8001c168) ∨ (SL.lo ≤ k ∧ k < SL.hi)

def InitialReadableByte (k : Nat) : Prop :=
  0x80000000 ≤ k ∧ k < 0x100000000

/-- One shared domain and one live ledger for the represented program/store. -/
structure InitialOwnershipData where
  exts : List Extent
  allocations : Allocations
  shared : Nat → Prop

/-- Concrete backing-array alignment and occupied value-word presence.
Semantic ValueRepr alone does not specify the padding copied by env_get. -/
structure StoreArraysReady (m : Mem) (phiF : Addr → Nat) (s : Store) : Prop where
  namesAligned : ∀ fa, fa < s.frames.size → ∀ pn,
    read64 m (phiF fa + 8) = some pn → pn % 8 = 0
  valuesAligned : ∀ fa, fa < s.frames.size → ∀ pv,
    read64 m (phiF fa + 16) = some pv → pv % 8 = 0
  valueWords : ∀ fa, (hf : fa < s.frames.size) → ∀ pv,
    read64 m (phiF fa + 16) = some pv →
    ∀ i, i < s.frames[fa].vars.length → ValueWordsTotal m (pv + 24 * i)

/-- Frame arrays: the live extents `env_define` passes to `realloc`. -/
def ReallocExtent (alloc : Allocations) (e : Extent) : Prop :=
  ∃ fa, Allocated alloc (.names fa) e.1 e.2 ∨ Allocated alloc (.values fa) e.1 e.2

/-- Initial ownership. The heap starts at or above the ELF _end symbol and
ends before the stack. The dlmalloc heap is consistent with the live ledger
and has room for every terminating derivation of the represented program.
This does not assert termination or successful execution. -/
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
  /-- The arena is exactly the range `_sbrk` grows through. -/
  arenaHeap : A.lo = DlHeap.heapStart ∧ A.hi = DlHeap.heapEnd

theorem InitialOwned.ast_owned {m : Mem} {A : Arena} {SL : StackLayout}
    {phiF phiC : Addr → Nat} {stmts count : Nat} {D : InitialOwnershipData}
    (h : InitialOwned m A SL phiF phiC stmts count D)
    (p : Program) (hp : ProgramRepr m stmts count p) :
    ProgramReprWithin m (fun k => ¬ InitialWriteByte SL k) stmts count p :=
  (h.program p hp).mono h.heap.immutable.outsideWrites

theorem InitialOwned.ast_readable {m : Mem} {A : Arena} {SL : StackLayout}
    {phiF phiC : Addr → Nat} {stmts count : Nat} {D : InitialOwnershipData}
    (h : InitialOwned m A SL phiF phiC stmts count D)
    (p : Program) (hp : ProgramRepr m stmts count p) :
    ProgramReprWithin m InitialReadableByte stmts count p :=
  (h.program p hp).mono h.heap.immutable.readable

/-- Every live extent avoids ELF runtime storage and the stack. This applies
to immutable allocations as well as mutable allocation roles. -/
theorem InitialOwned.extent_outsideWrites {m : Mem} {A : Arena} {SL : StackLayout}
    {phiF phiC : Addr → Nat} {stmts count : Nat} {D : InitialOwnershipData}
    (h : InitialOwned m A SL phiF phiC stmts count D)
    {e : Extent} (he : e ∈ D.exts) {k : Nat} (hk : ExtentByte e k) :
    ¬ InitialWriteByte SL k := by
  have ha := (h.heap.ledger.arena.1 e he).2
  have hlo := h.heapLower
  have hhi := h.heapUpper
  change A.lo ≤ e.1 ∧ e.1 + e.2 ≤ A.hi at ha
  unfold ExtentByte at hk
  intro hw
  rcases hw with hw | hw <;> omega

#print axioms InitialOwned.ast_owned
#print axioms InitialOwned.ast_readable
#print axioms InitialOwned.extent_outsideWrites

end Vsa.Sim.RuntimeOwnership
