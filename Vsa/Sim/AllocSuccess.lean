import Vsa.Sim.ReallocSpec
import Vsa.Sim.EvalSimCommon
import Vsa.Sim.Code.FixedImage
import Vsa.AllocReserve

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc
open Vsa.Logic

/-- Actual allocator entry with the fixed executable image. The invariant
supplier describes allocator metadata; code is supplied separately by the caller. -/
structure AllocatorCallEntry (SL : StackLayout) (gpv : BitVec 64) (headroom entry : Nat)
    (AInv : MState → List Extent → Prop)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent)
    (spv r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 entry)
  ra : c.σ.regs.get? Register.x1 = some r
  ra_align : r.toNat % 4 = 0
  sp : c.σ.regs.get? Register.x2 = some spv
  stack : StackOK SL spv headroom
  gp : c.σ.regs.get? Register.x3 = some gpv
  frame : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R
  ainv : AInv c.σ exts
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = out
  code : Code.FixedTextLoaded c.σ.mem

/-- Call resources refer to the entry's current memory and live ledger.
The initial resource supplier must establish both credit and concrete placement. -/
structure AllocationResources (A : Arena) (maxReq credits n : Nat)
    (exts : List Extent) (m : Mem) : Prop where
  bounded : n ≤ maxReq
  budget : ResourceBudget A maxReq exts (credits + 1)
  reserve : AllocationReserve A m exts maxReq (credits + 1)

/-- The next concrete placement follows from the retained reserve. -/
theorem AllocationResources.room {A : Arena} {maxReq credits n : Nat}
    {exts : List Extent} {m : Mem}
    (h : AllocationResources A maxReq credits n exts m) : AllocationRoom A m exts n :=
  h.reserve.room (Nat.zero_lt_succ _) h.bounded

/-- Common observations of the selected allocator return. -/
structure AllocatorReturn (gpv sp r : BitVec 64)
    (g : (R : Register) → Option (RegisterType R))
    (m0 : Mem) (out : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some r
  sp : c.σ.regs.get? Register.x2 = some sp
  gp : c.σ.regs.get? Register.x3 = some gpv
  frame : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R
  out : c.σ.sailOutput = out
  mem_extends : MemExtends m0 c.σ.mem
  code : Code.FixedTextLoaded c.σ.mem

/-- One nonzero pointer and its payload geometry at the selected return. -/
structure AllocationPointer (A : Arena) (p n : Nat) (σ : MState) : Prop where
  register : σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p)
  nonzero : p ≠ 0
  aligned : p % 16 = 0
  arena : A.contains p n

/-- Malloc success retains its fresh extent, frame, invariant, and unused
resources at the same endpoint as the result register. -/
structure MallocAllocated (A : Arena) (SL : StackLayout) (maxReq credits : Nat)
    (AInv : MState → List Extent → Prop) (privFoot : Nat → Prop)
    (exts : List Extent) (p n : Nat) (sp : BitVec 64) (m0 : Mem) (σ : MState) : Prop where
  pointer : AllocationPointer A p n σ
  disjoint : ∀ e ∈ exts, ExtDisjoint (p, n) e
  ainv : AInv σ ((p, n) :: exts)
  mem_frame : HeapPublicFrame privFoot SL sp [] m0 σ.mem
  budget : ResourceBudget A maxReq ((p, n) :: exts) credits
  reserve : AllocationReserve A σ.mem ((p, n) :: exts) maxReq credits

structure MallocSuccessEntry (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq credits : Nat) (AInv : MState → List Extent → Prop)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (sp r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  entry : AllocatorCallEntry SL gpv headroom mallocEntry AInv g exts sp r m0 out c
  request : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 n)
  resources : AllocationResources A maxReq credits n exts c.σ.mem

structure MallocSuccessExit (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (maxReq credits : Nat) (AInv : MState → List Extent → Prop) (privFoot : Nat → Prop)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (sp r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  returned : AllocatorReturn gpv sp r g m0 out c
  allocated : ∃ p, MallocAllocated A SL maxReq credits AInv privFoot exts p n sp m0 c.σ

/-- Required successful execution of the fixed malloc implementation.
Its supplier must prove the run and residual reserve from the actual entry.
This declaration supplies neither allocator correctness nor initial resources. -/
def MallocSuccessRun (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (AInv : MState → List Extent → Prop)
    (privFoot : Nat → Prop) : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R)) (exts : List Extent)
    (n credits : Nat) (sp r : BitVec 64) (m0 : Mem) (out : Array String),
    Triple (MallocSuccessEntry A SL gpv headroom maxReq credits AInv g exts n sp r m0 out)
      (MallocSuccessExit A SL gpv maxReq credits AInv privFoot g exts n sp r m0 out)

/-- Successful growth replaces the old live extent and copies its bytes.
Both affected extents remain explicit in the public memory frame. -/
structure ReallocGrown (A : Arena) (SL : StackLayout) (maxReq credits : Nat)
    (AInv : MState → List Extent → Prop) (privFoot : Nat → Prop)
    (exts : List Extent) (pOld nOld pNew nNew : Nat) (sp : BitVec 64)
    (m0 : Mem) (σ : MState) : Prop where
  pointer : AllocationPointer A pNew nNew σ
  disjoint : ∀ e ∈ exts, e ≠ (pOld, nOld) → ExtDisjoint (pNew, nNew) e
  copies : ReallocCopies m0 σ.mem pOld pNew nOld
  ainv : AInv σ ((pNew, nNew) :: exts.erase (pOld, nOld))
  mem_frame : HeapPublicFrame privFoot SL sp [(pOld, nOld), (pNew, nNew)] m0 σ.mem
  budget : ResourceBudget A maxReq ((pNew, nNew) :: exts.erase (pOld, nOld)) credits
  reserve : AllocationReserve A σ.mem ((pNew, nNew) :: exts.erase (pOld, nOld)) maxReq credits

structure ReallocNullAllocated (A : Arena) (SL : StackLayout) (maxReq credits : Nat)
    (AInv : MState → List Extent → Prop) (privFoot : Nat → Prop)
    (exts : List Extent) (p n : Nat) (sp : BitVec 64) (m0 : Mem) (σ : MState) : Prop where
  pointer : AllocationPointer A p n σ
  disjoint : ∀ e ∈ exts, ExtDisjoint (p, n) e
  ainv : AInv σ ((p, n) :: exts)
  mem_frame : HeapPublicFrame privFoot SL sp [(p, n)] m0 σ.mem
  budget : ResourceBudget A maxReq ((p, n) :: exts) credits
  reserve : AllocationReserve A σ.mem ((p, n) :: exts) maxReq credits

structure ReallocSuccessEntry (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq credits : Nat) (AInv : MState → List Extent → Prop)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (p n : Nat)
    (sp r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  entry : AllocatorCallEntry SL gpv headroom reallocEntry AInv g exts sp r m0 out c
  old_pointer : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p)
  request : c.σ.regs.get? Register.x11 = some (BitVec.ofNat 64 n)
  positive : 0 < n
  resources : AllocationResources A maxReq credits n exts c.σ.mem

structure ReallocGrowSuccessEntry (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq credits : Nat) (AInv : MState → List Extent → Prop)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent)
    (pOld nOld nNew : Nat) (sp r : BitVec 64) (m0 : Mem) (out : Array String)
    (c : Config) : Prop where
  call : ReallocSuccessEntry A SL gpv headroom maxReq credits AInv g exts pOld nNew sp r m0 out c
  growth : nOld < nNew
  nonzero : pOld ≠ 0
  live : (pOld, nOld) ∈ exts

structure ReallocGrowSuccessExit (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (maxReq credits : Nat) (AInv : MState → List Extent → Prop) (privFoot : Nat → Prop)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent)
    (pOld nOld nNew : Nat) (sp r : BitVec 64) (m0 : Mem) (out : Array String)
    (c : Config) : Prop where
  returned : AllocatorReturn gpv sp r g m0 out c
  grown : ∃ pNew, ReallocGrown A SL maxReq credits AInv privFoot exts pOld nOld pNew nNew sp m0 c.σ

structure ReallocNullSuccessExit (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (maxReq credits : Nat) (AInv : MState → List Extent → Prop) (privFoot : Nat → Prop)
    (g : (R : Register) → Option (RegisterType R)) (exts : List Extent) (n : Nat)
    (sp r : BitVec 64) (m0 : Mem) (out : Array String) (c : Config) : Prop where
  returned : AllocatorReturn gpv sp r g m0 out c
  allocated : ∃ p, ReallocNullAllocated A SL maxReq credits AInv privFoot exts p n sp m0 c.σ

/-- Required successful realloc runs. The implementation supplier retains
the reserve after each call; callers transport it through intervening writes. -/
structure ReallocSuccessRun (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (AInv : MState → List Extent → Prop)
    (privFoot : Nat → Prop) : Prop where
  grow : ∀ (g : (R : Register) → Option (RegisterType R)) (exts : List Extent)
    (pOld nOld nNew credits : Nat) (sp r : BitVec 64) (m0 : Mem) (out : Array String),
    Triple (ReallocGrowSuccessEntry A SL gpv headroom maxReq credits AInv
      g exts pOld nOld nNew sp r m0 out)
      (ReallocGrowSuccessExit A SL gpv maxReq credits AInv privFoot
        g exts pOld nOld nNew sp r m0 out)
  null : ∀ (g : (R : Register) → Option (RegisterType R)) (exts : List Extent)
    (n credits : Nat) (sp r : BitVec 64) (m0 : Mem) (out : Array String),
    Triple (ReallocSuccessEntry A SL gpv headroom maxReq credits AInv g exts 0 n sp r m0 out)
      (ReallocNullSuccessExit A SL gpv maxReq credits AInv privFoot g exts n sp r m0 out)

#print axioms AllocationResources.room

end Vsa.Sim
