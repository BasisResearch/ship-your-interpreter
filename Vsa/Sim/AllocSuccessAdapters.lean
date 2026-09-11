import Vsa.Sim.AllocSuccess

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- Read one selected malloc result at the successful operation's endpoint. -/
theorem MallocSuccessExit.result
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {maxReq credits : Nat}
    {AInv : MState → List Extent → Prop} {privFoot : Nat → Prop}
    {g : (R : Register) → Option (RegisterType R)} {exts : List Extent} {n : Nat}
    {sp r : BitVec 64} {m0 : Mem} {out : Array String} {c : Config}
    (h : MallocSuccessExit A SL gpv maxReq credits AInv privFoot g exts n sp r m0 out c) :
    ∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
      p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p n ∧
      (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧ AInv c.σ ((p, n) :: exts) := by
  obtain ⟨p, result⟩ := h.allocated
  exact ⟨p, result.pointer.register, result.pointer.nonzero, result.pointer.aligned,
    result.pointer.arena, result.disjoint, result.ainv⟩

/-- Assemble a successful-call entry from the actual ABI entry and resources.
The caller supplies code and placement at that entry's memory. -/
theorem ReallocSuccessEntry.of_pre
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq credits : Nat}
    {AInv : MState → List Extent → Prop}
    {g : (R : Register) → Option (RegisterType R)} {exts : List Extent} {p n : Nat}
    {sp r : BitVec 64} {m0 : Mem} {out : Array String} {c : Config}
    (h : ReallocPre SL gpv headroom AInv exts p n sp r m0 g c)
    (outEq : c.σ.sailOutput = out) (code : Code.FixedTextLoaded c.σ.mem)
    (resources : AllocationResources A maxReq credits n exts c.σ.mem)
    (positive : 0 < n) :
    ReallocSuccessEntry A SL gpv headroom maxReq credits AInv g exts p n sp r m0 out c := by
  obtain ⟨good, tick, pc, old, request, ra, aligned, stackPointer, stack,
    gp, frame, invariant, memory⟩ := h
  exact
    { entry :=
        { good := good, tick := tick, pc := pc, ra := ra, ra_align := aligned
          sp := stackPointer, stack := stack, gp := gp, frame := frame
          ainv := invariant, mem := memory, out := outEq, code := code }
      old_pointer := old, request := request, positive := positive, resources := resources }

/-- Project the ABI from the same successful return. -/
theorem AllocatorReturn.toReallocPost
    {gpv sp r : BitVec 64} {g : (R : Register) → Option (RegisterType R)}
    {m0 : Mem} {out : Array String} {c : Config}
    (h : AllocatorReturn gpv sp r g m0 out c) : ReallocPost gpv sp r g c :=
  ⟨h.good, h.tick, h.pc, h.sp, h.gp, h.frame⟩

/-- The successful grow refines the failure-aware result at its own endpoint. -/
theorem ReallocGrown.toResult
    {A : Arena} {SL : StackLayout} {maxReq credits : Nat}
    {AInv : MState → List Extent → Prop} {privFoot : Nat → Prop}
    {exts : List Extent} {pOld nOld pNew nNew : Nat} {sp : BitVec 64}
    {m0 : Mem} {σ : MState}
    (h : ReallocGrown A SL maxReq credits AInv privFoot exts pOld nOld pNew nNew sp m0 σ) :
    ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 σ :=
  Or.inr ⟨pNew, h.pointer.register, h.pointer.nonzero, h.pointer.aligned,
    h.pointer.arena, h.disjoint, h.copies, h.ainv, h.mem_frame⟩

/-- The successful NULL-input allocation refines its failure-aware result. -/
theorem ReallocNullAllocated.toResult
    {A : Arena} {SL : StackLayout} {maxReq credits : Nat}
    {AInv : MState → List Extent → Prop} {privFoot : Nat → Prop}
    {exts : List Extent} {p n : Nat} {sp : BitVec 64} {m0 : Mem} {σ : MState}
    (h : ReallocNullAllocated A SL maxReq credits AInv privFoot exts p n sp m0 σ) :
    ReallocNullResult A SL privFoot AInv exts n sp m0 σ :=
  Or.inr ⟨p, h.pointer.register, h.pointer.nonzero, h.pointer.aligned,
    h.pointer.arena, h.disjoint, h.ainv, h.mem_frame⟩

#print axioms ReallocSuccessEntry.of_pre
#print axioms MallocSuccessExit.result
#print axioms AllocatorReturn.toReallocPost
#print axioms ReallocGrown.toResult
#print axioms ReallocNullAllocated.toResult

end Vsa.Sim
