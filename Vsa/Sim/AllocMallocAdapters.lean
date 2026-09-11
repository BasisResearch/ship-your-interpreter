import Vsa.Sim.AllocRuns
import Vsa.Sim.AllocSuccessAdapters

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- Strengthen the actual malloc entry with its code and allocation resources. -/
theorem MallocSuccessEntry.of_entry
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq credits : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {g : (R : Register) → Option (RegisterType R)} {exts : List Extent} {n : Nat}
    {sp r : BitVec 64} {m0 : Mem} {out : Array String} {c : Config}
    (h : MallocEntry A SL gpv headroom maxReq M g exts n sp r m0 out c)
    (code : Code.FixedTextLoaded c.σ.mem)
    (resources : AllocationResources A maxReq credits n exts c.σ.mem) :
    MallocSuccessEntry A SL gpv headroom maxReq credits M.AInv g exts n sp r m0 out c :=
  { entry :=
      { good := h.good, tick := h.tick, pc := h.pc, ra := h.ra, ra_align := h.ra_align
        sp := h.sp, stack := h.stack, gp := h.gp, frame := h.frame
        ainv := h.ainv, mem := h.mem, out := h.out, code := code }
    request := h.a0, resources := resources }

/-- A selected successful allocation supplies the failure-aware exit at the same state. -/
theorem AllocatorReturn.toMallocExit
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq credits : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {g : (R : Register) → Option (RegisterType R)} {exts : List Extent} {p n : Nat}
    {sp r : BitVec 64} {m0 : Mem} {out : Array String} {c : Config}
    (h : AllocatorReturn gpv sp r g m0 out c)
    (result : MallocAllocated A SL maxReq credits M.AInv M.privFoot exts p n sp m0 c.σ) :
    MallocExit A SL gpv headroom maxReq M g exts n sp r m0 out c :=
  { good := h.good, tick := h.tick, pc := h.pc, sp := h.sp, gp := h.gp, frame := h.frame
    result := Or.inr ⟨p, result.pointer.register, result.pointer.nonzero,
      result.pointer.aligned, result.pointer.arena, result.disjoint, result.ainv⟩
    mem_frame := fun a hprivate hstack => result.mem_frame a hprivate hstack (by simp)
    out := h.out, mem_extends := h.mem_extends }

#print axioms MallocSuccessEntry.of_entry
#print axioms AllocatorReturn.toMallocExit

end Vsa.Sim
