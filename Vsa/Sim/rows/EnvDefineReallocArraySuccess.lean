import Vsa.Sim.AllocSuccess
import Vsa.Sim.RuntimeOwnershipArrays

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc
open Vsa.Logic
open RuntimeOwnership (Allocations Role ArrayOwned heapArena_erase_zero)

/-- Run realloc for an empty or live array from its actual resource-bearing
entry. The selected return retains copied bytes, replacement, public framing,
and placement for the following allocation. The allocator implementation must
supply `RI`; initial ownership must supply the entry resources. -/
theorem reallocArraySuccess_run {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {AInv : MState → List Extent → Prop} {privFoot : Nat → Prop}
    (RI : ReallocSuccessRun A SL gpv headroom maxReq AInv privFoot)
    {exts : List Extent} {alloc : Allocations} {role : Role} {pOld width cap nNew : Nat}
    (harena : HeapArena A exts)
    (hold : ArrayOwned alloc role pOld width cap)
    (hmem : 0 < cap → (pOld, width * cap) ∈ exts)
    (hnz : 0 < cap → pOld ≠ 0)
    (hgrow : width * cap < nNew)
    (g : (R : Register) → Option (RegisterType R)) (sp r : BitVec 64) (m0 : Mem)
    (out : Array String) (credits : Nat) :
    Triple
      (ReallocSuccessEntry A SL gpv headroom maxReq credits AInv g exts pOld nNew sp r m0 out)
      (ReallocGrowSuccessExit A SL gpv maxReq credits AInv privFoot
        g exts pOld (width * cap) nNew sp r m0 out) := by
  intro c entry
  rcases hold with ⟨hz, hp⟩ | ⟨hc, _⟩
  · subst hz
    subst hp
    obtain ⟨c', steps, post⟩ := RI.null g exts nNew credits sp r m0 out c entry
    obtain ⟨pNew, result⟩ := post.allocated
    refine ⟨c', steps, { returned := post.returned, grown := ⟨pNew, ?_⟩ }⟩
    exact
      { pointer := result.pointer
        disjoint := fun e he _ => result.disjoint e he
        copies := by
          intro k hk
          simp only [Nat.mul_zero] at hk
          omega
        ainv := by simpa only [Nat.mul_zero, heapArena_erase_zero harena] using result.ainv
        mem_frame := fun a hprivate hstack houtside =>
          result.mem_frame a hprivate hstack
            (fun e he => houtside e (List.mem_cons_of_mem _ he))
        budget := by simpa only [Nat.mul_zero, heapArena_erase_zero harena] using result.budget
        reserve := by simpa only [Nat.mul_zero, heapArena_erase_zero harena] using result.reserve }
  · exact RI.grow g exts pOld (width * cap) nNew credits sp r m0 out c
      { call := entry, growth := hgrow, nonzero := hnz hc, live := hmem hc }

#print axioms reallocArraySuccess_run

end Vsa.Sim
