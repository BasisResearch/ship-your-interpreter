import Vsa.Sim.EnvDefineMissAppend
import Vsa.Sim.EnvDefineAppendComplete

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- A missing name in a nonempty frame executes either capacity arm and returns. -/
theorem EnvDefinePrologueAllocatorPost.return_miss
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {target : Addr} {valid : target < st.store.frames.size} {name : String} {v : Value}
    {esp env namePtr src r : BitVec 64} {m : Mem} {out : Array String}
    {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {alloc : Allocations}
    {exts : List Extent} {shared : Nat → Prop} {credits : Nat} {before : Config}
    (h : EnvDefinePrologueAllocatorPost g esp env namePtr src r m out N M
      phiF phiC alloc exts shared (credits + 3) st.store target valid name v before)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (geometry : EnvDefineGrowGeometry A SL esp src)
    (envAddr : env.toNat = phiF target) (ghostSp : g Register.x2 = some esp)
    (retAlign : r.toNat % 4 = 0) (sourceAlign : src.toNat % 8 = 0)
    (present : EnvDefineSavedPresent g)
    (bounded : ValueClosuresBounded st.store.closures.size v)
    (positive : 0 < (st.store.frames[target]'valid).vars.length)
    (missing : ∀ i (hi : i < (st.store.frames[target]'valid).vars.length),
      ((st.store.frames[target]'valid).vars[i]'hi).1 ≠ name)
    (nameRequest : name.length + 1 ≤ maxReq)
    (growRequest : 48 * (st.store.frames[target]'valid).vars.length ≤ maxReq) :
    ∃ after, Steps before after ∧
      EnvDefineReturnState g N A SL phiF phiC st target name v esp r m out after ∧
      AgreeP shared m after.σ.mem := by
  obtain ⟨ready, reachSteps, selected⟩ := h.reach_append L geometry envAddr ghostSp retAlign
    positive missing growRequest
  obtain ⟨alloc', exts', cap', entry⟩ := selected.selected
  obtain ⟨after, returnSteps, returned, agreement⟩ :=
    entry.return_append L geometry sourceAlign nameRequest present bounded
  exact ⟨after, reachSteps.trans returnSteps, returned,
    fun k hk => (selected.agreement k hk).trans (agreement k hk)⟩

#print axioms EnvDefinePrologueAllocatorPost.return_miss

end Vsa.Sim
