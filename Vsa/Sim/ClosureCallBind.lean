import Vsa.Sim.ClosureCallScope

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership ClosureParam

/-- The actual scope allocation and completed parameter fold share one execution. -/
structure BoundScopeAt (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (reserve : Nat) (st : Vsa.While.St) (env : Addr)
    (sp fn names savedS6 : BitVec 64) (cd : ClosureData) (values : List Value)
    (before called scope : Config) (p : BitVec 64) (after : Config) : Prop where
  scopePost : ClosureScopePost called.σ.regs.get? N M phiF phiC alloc exts shared
    (3 * values.length + reserve) st env sp p savedS6 values.length true
    called.σ.mem before.σ.sailOutput scope
  bound : FoldLoopState M N (pushFrameMap phiF st.store.frames.size p.toNat) phiC shared reserve
    (st.store.allocFrame (some env)).1 cd values st.store.frames.size
    sp p fn names savedS6 scope values.length after
  run : Steps called after

/-- Run scope allocation and every parameter binding from the reached dispatch call. -/
theorem ScopeReady.bind_params
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {reserve : Nat} {st : Vsa.While.St} {env : Addr}
    {sp call object fn interp parent saved5 saved3 savedS6 names : BitVec 64}
    {cd : ClosureData} {values : List Value} {depth : Nat} {before called : Config}
    (ready : ScopeReady N M phiF phiC alloc exts shared
      (3 * values.length + reserve + 1) st env sp parent savedS6 before called)
    (post : Post sp call object fn interp parent saved5 saved3 values.length depth before called)
    (data : FoldData before.σ.mem N phiC shared sp fn names cd.params values)
    (L : AllocLedger A SL gpv headroom maxReq M) (placement : BindingArena A SL)
    (R : ScopeResources A SL phiF st env sp interp parent gpv savedS6 before)
    (positive : 0 < values.length) (unique : StoreUnique st.store)
    (bounded : ∀ i (hi : i < values.length), ValueClosuresBounded st.store.closures.size values[i])
    (nameRequest : ∀ param ∈ cd.params, param.length + 1 ≤ maxReq)
    (growRequest : 48 * values.length ≤ maxReq)
    (present : EnvDefineSavedPresent called.σ.regs.get?) :
    ∃ scope p after, BoundScopeAt N M phiF phiC alloc exts shared reserve st env
      sp fn names savedS6 cd values before called scope p after := by
  have stackHi : sp.toNat + 1032 ≤ SL.hi := by have := R.stackHi; omega
  obtain ⟨scope, p, allocationSteps, scopePost⟩ := ready.allocate post L stackHi
    (by have := data.bound; omega)
  have branch : decide (0 < values.length) = true := by simp [positive]
  rw [branch] at scopePost
  have calledData : FoldData called.σ.mem N phiC shared sp fn names cd.params values :=
    data.transport ready.agreement (fun _ hk => hk) ready.arguments
  have closureReg : called.σ.regs.get? Register.x21 = some fn :=
    gholds_lookup _ post.regs (show lookupG 21 _ = some fn from rfl)
  obtain ⟨after, bindingSteps, bound⟩ := scopePost.bind_params calledData L placement
    R.stack R.stackRam R.stackWin stackHi positive unique bounded nameRequest growRequest
    closureReg present
  exact ⟨scope, p, after,
    { scopePost := scopePost, bound := bound
      run := allocationSteps.trans bindingSteps }⟩

/-- The dispatch supplies its reseated registers and preserves the other binding spills. -/
theorem Post.saved_present
    {sp call object fn interp parent saved5 saved3 : BitVec 64}
    {count depth : Nat} {before called : Config}
    (h : Post sp call object fn interp parent saved5 saved3 count depth before called)
    (present : EnvDefineSavedPresent before.σ.regs.get?) :
    EnvDefineSavedPresent called.σ.regs.get? := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have r : called.σ.regs.get? Register.x8 = some call :=
      gholds_lookup _ h.regs (show lookupG 8 _ = some call from rfl)
    rw [r]; rfl
  · rw [h.frame .x9 (by decide) (by decide) (by decide)]; exact present.s1
  · have r : called.σ.regs.get? Register.x18 = some interp :=
      gholds_lookup _ h.regs (show lookupG 18 _ = some interp from rfl)
    rw [r]; rfl
  · have r : called.σ.regs.get? Register.x19 = some saved3 :=
      gholds_lookup _ h.regs (show lookupG 19 _ = some saved3 from rfl)
    rw [r]; rfl
  · rw [h.frame .x20 (by decide) (by decide) (by decide)]; exact present.s4
  · have r : called.σ.regs.get? Register.x21 = some fn :=
      gholds_lookup _ h.regs (show lookupG 21 _ = some fn from rfl)
    rw [r]; rfl
  · rw [h.frame .x22 (by decide) (by decide) (by decide)]; exact present.s6

/-- Dispatch, scope creation, and parameter binding reach one body-entry state. -/
structure BoundCallAt (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (reserve : Nat) (st : Vsa.While.St) (env : Addr)
    (sp call object fn interp parent saved5 saved3 names savedS6 : BitVec 64)
    (cd : ClosureData) (values : List Value) (depth : Nat)
    (before called scope : Config) (p : BitVec 64) (after : Config) : Prop where
  dispatch : Post sp call object fn interp parent saved5 saved3 values.length depth before called
  binding : BoundScopeAt N M phiF phiC alloc exts shared reserve st env
    sp fn names savedS6 cd values before called scope p after
  run : Steps before after

/-- Execute the nonempty closure-call prefix through the complete owned fold. -/
theorem Pre.bind_params
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {reserve : Nat} {st : Vsa.While.St} {env : Addr}
    {sp call object fn interp parent a3 saved5 saved3 savedS6 names : BitVec 64}
    {cd : ClosureData} {values : List Value} {depth : Nat} {before : Config}
    (pre : Pre sp call object fn interp parent a3 saved5 saved3 values.length depth before)
    (L : AllocLedger A SL gpv headroom maxReq M) (placement : BindingArena A SL)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared
      (3 * values.length + reserve + 1) st.store before.σ.mem)
    (R : ScopeResources A SL phiF st env sp interp parent gpv savedS6 before)
    (data : FoldData before.σ.mem N phiC shared sp fn names cd.params values)
    (positive : 0 < values.length) (unique : StoreUnique st.store)
    (bounded : ∀ i (hi : i < values.length), ValueClosuresBounded st.store.closures.size values[i])
    (nameRequest : ∀ param ∈ cd.params, param.length + 1 ≤ maxReq)
    (growRequest : 48 * values.length ≤ maxReq)
    (present : EnvDefineSavedPresent before.σ.regs.get?) :
    ∃ called scope p after, BoundCallAt N M phiF phiC alloc exts shared reserve st env
      sp call object fn interp parent saved5 saved3 names savedS6 cd values depth
      before called scope p after := by
  obtain ⟨called, dispatchSteps, dispatch⟩ := run pre
  have ready := dispatch.scope_ready pre.geometry L allocator R
  obtain ⟨scope, p, after, bound⟩ := ready.bind_params dispatch data L placement R
    positive unique bounded nameRequest growRequest (dispatch.saved_present present)
  exact ⟨called, scope, p, after,
    { dispatch := dispatch, binding := bound, run := dispatchSteps.trans bound.run }⟩

end Vsa.Sim.ClosureCallPrefix
