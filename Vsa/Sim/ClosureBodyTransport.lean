import Vsa.Sim.ClosureBodyReads
import Vsa.Sim.ClosureCallScope

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership ClosureParam

/-- Actual heap/stack and register preservation needed by the body handoff. -/
structure ClosureBodyFrame (A : Arena) (SL : StackLayout) (shared shared' : Nat → Prop)
    (closure : BitVec 64) (before after : Config) : Prop where
  agreement : AgreeP shared before.σ.mem after.σ.mem
  includes : ∀ k, shared k → shared' k
  presence : MemExtends before.σ.mem after.σ.mem
  memory : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < SL.hi) →
    before.σ.mem[k]? = after.σ.mem[k]?
  s1 : after.σ.regs.get? Register.x9 = before.σ.regs.get? Register.x9
  interp : after.σ.regs.get? Register.x18 = before.σ.regs.get? Register.x18
  s4 : after.σ.regs.get? Register.x20 = before.σ.regs.get? Register.x20
  closureReg : after.σ.regs.get? Register.x21 = some closure

/-- Preserve all body inputs through one actual prefix, allocation, or binding run. -/
theorem ClosureParam.FoldBodyData.transport_frame
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {shared shared' : Nat → Prop}
    {store store' : Store} {d : Nat} {ss : List Stmt}
    {sp closure body base interp : BitVec 64} {before after : Config}
    (h : FoldBodyData N A SL shared store d ss sp closure body base interp before)
    (frame : ClosureBodyFrame A SL shared shared' closure before after)
    (bodies : StoreBodiesBound store' perCallBudget) :
    FoldBodyData N A SL shared' store' d ss sp closure body base interp after :=
  { bodyRead := (h.bodyCovered.read64_eq frame.agreement).symm.trans h.bodyRead
    bodyCovered := h.bodyCovered.mono frame.includes
    baseRead := (h.resources.baseCovered.read64_eq frame.agreement).symm.trans h.baseRead
    countRead := (h.resources.countCovered.read32_eq frame.agreement).symm.trans h.countRead
    countBound := h.countBound
    suffix := h.suffix.transport_heap_stack frame.presence frame.memory frame.agreement frame.includes
    resources :=
      { h.resources with
        baseCovered := h.resources.baseCovered.mono frame.includes
        countCovered := h.resources.countCovered.mono frame.includes
        spill9 := by obtain ⟨v, hv⟩ := h.resources.spill9; exact ⟨v, frame.s1.trans hv⟩
        spill20 := by obtain ⟨v, hv⟩ := h.resources.spill20; exact ⟨v, frame.s4.trans hv⟩
        spill21 := ⟨closure, frame.closureReg⟩ }
    interpReg := frame.interp.trans h.interpReg, storeBodies := bodies }

/-- The same dispatch endpoint used by scope allocation retains the complete body data. -/
theorem ClosureCallPrefix.ScopeReady.body_data
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {sp call object fn interp parent saved5 saved3 savedS6 body base : BitVec 64}
    {count depth d : Nat} {ss : List Stmt} {before called : Config}
    (ready : ClosureCallPrefix.ScopeReady N M phiF phiC alloc exts shared credits st env
      sp parent savedS6 before called)
    (post : ClosureCallPrefix.Post sp call object fn interp parent saved5 saved3 count depth before called)
    (data : FoldBodyData N A SL shared st.store d ss sp fn body base interp before) :
    FoldBodyData N A SL shared st.store d ss sp fn body base interp called := by
  apply data.transport_frame (bodies := data.storeBodies)
  exact
    { agreement := ready.agreement, includes := fun _ hk => hk, presence := ready.presence
      memory := fun k _ hs => ready.stackFrame k hs
      s1 := post.frame .x9 (by decide) (by decide) (by decide)
      interp := post.frame .x18 (by decide) (by decide) (by decide)
      s4 := post.frame .x20 (by decide) (by decide) (by decide)
      closureReg := gholds_lookup _ post.regs (show lookupG 21 _ = some fn from rfl) }

/-- Fresh scope allocation preserves the body on both parameter branches. -/
theorem ClosureScopePost.body_data
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {sp p closure interp savedS6 body base : BitVec 64}
    {count d : Nat} {ss : List Stmt} {hasParams : Bool}
    {out : Array String} {called after : Config}
    (h : ClosureScopePost called.σ.regs.get? N M phiF phiC alloc exts shared credits st env
      sp p savedS6 count hasParams called.σ.mem out after)
    (data : FoldBodyData N A SL shared st.store d ss sp closure body base interp called)
    (stackLo : SL.lo ≤ sp.toNat) (stackHi : sp.toNat + 1032 ≤ SL.hi)
    (closureReg : called.σ.regs.get? Register.x21 = some closure) :
    FoldBodyData N A SL shared (st.store.allocFrame (some env)).1 d ss
      sp closure body base interp after := by
  apply data.transport_frame (store' := (st.store.allocFrame (some env)).1)
    (bodies := by exact data.storeBodies)
  refine
    { agreement := h.agreement, includes := fun _ hk => hk, presence := h.presence
      memory := ?_, s1 := h.frame .x9 (by decide), interp := h.frame .x18 (by decide)
      s4 := h.frame .x20 (by decide), closureReg := (h.frame .x21 (by decide)).trans closureReg }
  intro k ha hs
  symm
  exact h.memoryFrame k ha (by omega) (by omega)

end Vsa.Sim
