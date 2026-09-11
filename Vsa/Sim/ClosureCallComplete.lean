import Vsa.Sim.ClosureCallFinish

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership ClosureParam

/-- Execute closure dispatch, scope allocation, binding, body, and the complete owned return. -/
theorem Pre.complete
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve : Nat} {st final : Vsa.While.St} {env d : Addr}
    {sp call object fn interp parent a3 saved5 saved3 saved7 savedS6 names body base ret sret v8 v9 v18 : BitVec 64}
    {cd : ClosureData} {values : List Value} {depth : Nat} {m0 : Mem} {before : Config}
    {status : Status} {value : Value}
    (pre : Pre (sp - 1088#64) call object fn interp parent a3 saved5 saved3 values.length depth before)
    (L : AllocLedger A SL gpv headroom maxReq M) (placement : BindingArena A SL)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared
      (3 * values.length + (cost + reserve) + 1) st.store before.σ.mem)
    (R : ScopeResources A SL phiF st env (sp - 1088#64) interp parent gpv savedS6 before)
    (data : FoldData before.σ.mem N phiC shared (sp - 1088#64) fn names cd.params values)
    (bodyData : FoldBodyData N A SL shared st.store d cd.body (sp - 1088#64) fn body base interp before)
    (stack : StackOK SL (sp - 1088#64) (176 + 1088))
    (unique : StoreUnique st.store)
    (bounded : ∀ i (hi : i < values.length), ValueClosuresBounded st.store.closures.size values[i])
    (nameRequest : ∀ param ∈ cd.params, param.length + 1 ≤ maxReq)
    (growRequest : 48 * values.length ≤ maxReq)
    (present : EnvDefineSavedPresent before.σ.regs.get?)
    (caller : CallerFrame g A SL sp ret sret interp v8 v9 v18 saved5 saved3 saved7 depth m0 before)
    (windows : ClosureReturn.StackWindows SL interp sret) (region : NullRegion sret)
    (agreement : AgreeP shared m0 before.σ.mem) (out : OutRepr before.σ st)
    (requestBound : request ≤ maxReq)
    (bodyRun : ExecSeqAllocatorAt N .closureBody
      ⟨closureBoundStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size, st.out⟩
      d st.store.frames.size cd.body final status cost request)
    (meaning : status = .normal ∧ value = .null ∨ status = .ret value) :
    ∃ after, Steps before after ∧
      EvalAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size shared reserve
        final value sp ret sret m0 after := by
  obtain ⟨called, p, head, prepared⟩ := pre.prepare_body L placement allocator R data bodyData stack
    unique bounded nameRequest growRequest present
  have sourceOutput : Vsa.Machine.output before.σ = st.out := out
  obtain ⟨exited, executed⟩ := prepared.run_sequence L requestBound
    (by have := R.stackHi; omega) (by simpa only [sourceOutput] using bodyRun)
  exact executed.finish L pre.geometry caller windows region agreement meaning

end Vsa.Sim.ClosureCallPrefix
