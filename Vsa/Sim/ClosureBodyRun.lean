import Vsa.Sim.ClosureBodyAllocator

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open RuntimeOwnership

/-- Consume the reached owned sequence and retain its caller's memory baseline. -/
theorem ClosureBodyPost.run_sequence
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve : Nat} {st final : Vsa.While.St} {d env : Nat}
    {ss : List Stmt} {status : Status} {sp : BitVec 64} {before ready : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (h : ClosureBodyPost N M phiF phiC alloc exts shared (cost + reserve) st d env ss sp before ready)
    (body : ExecSeqAllocatorAt N .closureBody st d env ss final status cost request) :
    ∃ after, Steps ready after ∧ ExecSeqAllocatorReturn .closureBody before.σ.regs.get? N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve final status
      sp (sp + 144#64) before.σ.mem after := by
  obtain ⟨after, steps, child⟩ := body.run before.σ.regs.get? A SL gpv headroom maxReq M L hrequest
    phiF phiC alloc exts shared reserve sp (sp + 144#64) ready.σ.mem ready h.entry
  obtain ⟨resultF, resultC, repr⟩ := child.selected
  exact ⟨after, steps,
    { exit :=
        { child.exit with
          mem_frame := fun k hs ha => (child.exit.mem_frame k hs ha).trans (h.stackFrame k hs).symm
          stack_frame := h.highStack.trans child.exit.stack_frame
          mem_extends := h.presence.trans child.exit.mem_extends }
      selected := ⟨resultF, resultC, { repr with owned := repr.owned.rebase (fun _ hv => hv) h.agreement }⟩
      gp := child.gp }⟩

/-- Execute closure-body initialization and the complete owned sequence. -/
theorem closureBodyAllocator_run_sequence
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve : Nat} {st final : Vsa.While.St} {d env : Nat}
    {ss : List Stmt} {status : Status} {sp closure body base interp : BitVec 64} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (I : ClosureBodyInput N A SL phiF shared st d env ss sp closure body base interp before)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve)
      st.store before.σ.mem)
    (gp : before.σ.regs.get? Register.x3 = some gpv)
    (bodyRun : ExecSeqAllocatorAt N .closureBody st d env ss final status cost request) :
    ∃ after, Steps before after ∧ ExecSeqAllocatorReturn .closureBody before.σ.regs.get? N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve final status
      sp (sp + 144#64) before.σ.mem after := by
  obtain ⟨ready, setupSteps, setup⟩ := closureBodyAllocator_run L I allocator gp
  obtain ⟨after, bodySteps, result⟩ := setup.run_sequence L hrequest bodyRun
  exact ⟨after, setupSteps.trans bodySteps, result⟩

#print axioms ClosureBodyPost.run_sequence
#print axioms closureBodyAllocator_run_sequence

end Vsa.Sim
