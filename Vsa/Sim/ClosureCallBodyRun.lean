import Vsa.Sim.ClosureCallBody

namespace Vsa.Sim.ClosureCallPrefix

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The executed body returns one represented heap and the caller's actual saved slots. -/
structure BodyRunAt (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (shared : Nat → Prop) (reserve : Nat)
    (st final : Vsa.While.St) (env : Nat) (cd : ClosureData) (values : List Value) (status : Status)
    (sp call object fn interp parent saved5 saved3 : BitVec 64) (depth : Nat)
    (before called head : Config) (p : BitVec 64) (after : Config) : Prop where
  dispatch : Post sp call object fn interp parent saved5 saved3 values.length depth before called
  exit : ExecSeqExitI .closureBody head.σ.regs.get? N A SL
    (pushFrameMap phiF st.store.frames.size p.toNat) phiC
    (closureBoundStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size).frames.size
    (closureBoundStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size).closures.size
    final status sp (sp + 144#64) head.σ.mem after
  selected : ∃ resultF resultC, ReturnRepr N A
    (pushFrameMap phiF st.store.frames.size p.toNat) phiC resultF resultC
    (closureBoundStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size).frames.size
    (closureBoundStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size).closures.size
    final.store (statusResults (sp + 144#64).toNat status)
    (AllocatorResult M N shared reserve final.store (statusResults (sp + 144#64).toNat status) before.σ.mem)
    (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem
  gp : after.σ.regs.get? Register.x3 = some gpv
  spReg : after.σ.regs.get? Register.x2 = some sp
  interpReg : after.σ.regs.get? Register.x18 = some interp
  s1 : after.σ.regs.get? Register.x9 = before.σ.regs.get? Register.x9
  s4 : after.σ.regs.get? Register.x20 = before.σ.regs.get? Register.x20
  frame : ∀ R, bodyKeep R = true → after.σ.regs.get? R = before.σ.regs.get? R
  highStack : ∀ k, sp.toNat + 1032 ≤ k → k < SL.hi → called.σ.mem[k]? = after.σ.mem[k]?
  saved7Frame : ∀ k, sp.toNat + 1016 ≤ k → k < sp.toNat + 1024 →
    before.σ.mem[k]? = after.σ.mem[k]?
  presence : MemExtends before.σ.mem after.σ.mem
  memoryFrame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < SL.hi) →
    before.σ.mem[k]? = after.σ.mem[k]?
  run : Steps before after

/-- Run the complete body from the call's selected scope and parameter bindings. -/
theorem BodyCallAt.run_sequence
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {shared : Nat → Prop} {cost request reserve : Nat}
    {st final : Vsa.While.St} {env d : Nat} {cd : ClosureData} {values : List Value} {status : Status}
    {sp call object fn interp parent saved5 saved3 body base p : BitVec 64} {depth : Nat}
    {before called head : Config}
    (h : BodyCallAt N M phiF phiC shared (cost + reserve) st env d cd values
      sp call object fn interp parent saved5 saved3 body base depth before called p head)
    (L : AllocLedger A SL gpv headroom maxReq M) (requestBound : request ≤ maxReq)
    (stackHi : sp.toNat + 1024 ≤ SL.hi)
    (bodyRun : ExecSeqAllocatorAt N .closureBody
      ⟨closureBoundStore (st.store.allocFrame (some env)).1 cd values st.store.frames.size,
        Vsa.Machine.output before.σ⟩ d st.store.frames.size cd.body final status cost request) :
    ∃ after, BodyRunAt N M phiF phiC shared reserve st final env cd values status
      sp call object fn interp parent saved5 saved3 depth before called head p after := by
  obtain ⟨alloc, exts, shared', ready⟩ := h.selected
  obtain ⟨after, steps, result⟩ := closureBodyAllocator_run_sequence L requestBound
    ready.input ready.allocator ready.gp bodyRun
  obtain ⟨resultF, resultC, repr⟩ := result.selected
  exact ⟨after,
    { dispatch := h.dispatch, exit := result.exit
      selected := ⟨resultF, resultC,
        { repr with owned := repr.owned.rebase_shared ready.includes (fun _ hv => hv) ready.agreement }⟩
      gp := result.gp
      spReg := (result.exit.frame .x2 (by unfold ExecSeqFrameReg; decide)).trans ready.input.spReg
      interpReg := (result.exit.frame .x18 (by unfold ExecSeqFrameReg; decide)).trans ready.input.interpReg
      s1 := (result.exit.frame .x9 (by unfold ExecSeqFrameReg; decide)).trans ready.s1
      s4 := (result.exit.frame .x20 (by unfold ExecSeqFrameReg; decide)).trans ready.s4
      frame := fun R hr => (result.exit.frame R (by
        have mask : ∀ R, bodyKeep R = true → ExecSeqFrameReg .closureBody R := by
          intro reg; cases reg <;> unfold ExecSeqFrameReg <;> decide
        exact mask R hr)).trans (ready.frame R hr)
      highStack := fun k hlo hhi =>
        (h.highStack k hlo hhi).trans (result.exit.stack_frame k (by omega) hhi).symm
      saved7Frame := fun k hlo hhi =>
        (h.saved7Frame k hlo hhi).trans (result.exit.stack_frame k (by omega) (by omega)).symm
      presence := ready.presence.trans result.exit.mem_extends
      memoryFrame := fun k ha hs => (ready.memoryFrame k ha hs).trans (result.exit.mem_frame k hs ha).symm
      run := h.run.trans steps }⟩

end Vsa.Sim.ClosureCallPrefix
