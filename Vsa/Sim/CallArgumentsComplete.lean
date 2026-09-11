import Vsa.Sim.CallArgsBegin

namespace Vsa.Sim.CallCallee

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The callee and every argument are owned at closure dispatch; the outer caller frame is retained. -/
structure ArgumentsReady (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (alloc : Allocations) (exts : List Extent) (shared : Nat → Prop) (calleeCost argsCost reserve : Nat)
    (st middle final : Vsa.While.St) (d env : Nat) (callee : Expr) (args : List Expr)
    (calleeValue : Value) (values : List Value) (sp ret dst node interp saved7 : BitVec 64)
    (m0 : Mem) (after : Config) : Prop where
  pc : after.σ.regs.get? Register.PC = some 0x80003254#64
  loop : CallArgStage.LoopState N M phiF phiC st.store.frames.size st.store.closures.size shared reserve final
    ([(((sp - 1088#64) + 96#64).toNat, calleeValue)] ++ CallArgStage.argumentSlots (sp - 1088#64) 0 values)
    d env callee args node (sp - 1088#64) interp args.length m0 after
  path : ∃ start empty,
    ReturnedWith
      (fun _ => Started g N M phiF phiC alloc exts shared calleeCost (argsCost + reserve)
        st middle d env callee args calleeValue sp ret dst node interp saved7 m0 empty start)
      (CallArgStage.LoopFrame SL A (sp - 1088#64) start) after

/-- Run the call prologue, callee, and full argument list to the actual closure dispatch. -/
theorem evaluate_arguments
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {calleeCost argsCost request reserve : Nat} {st middle final : Vsa.While.St}
    {d env : Nat} {callee : Expr} {args : List Expr} {calleeValue : Value} {values : List Value}
    {sp ret dst node interp saved7 : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (requestBound : request ≤ maxReq)
    (entry : EvalAllocatorEntry g N M phiF phiC alloc exts shared (calleeCost + (argsCost + reserve))
      st d env (.call callee args) sp ret dst interp node m0 before)
    (saved7Reg : before.σ.regs.get? Register.x23 = some saved7) (countBound : args.length ≤ 32)
    (source : EvalE st d env callee middle calleeValue) (bounded : StoreClosuresBounded st.store)
    (calleeRun : EvalAllocatorAt N st d env callee middle calleeValue calleeCost request)
    (argsRun : CallArgStage.Arguments N d env request middle args final values argsCost) :
    ∃ after, Steps before after ∧ ArgumentsReady g N M phiF phiC alloc exts shared calleeCost argsCost reserve
      st middle final d env callee args calleeValue values sp ret dst node interp saved7 m0 after := by
  obtain ⟨start, empty, calleeSteps, started⟩ := CallCallee.start L requestBound entry saved7Reg countBound calleeRun
  have initial := started.loop_state entry source bounded countBound
  obtain ⟨after, argumentSteps, loop, frame⟩ := argsRun.run L requestBound []
    [(((sp - 1088#64) + 96#64).toNat, calleeValue)] start rfl initial
  exact ⟨after, calleeSteps.trans argumentSteps,
    { pc := by simpa [CallArgStage.loopPC] using loop.pc
      loop := loop, path := ⟨start, empty, started, frame⟩ }⟩

end Vsa.Sim.CallCallee
