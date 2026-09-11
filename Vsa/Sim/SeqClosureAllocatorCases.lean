import Vsa.Sim.SeqClosureLoopInput
import Vsa.Sim.SeqClosureAllocatorFinal

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- The owned closure entry supplies every input to a normal nonfinal iteration. -/
theorem execSeqAllocatorAt_closure_consNormal
    {N : NativeAddrs} {st middle final : Vsa.While.St} {d env : Nat}
    {s : Stmt} {ss : List Stmt} {status : Status}
    {headCost tailCost headRequest tailRequest : Nat}
    (source : ExecS st d env s middle .normal) (nonempty : ss ≠ [])
    (head : ExecAllocatorAt N st d env s middle .normal headCost headRequest)
    (tail : ExecSeqAllocatorAt N .closureBody middle d env ss final status tailCost tailRequest) :
    ExecSeqAllocatorAt N .closureBody st d env (s :: ss) final status
      (headCost + tailCost) (max headRequest tailRequest) where
  run := by
    intro g A SL gpv headroom maxReq M L request phiF phiC alloc exts shared reserve
      sp aRet m0 before entry
    obtain ⟨body, base, interp, index, count, input⟩ := SeqClosureDispatch.LoopInput.of_entry entry
    exact SeqClosureDispatch.consNormal L request source head tail entry input nonempty

/-- A normally returning singleton executes the final closure-loop route. -/
theorem execSeqAllocatorAt_closure_singleton
    {N : NativeAddrs} {st final : Vsa.While.St} {d env : Nat} {s : Stmt}
    {cost request : Nat}
    (head : ExecAllocatorAt N st d env s final .normal cost request) :
    ExecSeqAllocatorAt N .closureBody st d env [s] final .normal cost request where
  run := by
    intro g A SL gpv headroom maxReq M L request phiF phiC alloc exts shared reserve
      sp aRet m0 before entry
    obtain ⟨body, base, interp, index, count, input⟩ := SeqClosureDispatch.LoopInput.of_entry entry
    exact SeqClosureDispatch.consFinal L request head entry input

/-- A value-returning head exits the closure sequence without executing its tail. -/
theorem execSeqAllocatorAt_closure_consRet
    {N : NativeAddrs} {st final : Vsa.While.St} {d env : Nat} {s : Stmt} {ss : List Stmt}
    {v : Value} {cost request : Nat}
    (head : ExecAllocatorAt N st d env s final (.ret v) cost request) :
    ExecSeqAllocatorAt N .closureBody st d env (s :: ss) final (.ret v) cost request where
  run := by
    intro g A SL gpv headroom maxReq M L request phiF phiC alloc exts shared reserve
      sp aRet m0 before entry
    obtain ⟨body, base, interp, index, count, input⟩ := SeqClosureDispatch.LoopInput.of_entry entry
    exact SeqClosureDispatch.consRet L request head entry input.toInput input.arenaBelow

#print axioms execSeqAllocatorAt_closure_consNormal
#print axioms execSeqAllocatorAt_closure_singleton
#print axioms execSeqAllocatorAt_closure_consRet

end Vsa.Sim
