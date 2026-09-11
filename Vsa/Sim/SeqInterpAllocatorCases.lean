import Vsa.Sim.SeqInterpLoopInput

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- The owned interpreter entry supplies every normal nonfinal iteration input. -/
theorem execSeqAllocatorAt_interp_consNormal
    {N : NativeAddrs} {st middle final : Vsa.While.St} {d env : Nat}
    {s : Stmt} {ss : List Stmt} {headCost tailCost headRequest tailRequest : Nat}
    (source : ExecS st d env s middle .normal) (nonempty : ss ≠ [])
    (head : ExecAllocatorAt N st d env s middle .normal headCost headRequest)
    (tail : ExecSeqAllocatorAt N .interpRun middle d env ss final .normal tailCost tailRequest) :
    ExecSeqAllocatorAt N .interpRun st d env (s :: ss) final .normal
      (headCost + tailCost) (max headRequest tailRequest) where
  run := by
    intro g A SL gpv headroom maxReq M L request phiF phiC alloc exts shared reserve
      sp aRet m0 before entry
    obtain ⟨cursor, finish, interp, input⟩ := SeqInterpDispatch.LoopInput.of_entry entry
    exact SeqInterpDispatch.consNormal L request source head tail entry input nonempty

/-- A normal singleton executes the final interpreter-loop route. -/
theorem execSeqAllocatorAt_interp_singleton
    {N : NativeAddrs} {st final : Vsa.While.St} {d env : Nat} {s : Stmt}
    {cost request : Nat}
    (head : ExecAllocatorAt N st d env s final .normal cost request) :
    ExecSeqAllocatorAt N .interpRun st d env [s] final .normal cost request where
  run := by
    intro g A SL gpv headroom maxReq M L request phiF phiC alloc exts shared reserve
      sp aRet m0 before entry
    obtain ⟨cursor, finish, interp, input⟩ := SeqInterpDispatch.LoopInput.of_entry entry
    exact SeqInterpDispatch.consFinal L request head entry input

#print axioms execSeqAllocatorAt_interp_consNormal
#print axioms execSeqAllocatorAt_interp_singleton

end Vsa.Sim
