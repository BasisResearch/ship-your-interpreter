import Vsa.Sim.SeqBlockAllocatorStep

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- The owned block entry supplies every continuing normal iteration input. -/
theorem execSeqAllocatorAt_block_consNormal
    {N : NativeAddrs} {st middle final : Vsa.While.St} {d env : Nat}
    {s : Stmt} {ss : List Stmt} {status : Status}
    {headCost tailCost headRequest tailRequest : Nat}
    (source : ExecS st d env s middle .normal) (nonempty : ss ≠ [])
    (head : ExecAllocatorAt N st d env s middle .normal headCost headRequest)
    (tail : ExecSeqAllocatorAt N .blockBody middle d env ss final status tailCost tailRequest) :
    ExecSeqAllocatorAt N .blockBody st d env (s :: ss) final status
      (headCost + tailCost) (max headRequest tailRequest) where
  run := by
    intro g A SL gpv headroom maxReq M L request phiF phiC alloc exts shared reserve
      sp aRet m0 before entry
    obtain ⟨block, base, interp, index, count, input⟩ := SeqBlockDispatch.LoopInput.of_entry entry
    exact SeqBlockDispatch.consNormal L request source head tail entry input nonempty

/-- A normal singleton takes the block's final loop route. -/
theorem execSeqAllocatorAt_block_singleton
    {N : NativeAddrs} {st final : Vsa.While.St} {d env : Nat} {s : Stmt}
    {cost request : Nat}
    (head : ExecAllocatorAt N st d env s final .normal cost request) :
    ExecSeqAllocatorAt N .blockBody st d env [s] final .normal cost request where
  run := by
    intro g A SL gpv headroom maxReq M L request phiF phiC alloc exts shared reserve
      sp aRet m0 before entry
    obtain ⟨block, base, interp, index, count, input⟩ := SeqBlockDispatch.LoopInput.of_entry entry
    exact SeqBlockDispatch.consFinal L request head entry input

/-- Every abrupt child propagates its exact status through the block exit. -/
theorem execSeqAllocatorAt_block_consAbrupt
    {N : NativeAddrs} {st final : Vsa.While.St} {d env : Nat} {s : Stmt} {ss : List Stmt}
    {status : Status} {cost request : Nat}
    (head : ExecAllocatorAt N st d env s final status cost request) (abrupt : status ≠ .normal) :
    ExecSeqAllocatorAt N .blockBody st d env (s :: ss) final status cost request where
  run := by
    intro g A SL gpv headroom maxReq M L request phiF phiC alloc exts shared reserve
      sp aRet m0 before entry
    obtain ⟨block, base, interp, index, count, input⟩ := SeqBlockDispatch.LoopInput.of_entry entry
    exact SeqBlockDispatch.consAbrupt L request head abrupt entry input.toInput

#print axioms execSeqAllocatorAt_block_consNormal
#print axioms execSeqAllocatorAt_block_singleton
#print axioms execSeqAllocatorAt_block_consAbrupt

end Vsa.Sim
