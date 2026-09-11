import Vsa.Sim.BinaryRightStage
import Vsa.Sim.AllocatorCallCore

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- Invoke the right child with the left return's allocator and the reached register ghost. -/
theorem BinaryRightStaged.call_allocator
    {gpre : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st st' : Vsa.While.St} {d env : Nat} {er : Expr} {v : Value}
    {cost maxRequest reserve : Nat}
    {sp ret dst node interp operand v8 v9 v18 : BitVec 64}
    {before called : Config}
    (staged : BinaryRightStaged gpre N A SL phiF phiC st d env er
      sp ret dst node interp operand v8 v9 v18 before called)
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve)
      st.store before.σ.mem)
    (ast : ExprReprWithin before.σ.mem shared operand.toNat er)
    (gp : before.σ.regs.get? .x3 = some gpv)
    (ih : EvalAllocatorIH st d env er st' v cost maxRequest) :
    ∃ after, Steps before after ∧
      ReturnedWith
        (SubEvalReturn (fun R => called.σ.regs.get? R) N A SL phiF phiC
          st.store.frames.size st.store.closures.size st' v sp ret dst
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12))
          0x8000351c#64 v8 v9 v18 called.σ.mem)
        (EvalAllocatorCallData N M phiF phiC st.store.frames.size st.store.closures.size
          shared reserve st' v
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat before.σ.mem) after := by
  obtain ⟨br, segment⟩ := staged.segment
  have carried := BinaryPrefix.allocator_prefix L allocator segment.toSelectedFramedSegResult
    (fun _ hk => staged.window.second hk)
  obtain ⟨after, steps, returned⟩ := staged.call.call_allocator L hrequest carried.allocator
    (carried.ast ast) ((segment.reg_frame .x3 (by decide)).trans gp) ih
  exact ⟨after, segment.steps.trans steps, returned.result, returned.extra.rebase carried.agreement⟩

#print axioms BinaryRightStaged.call_allocator

end Vsa.Sim
