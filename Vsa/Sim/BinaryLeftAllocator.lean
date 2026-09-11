import Vsa.Sim.BinaryLeftStage
import Vsa.Sim.AllocatorCallCore

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- Carry ownership through the left prefix and its child at the current native addresses. -/
theorem BinaryLeftStaged.call_allocator_at
    {gpre : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st st' : Vsa.While.St} {d env : Nat} {el : Expr} {v : Value}
    {cost maxRequest reserve : Nat}
    {sp ret dst node interp operand envReg v8 v9 v18 v19 : BitVec 64}
    {out : Array String} {before called : Config}
    (staged : BinaryLeftStaged gpre N A SL phiF phiC st d env el
      sp ret dst node interp operand envReg v8 v9 v18 v19 out before called)
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve)
      st.store before.σ.mem)
    (ast : ExprReprWithin before.σ.mem shared operand.toNat el)
    (gp : before.σ.regs.get? .x3 = some gpv)
    (ih : EvalAllocatorAt N st d env el st' v cost maxRequest) :
    ∃ after, Steps before after ∧
      ReturnedWith
        (SubEvalReturn gpre N A SL phiF phiC st.store.frames.size st.store.closures.size
          st' v sp ret dst ((sp - 1088#64) + sign_extend (m := 64) (0x078#12))
          0x800034fc#64 v8 v9 v18 called.σ.mem)
        (EvalAllocatorCallData N M phiF phiC st.store.frames.size st.store.closures.size
          shared reserve st' v
          ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat before.σ.mem) after := by
  obtain ⟨bs, segment⟩ := staged.segment
  have carried := BinaryPrefix.allocator_prefix L allocator segment.toSelectedFramedSegResult
    (fun _ hk => staged.window.first hk)
  obtain ⟨after, steps, returned⟩ := staged.call.call_allocator_at L hrequest carried.allocator
    (carried.ast ast) ((staged.frame .x3 (by decide)).symm.trans gp) ih
  exact ⟨after, segment.steps.trans steps, returned.result, returned.extra.rebase carried.agreement⟩

/-- The reached left prefix supplies the owned child entry and retains its actual return. -/
theorem BinaryLeftStaged.call_allocator
    {gpre : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st st' : Vsa.While.St} {d env : Nat} {el : Expr} {v : Value}
    {cost maxRequest reserve : Nat}
    {sp ret dst node interp operand envReg v8 v9 v18 v19 : BitVec 64}
    {out : Array String} {before called : Config}
    (staged : BinaryLeftStaged gpre N A SL phiF phiC st d env el
      sp ret dst node interp operand envReg v8 v9 v18 v19 out before called)
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve)
      st.store before.σ.mem)
    (ast : ExprReprWithin before.σ.mem shared operand.toNat el)
    (gp : before.σ.regs.get? .x3 = some gpv)
    (ih : EvalAllocatorIH st d env el st' v cost maxRequest) :
    ∃ after, Steps before after ∧
      ReturnedWith
        (SubEvalReturn gpre N A SL phiF phiC st.store.frames.size st.store.closures.size
          st' v sp ret dst ((sp - 1088#64) + sign_extend (m := 64) (0x078#12))
          0x800034fc#64 v8 v9 v18 called.σ.mem)
        (EvalAllocatorCallData N M phiF phiC st.store.frames.size st.store.closures.size
          shared reserve st' v
          ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat before.σ.mem) after :=
  staged.call_allocator_at L hrequest allocator ast gp (ih.at N)

#print axioms BinaryLeftStaged.call_allocator_at
#print axioms BinaryLeftStaged.call_allocator

end Vsa.Sim
