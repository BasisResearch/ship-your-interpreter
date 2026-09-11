import Vsa.Sim.BinaryRightAllocator
import Vsa.Sim.BinaryOperandBind
import Vsa.Sim.SubEvalReturnFacts

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- Both operand slots and allocator ownership use the final child's selected maps. -/
structure BinaryAllocatorReturnData (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (reserve : Nat)
    (st : Vsa.While.St) (vl vr : Value) (sp : BitVec 64) (m0 : Mem) (c : Config) : Prop where
  selected : ∃ resultF resultC,
    ReturnRepr N A phiF phiC resultF resultC nf nc st.store
      [((sp + 120#64).toNat, vl), ((sp + 144#64).toNat, vr)]
      (AllocatorResult M N shared reserve st.store
        [((sp + 120#64).toNat, vl), ((sp + 144#64).toNat, vr)] m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) c.σ.mem
  gp : c.σ.regs.get? Register.x3 = some gpv

/-- Run the right child at the current native addresses and retain both owned operands. -/
theorem BinaryRightStaged.bind_allocator_at
    {gpre : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {entryF entryC middleF middleC : Addr → Nat} {nf nc : Nat}
    {alloc : Allocations} {exts : List Extent} {entryShared shared : Nat → Prop}
    {st st' : Vsa.While.St} {d env : Nat} {er : Expr} {vl vr : Value}
    {cost maxRequest reserve : Nat}
    {sp ret dst node interp operand v8 v9 v18 : BitVec 64}
    {m0 : Mem} {before called : Config}
    {FirstOwned : (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    {firstWrites : Nat → Prop}
    (staged : BinaryRightStaged gpre N A SL middleF middleC st d env er
      sp ret dst node interp operand v8 v9 v18 before called)
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (data : AllocatorResultAt M N entryShared (cost + reserve) st.store
      [(((sp - 1088#64) + 120#64).toNat, vl)] m0
      middleF middleC alloc exts shared before.σ.mem)
    (first : ReturnRepr N A entryF entryC middleF middleC nf nc st.store
      [(((sp - 1088#64) + 120#64).toNat, vl)] FirstOwned firstWrites before.σ.mem)
    (ast : ExprReprWithin before.σ.mem shared operand.toNat er)
    (gp : before.σ.regs.get? .x3 = some gpv)
    (ih : EvalAllocatorAt N st d env er st' vr cost maxRequest)
    (lowered : (sp - 1088#64).toNat = sp.toNat - 1088)
    (ram : (sp - 1088#64).toNat + 1056 ≤ 0x100000000)
    (hsizeF : nf ≤ st.store.frames.size) (hsizeC : nc ≤ st.store.closures.size)
    (hbound : ValueClosuresBounded st.store.closures.size vl) :
    ∃ after, Steps before after ∧
      ReturnedWith
        (SubEvalReturn (fun R => called.σ.regs.get? R) N A SL middleF middleC
          st.store.frames.size st.store.closures.size st' vr sp ret dst
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12))
          0x8000351c#64 v8 v9 v18 called.σ.mem)
        (BinaryAllocatorReturnData N M entryF entryC nf nc entryShared reserve
          st' vl vr (sp - 1088#64) m0) after := by
  obtain ⟨br, segment⟩ := staged.segment
  have carried := BinaryPrefix.allocator_prefix L data.allocator
    segment.toSelectedFramedSegResult (fun _ hk => staged.window.second hk)
  obtain ⟨after, steps, returned⟩ := staged.call.call_allocator_at L hrequest
    carried.allocator (carried.ast ast) ((segment.reg_frame .x3 (by decide)).trans gp) ih
  have exit := returned.result.toExit (by decide) lowered
  obtain ⟨resultF, resultC, both⟩ := BinaryPrefix.bind_operands L data first
    segment.toSelectedFramedSegResult returned.extra.repr steps exit.memFrame
    staged.window ram hsizeF hsizeC hbound
  exact ⟨after, segment.steps.trans steps, returned.result,
    { selected := ⟨resultF, resultC, both⟩, gp := returned.extra.gp }⟩

/-- Run the staged right child and retain the left operand through its actual frame. -/
theorem BinaryRightStaged.bind_allocator
    {gpre : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {entryF entryC middleF middleC : Addr → Nat} {nf nc : Nat}
    {alloc : Allocations} {exts : List Extent} {entryShared shared : Nat → Prop}
    {st st' : Vsa.While.St} {d env : Nat} {er : Expr} {vl vr : Value}
    {cost maxRequest reserve : Nat}
    {sp ret dst node interp operand v8 v9 v18 : BitVec 64}
    {m0 : Mem} {before called : Config}
    {FirstOwned : (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    {firstWrites : Nat → Prop}
    (staged : BinaryRightStaged gpre N A SL middleF middleC st d env er
      sp ret dst node interp operand v8 v9 v18 before called)
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (data : AllocatorResultAt M N entryShared (cost + reserve) st.store
      [(((sp - 1088#64) + 120#64).toNat, vl)] m0
      middleF middleC alloc exts shared before.σ.mem)
    (first : ReturnRepr N A entryF entryC middleF middleC nf nc st.store
      [(((sp - 1088#64) + 120#64).toNat, vl)] FirstOwned firstWrites before.σ.mem)
    (ast : ExprReprWithin before.σ.mem shared operand.toNat er)
    (gp : before.σ.regs.get? .x3 = some gpv)
    (ih : EvalAllocatorIH st d env er st' vr cost maxRequest)
    (lowered : (sp - 1088#64).toNat = sp.toNat - 1088)
    (ram : (sp - 1088#64).toNat + 1056 ≤ 0x100000000)
    (hsizeF : nf ≤ st.store.frames.size) (hsizeC : nc ≤ st.store.closures.size)
    (hbound : ValueClosuresBounded st.store.closures.size vl) :
    ∃ after, Steps before after ∧
      ReturnedWith
        (SubEvalReturn (fun R => called.σ.regs.get? R) N A SL middleF middleC
          st.store.frames.size st.store.closures.size st' vr sp ret dst
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12))
          0x8000351c#64 v8 v9 v18 called.σ.mem)
        (BinaryAllocatorReturnData N M entryF entryC nf nc entryShared reserve
          st' vl vr (sp - 1088#64) m0) after :=
  staged.bind_allocator_at L hrequest data first ast gp (ih.at N) lowered ram
    hsizeF hsizeC hbound

#print axioms BinaryRightStaged.bind_allocator_at
#print axioms BinaryRightStaged.bind_allocator

end Vsa.Sim
