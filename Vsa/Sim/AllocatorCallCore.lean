import Vsa.Sim.JalPreCore
import Vsa.Sim.EvalAllocatorCall

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- Execute the owned child at the actual call prefix's selected witnesses. -/
theorem JalPreCore.call_allocator_at
    {gpre : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    {cost maxRequest reserve : Nat}
    {callPC retPC : BitVec 64} {jalImm : BitVec 21}
    {sp ret dst childDst interp operand v8 v9 v18 : BitVec 64}
    {out : Array String} {mcall : Mem} {called : Config}
    (core : JalPreCore e called st d env gpre N A SL phiF phiC callPC retPC jalImm
      sp ret dst childDst interp operand v8 v9 v18 out mcall)
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve)
      st.store mcall)
    (ast : ExprReprWithin mcall shared operand.toNat e)
    (gp : gpre .x3 = some gpv)
    (ih : EvalAllocatorAt N st d env e st' v cost maxRequest) :
    ∃ after, Steps called after ∧
      ReturnedWith
        (SubEvalReturn gpre N A SL phiF phiC st.store.frames.size st.store.closures.size
          st' v sp ret dst childDst retPC v8 v9 v18 mcall)
        (EvalAllocatorCallData N M phiF phiC st.store.frames.size st.store.closures.size
          shared reserve st' v childDst.toNat mcall) after := by
  obtain ⟨envValid, target, link, aligned, site, pre⟩ := core
  exact armTail_rec_allocator_at gpre N M phiF phiC alloc exts shared st st' d env e v
    cost maxRequest reserve callPC retPC jalImm sp ret dst childDst interp operand
    v8 v9 v18 out mcall target link aligned envValid site L hrequest allocator ast gp ih
    called pre

/-- Invoke the owned child at the fixed witnesses selected by its actual call prefix. -/
theorem JalPreCore.call_allocator
    {gpre : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st st' : Vsa.While.St} {d env : Nat} {e : Expr} {v : Value}
    {cost maxRequest reserve : Nat}
    {callPC retPC : BitVec 64} {jalImm : BitVec 21}
    {sp ret dst childDst interp operand v8 v9 v18 : BitVec 64}
    {out : Array String} {mcall : Mem} {called : Config}
    (core : JalPreCore e called st d env gpre N A SL phiF phiC callPC retPC jalImm
      sp ret dst childDst interp operand v8 v9 v18 out mcall)
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : maxRequest ≤ maxReq)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (cost + reserve)
      st.store mcall)
    (ast : ExprReprWithin mcall shared operand.toNat e)
    (gp : gpre .x3 = some gpv)
    (ih : EvalAllocatorIH st d env e st' v cost maxRequest) :
    ∃ after, Steps called after ∧
      ReturnedWith
        (SubEvalReturn gpre N A SL phiF phiC st.store.frames.size st.store.closures.size
          st' v sp ret dst childDst retPC v8 v9 v18 mcall)
        (EvalAllocatorCallData N M phiF phiC st.store.frames.size st.store.closures.size
          shared reserve st' v childDst.toNat mcall) after :=
  core.call_allocator_at L hrequest allocator ast gp (ih.at N)

/-- Retain the same return while composing the prefix's shared-memory agreement. -/
theorem EvalAllocatorCallData.rebase
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {nf nc : Nat} {shared : Nat → Prop} {reserve : Nat}
    {st : Vsa.While.St} {v : Value} {dst : Nat} {m0 m1 : Mem} {after : Config}
    (result : EvalAllocatorCallData N M phiF phiC nf nc shared reserve st v dst m1 after)
    (agreement : AgreeP shared m0 m1) :
    EvalAllocatorCallData N M phiF phiC nf nc shared reserve st v dst m0 after := by
  obtain ⟨resultF, resultC, represented⟩ := result.repr.selected
  exact
    { repr := ⟨resultF, resultC, represented.withOwnership
        (represented.owned.rebase (fun _ h => h) agreement)⟩
      gp := result.gp }

#print axioms JalPreCore.call_allocator_at
#print axioms JalPreCore.call_allocator
#print axioms EvalAllocatorCallData.rebase

end Vsa.Sim
