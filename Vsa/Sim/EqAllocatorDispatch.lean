import Vsa.Sim.EqCaseEntry
import Vsa.Sim.EqDispatchOwned
import Vsa.Sim.BinaryAllocatorEntry

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- Equality's stack copies preserve the selected allocator and caller reserve. -/
theorem EqDispatchOperands.allocator
    {N : NativeAddrs} {phiF phiC : Addr → Nat} {shared entryShared : Nat → Prop}
    {base : BitVec 64} {vl vr : Value} {m0 m : Mem} {c : Config}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq credits : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {store : Store}
    {alloc : Allocations} {exts : List Extent} {results : List (Nat × Value)}
    (h : EqDispatchOperands N phiC shared base vl vr m c)
    (data : AllocatorResultAt M N entryShared credits store results m0
      phiF phiC alloc exts shared m)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (low : SL.lo ≤ base.toNat) (high : base.toNat + 88 ≤ SL.hi) :
    AllocatorResultAt M N entryShared credits store
      [((base + 0x40#64).toNat, vl), ((base + 0x20#64).toNat, vr)] m0
      phiF phiC alloc exts shared c.σ.mem := by
  refine
    { allocator := data.allocator.after_stack L (fun k hk =>
        (h.outside k (by omega)).symm)
      includes := data.includes
      values := ?_
      agreement := fun k hk => (data.agreement k hk).trans
        (h.sharedAgreement k (data.includes k hk)) }
  intro a v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with left | right
  · cases left; exact h.leftOwned
  · cases right; exact h.rightOwned

/-- The actual helper-call endpoint retains the operand run and the copied store maps. -/
structure EqAllocatorDispatchAt
    (op : EqNeOp) (g gpre : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (nf nc : Nat) (shared : Nat → Prop) (reserve : Nat)
    (middle final : Vsa.While.St) (vl vr : Value)
    (sp ret dst node v8 v9 v18 v19 : BitVec 64) (m0 : Mem)
    (operands : Config) (lds : List (List (BitVec 8))) (c : Config) : Prop where
  frame : BinaryArmFrame g gpre sp node v8 v9 v18 v19
  head : BinaryAllocatorHeadReturn gpre N M phiF phiC nf nc shared reserve
    middle final vl vr sp ret dst v8 v9 v18 m0 operands
  dispatch : op.DispatchPost (sp - 1088#64) lds operands.σ.mem operands.σ.sailOutput
    (fun R => operands.σ.regs.get? R) c
  selected : ∃ resultF resultC,
    ReturnRepr N A phiF phiC resultF resultC nf nc final.store
      [(((sp - 1088#64) + 0x40#64).toNat, vl), (((sp - 1088#64) + 0x20#64).toNat, vr)]
      (AllocatorResult M N shared reserve final.store
        [(((sp - 1088#64) + 0x40#64).toNat, vl), (((sp - 1088#64) + 0x20#64).toNat, vr)] m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) c.σ.mem
  presence : MemExtends operands.σ.mem c.σ.mem
  outside : ∀ k, k < (sp - 1088#64).toNat + 32 ∨ (sp - 1088#64).toNat + 88 ≤ k →
    c.σ.mem[k]? = operands.σ.mem[k]?

/-- Execute equality's owned children and operand copies at the current native addresses. -/
theorem evalEqAllocatorDispatch_at
    (op : EqNeOp)
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    {costL costR maxRequest reserve : Nat} {sp ret dst node interp : BitVec 64}
    {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (request : maxRequest ≤ maxReq)
    (leftSem : EvalE st d env el middle vl) (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorAt N st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorAt N middle d env er final vr costR maxRequest)
    (entry : EvalAllocatorEntry g N M phiF phiC alloc exts shared
      (costL + (costR + reserve)) st d env (.binary op.operator el er)
      sp ret dst interp node m0 before) :
    ∃ after operands gpre v8 v9 v18 v19 lds, Steps before after ∧
      EqAllocatorDispatchAt op g gpre N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve middle final vl vr sp ret dst node v8 v9 v18 v19 m0 operands lds after := by
  obtain ⟨operands, headSteps, returned⟩ :=
    evalBinaryAllocatorOperands_at L request leftSem bounded leftIH rightIH before entry
  obtain ⟨gpre, v8, v9, v18, v19, frame, head⟩ := returned.selected
  obtain ⟨resultF, resultC, repr⟩ := head.owned.selected
  obtain ⟨resultAlloc, resultExts, resultShared, data⟩ := repr.owned.selected
  have input := entry.entry.eqDispatchInput op frame head.ordinary
  obtain ⟨after, lds, dispatchSteps, dispatch⟩ :=
    evalEqNeChain_dispatch_of_twoSubReturn op gpre N A SL phiF phiC
      st.store.frames.size st.store.closures.size middle final vl vr sp ret dst node
      v8 v9 v18 m0 operands head.ordinary head.machine.toBinaryReturnLoads input
  obtain ⟨leftNode, rightNode, geometry⟩ := entry.entry.binaryExtras
  have room := geometry.sproom
  have high := geometry.spSLhi
  have ram := geometry.SLhiRam
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1088 ≤ sp.toNat; omega)
  have copies := dispatch.readback.owned
    (by rw [lowered]; omega) (by rw [lowered]; omega) (by rw [lowered]; omega)
    data.allocator.geometry
    (repr.values _ _ (List.mem_cons_self ..))
    (repr.values _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    (data.values _ _ (List.mem_cons_self ..))
    (data.values _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have advanced := copies.allocator data L (by rw [lowered]; omega) (by rw [lowered]; omega)
  have coherent := advanced.coherent L repr.frames repr.closures (by
    intro a v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with left | right
    · cases left; exact copies.left
    · cases right; exact copies.right)
  exact ⟨after, operands, gpre, v8, v9, v18, v19, lds,
    headSteps.trans dispatchSteps,
    { frame := frame, head := head, dispatch := dispatch
      selected := ⟨resultF, resultC, coherent⟩
      presence := copies.presence, outside := copies.outside }⟩

/-- Execute both children and either equality dispatch with coherent owned operands. -/
theorem evalEqAllocatorDispatch
    (op : EqNeOp)
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    {costL costR maxRequest reserve : Nat} {sp ret dst node interp : BitVec 64}
    {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (request : maxRequest ≤ maxReq)
    (leftSem : EvalE st d env el middle vl) (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorIH st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorIH middle d env er final vr costR maxRequest)
    (entry : EvalAllocatorEntry g N M phiF phiC alloc exts shared
      (costL + (costR + reserve)) st d env (.binary op.operator el er)
      sp ret dst interp node m0 before) :
    ∃ after operands gpre v8 v9 v18 v19 lds, Steps before after ∧
      EqAllocatorDispatchAt op g gpre N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve middle final vl vr sp ret dst node v8 v9 v18 v19 m0 operands lds after :=
  evalEqAllocatorDispatch_at op L request leftSem bounded (leftIH.at N) (rightIH.at N) entry

#print axioms EqDispatchOperands.allocator
#print axioms evalEqAllocatorDispatch_at
#print axioms evalEqAllocatorDispatch

end Vsa.Sim
