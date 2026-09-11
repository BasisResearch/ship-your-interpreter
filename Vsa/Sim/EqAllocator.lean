import Vsa.Sim.EqOwnedFront
import Vsa.Sim.EqBoxEntry
import Vsa.Sim.EqBoxFinish

open LeanRV64DExecutable Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc
open Vsa.Machine Vsa.Logic Vsa.Sim.Code

namespace Vsa.Sim
open RuntimeOwnership

/-- Execute equality and its outer return with recursive children at fixed native addresses. -/
theorem evalEqAllocator_at (op : EqNeOp)
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    {costL costR maxRequest reserve : Nat} {sp ret dst node interp : BitVec 64} {m0 : Mem}
    (L : AllocLedger A SL gpv headroom maxReq M) (request : maxRequest ≤ maxReq)
    (native : ∀ f h, N.addr f = N.addr h → f = h)
    (leftSem : EvalE st d env el middle vl) (rightSem : EvalE middle d env er final vr)
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorAt N st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorAt N middle d env er final vr costR maxRequest) :
    Triple (EvalAllocatorEntry g N M phiF phiC alloc exts shared
      (costL + (costR + reserve)) st d env (.binary op.operator el er)
      sp ret dst interp node m0)
      (EvalAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve final (.bool (op.result vl vr)) sp ret dst m0) := by
  intro before entry
  obtain ⟨dispatch, operands, gpre, v8, v9, v18, v19, lds, dispatchSteps, reached⟩ :=
    evalEqAllocatorDispatch_at op L request leftSem bounded leftIH rightIH entry
  obtain ⟨resultF, resultC, repr⟩ := reached.selected
  obtain ⟨resultAlloc, resultExts, resultShared, data⟩ := repr.owned.selected
  obtain ⟨leftNode, rightNode, geometry⟩ := entry.entry.binaryExtras
  have room := geometry.sproom
  have high := geometry.spSLhi
  have ram := geometry.SLhiRam
  have aligned := geometry.sp16
  have lowered : (sp - 1088#64).toNat = sp.toNat - 1088 :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 1088 ≤ sp.toNat; omega)
  have copied : EqDispatchOperands N resultC resultShared (sp - 1088#64) vl vr
      operands.σ.mem dispatch :=
    { left := repr.values _ _ (List.mem_cons_self ..)
      right := repr.values _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      leftOwned := data.values _ _ (List.mem_cons_self ..)
      rightOwned := data.values _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      sharedAgreement := fun k hk => (reached.outside k (by
        have stack := data.allocator.geometry.stack k hk
        rw [lowered]; omega)).symm
      presence := reached.presence
      outside := reached.outside }
  have image := copied.image (entry.entry.binaryReturnImage reached.head.ordinary)
    (by rw [lowered]; omega) (by rw [lowered]; omega)
  have leftBound := storeClosuresBounded_mutual.onEvalE leftSem bounded
  have rightBound := storeClosuresBounded_mutual.onEvalE rightSem leftBound.1
  have identity := ValueEqualityIdentity.of_store repr.storeRepr
    (ValueClosuresBounded.mono (evalE_store_mono rightSem).2 leftBound.2)
    rightBound.2 (fun f h _ _ => native f h)
  have parts := TwoSubReturn.destruct gpre N A SL phiF phiC st.store.frames.size
    st.store.closures.size middle final vl vr sp ret dst v8 v9 v18 m0 operands reached.head.ordinary
  have machine := reached.dispatch.machine
  have dstReg : dispatch.σ.regs.get? Register.x9 = some dst :=
    (machine.frame .x9 (by decide) (by decide)).trans parts.p5
  have front := op.ownedFront machine copied data.allocator.geometry image identity
    (by rw [lowered]; omega) (by rw [lowered]; omega)
    entry.entry.stack_ram.1 ram entry.entry.stack_win (by rw [lowered]; omega) dstReg
  obtain ⟨compared, compareSteps, returned⟩ :=
    blockC_eqne_front_present (fun R => dispatch.σ.regs.get? R) N resultC (sp - 1088#64) dst
      vl vr op.returnPC op.callPC op.callImm dispatch.σ.mem operands.σ.sailOutput dispatch front
  have box := EqNeBoxPre.of_entry entry.entry reached.frame reached.head.ordinary
    reached.head.machine.toBinaryReturnMemory image reached.presence reached.outside repr.survives
  have collapse : ∀ R, AbiPreservedNoise R → (Register.x8 == R) = false →
      (Register.x9 == R) = false → (Register.x18 == R) = false →
      (Register.x2 == R) = false → (Register.x19 == R) = false → dispatch.σ.regs.get? R = g R := by
    intro R hR h8 h9 h18 h2 h19
    exact (machine.frame R hR h8).trans
      ((parts.p9 R hR h19).trans (reached.frame.bridge R hR h8 h9 h18 h2))
  obtain ⟨preReturn, mpre, tailF, tailC, boxed⟩ := op.finishBox returned box collapse
  obtain ⟨after, returnSteps, finalReturn⟩ :=
    blockD_v_rec_coherent g N A SL tailF tailC final (.bool (op.result vl vr))
      sp ret dst v8 v9 v18 operands.σ.sailOutput m0
      (fun _ _ memory => MemFootprint (eqneCellFoot sp.toNat dst.toNat) dispatch.σ.mem memory)
      preReturn ⟨mpre, boxed.pre, boxed.footprint⟩
  have agreement : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → dispatch.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply (finalReturn.extra.owned.agree k ?_).symm
    unfold eqneCellFoot resultSlot
    have resultStack := geometry.sret_inSL
    omega
  have resultData : AllocatorResultAt M N shared reserve final.store
      [(dst.toNat, .bool (op.result vl vr))] m0 resultF resultC
      resultAlloc resultExts resultShared after.σ.mem :=
    { allocator := data.allocator.after_stack L agreement
      includes := data.includes
      values := fun a v hv => by
        have heq : (a, v) = (dst.toNat, .bool (op.result vl vr)) := List.mem_singleton.mp hv
        cases heq
        trivial
      agreement := fun k hk => (data.agreement k hk).trans
        (agreement k ((data.allocator.runtime L).shared_off_stack (data.includes k hk))) }
  have value : ValueRepr after.σ.mem N resultC dst.toNat (.bool (op.result vl vr)) :=
    valueRepr_phic_mono (size := 0) (by trivial) (by intro k hk; omega)
      (finalReturn.extra.values _ _ (List.mem_singleton_self _))
  have coherent := resultData.coherent L repr.frames repr.closures (by
    intro a v hv
    have heq : (a, v) = (dst.toNat, .bool (op.result vl vr)) := List.mem_singleton.mp hv
    cases heq
    exact value)
  have result := finalReturn.result.withReturnRepr coherent
  have gp : after.σ.regs.get? Register.x3 = some gpv :=
    (result.exit.1.frame .x3 (by decide)).trans
      ((entry.entry.frame .x3 (by decide)).symm.trans entry.gp)
  exact ⟨after, dispatchSteps.trans (compareSteps.trans (boxed.run.trans returnSteps)), result, gp⟩

/-- Execute an owned equality or inequality case through its outer return.
The fixed boundary supplies native identity through
`LayoutInstance.InterpRunPhysicalFacts.native_injective`. -/
theorem evalEqAllocator (op : EqNeOp)
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {vl vr : Value}
    {costL costR maxRequest reserve : Nat} {sp ret dst node interp : BitVec 64} {m0 : Mem}
    (L : AllocLedger A SL gpv headroom maxReq M) (request : maxRequest ≤ maxReq)
    (native : ∀ f h, N.addr f = N.addr h → f = h)
    (leftSem : EvalE st d env el middle vl) (rightSem : EvalE middle d env er final vr)
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorIH st d env el middle vl costL maxRequest)
    (rightIH : EvalAllocatorIH middle d env er final vr costR maxRequest) :
    Triple (EvalAllocatorEntry g N M phiF phiC alloc exts shared
      (costL + (costR + reserve)) st d env (.binary op.operator el er)
      sp ret dst interp node m0)
      (EvalAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve final (.bool (op.result vl vr)) sp ret dst m0) :=
  evalEqAllocator_at op L request native leftSem rightSem bounded (leftIH.at N) (rightIH.at N)

#print axioms evalEqAllocator_at
#print axioms evalEqAllocator

end Vsa.Sim
