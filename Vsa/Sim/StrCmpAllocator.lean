import Vsa.Sim.BinaryAllocatorEntry
import Vsa.Sim.StrCmpReadOperands
import Vsa.Sim.EvalAllocatorLiteral

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While Vsa.Machine Vsa.Logic

namespace Vsa.Sim
open RuntimeOwnership

/-- Execute a string comparison and its outer return with the children's allocator reserve. -/
theorem evalStrCmpAllocator (D : StrCmpOp) (C : D.Cert)
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {sl sr : String}
    {costL costR maxRequest reserve : Nat}
    {sp ret dst node interp : BitVec 64} {m0 : Mem}
    (L : AllocLedger A SL gpv headroom maxReq M) (request : maxRequest ≤ maxReq)
    (leftSem : EvalE st d env el middle (.str sl))
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorIH st d env el middle (.str sl) costL maxRequest)
    (rightIH : EvalAllocatorIH middle d env er final (.str sr) costR maxRequest) :
    Triple (EvalAllocatorEntry g N M phiF phiC alloc exts shared
      (costL + (costR + reserve)) st d env (.binary D.op el er) sp ret dst interp node m0)
      (EvalAllocatorReturn g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve final (.bool (D.bres sl sr)) sp ret dst m0) := by
  intro before entry
  obtain ⟨operands, headSteps, headReturn⟩ :=
    evalBinaryAllocatorOperands L request leftSem bounded leftIH rightIH before entry
  obtain ⟨gpre, v8, v9, v18, v19, frame, head⟩ := headReturn.selected
  obtain ⟨resultF, resultC, repr⟩ := head.owned.selected
  obtain ⟨resultAlloc, resultExts, resultShared, data⟩ := repr.owned.selected
  obtain ⟨leftNode, rightNode, geometry⟩ := entry.entry.binaryExtras
  have room := geometry.sproom
  have high := geometry.spSLhi
  have ram := geometry.SLhiRam
  have leftAddr : ((sp - 1088#64) + 120#64).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) (by omega)
  have rightAddr : ((sp - 1088#64) + 144#64).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) (by omega)
  have leftOwned := data.values _ _ (List.mem_cons_self ..)
  have rightOwned := data.values _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rw [leftAddr] at leftOwned
  rw [rightAddr] at rightOwned
  have regions := strCmpOperandsAt_of_readOwned data.allocator.geometry
    (by omega : SL.lo + 1088 ≤ sp.toNat) high leftOwned rightOwned
  have residual := strCmpResid_of_entry D C entry.entry frame head.ordinary regions
  have output : String.join operands.σ.sailOutput.toList = final.out :=
    (TwoSubReturn.destruct gpre N A SL phiF phiC st.store.frames.size st.store.closures.size
      middle final (.str sl) (.str sr) sp ret dst v8 v9 v18 m0 operands head.ordinary).p8
  have saved19 : gpre Register.x19 = some v19 :=
    (frame.bridge .x19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
      frame.saved19
  obtain ⟨preReturn, cellSteps, mpre, middleF, middleC, tailF, tailC,
    _frames, _closures, _tailFrames, _tailClosures, pre, footprint⟩ :=
    blockC_strcmp_footprint D C gpre g N A SL phiF phiC
      st.store.frames.size st.store.closures.size middle final sl sr sp ret dst node
      v8 v9 v18 v19 operands.σ.sailOutput m0 operands.σ.mem operands
      ⟨head.ordinary, residual, head.machine, output, rfl,
        frame.saved8, frame.saved9, frame.saved18, frame.savedSp, saved19,
        frame.saved19, frame.bridge, rfl⟩
  obtain ⟨after, returnSteps, returned⟩ :=
    blockD_v_rec_coherent g N A SL tailF tailC final (.bool (D.bres sl sr))
      sp ret dst v8 v9 v18 operands.σ.sailOutput m0
      (fun _ _ m => MemFootprint (strCmpCellFoot sp.toNat dst.toNat) operands.σ.mem m)
      preReturn ⟨mpre, pre, footprint⟩
  have agreement : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) →
      operands.σ.mem[k]? = after.σ.mem[k]? := by
    intro k hk
    apply (returned.extra.owned.agree k ?_).symm
    unfold strCmpCellFoot word8 resultSlot
    have dstStack := geometry.sret_inSL
    omega
  have resultData : AllocatorResultAt M N shared reserve final.store
      [(dst.toNat, .bool (D.bres sl sr))] m0 resultF resultC
      resultAlloc resultExts resultShared after.σ.mem :=
    { allocator := data.allocator.after_stack L agreement
      includes := data.includes
      values := fun a v hv => by
        have heq : (a, v) = (dst.toNat, .bool (D.bres sl sr)) := List.mem_singleton.mp hv
        cases heq
        trivial
      agreement := fun k hk => (data.agreement k hk).trans
        (agreement k ((data.allocator.runtime L).shared_off_stack (data.includes k hk))) }
  have value : ValueRepr after.σ.mem N resultC dst.toNat (.bool (D.bres sl sr)) :=
    valueRepr_phic_mono (size := 0) (by trivial) (by intro k hk; omega)
      (returned.extra.values _ _ (List.mem_singleton_self _))
  have coherent := resultData.coherent L repr.frames repr.closures (by
    intro a v hv
    have heq : (a, v) = (dst.toNat, .bool (D.bres sl sr)) := List.mem_singleton.mp hv
    cases heq
    exact value)
  have result := returned.result.withReturnRepr coherent
  have gp : after.σ.regs.get? Register.x3 = some gpv :=
    (result.exit.1.frame .x3 (by decide)).trans
      ((entry.entry.frame .x3 (by decide)).symm.trans entry.gp)
  exact ⟨after, headSteps.trans (cellSteps.trans returnSteps), result, gp⟩

#print axioms evalStrCmpAllocator

/-- A certified string comparison preserves every caller reserve after both children. -/
theorem evalAllocatorIH_strCmp (D : StrCmpOp) (C : D.Cert)
    {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {sl sr : String}
    {costL costR maxRequest : Nat}
    (leftSem : EvalE st d env el middle (.str sl))
    (bounded : StoreClosuresBounded st.store)
    (leftIH : EvalAllocatorIH st d env el middle (.str sl) costL maxRequest)
    (rightIH : EvalAllocatorIH middle d env er final (.str sr) costR maxRequest) :
    EvalAllocatorIH st d env (.binary D.op el er) final (.bool (D.bres sl sr))
      (costL + costR) maxRequest where
  run := by
    intro g N A SL gpv headroom maxReq M L request phiF phiC alloc exts shared reserve
      sp ret dst interp node m0 before entry
    have entry' : EvalAllocatorEntry g N M phiF phiC alloc exts shared
        (costL + (costR + reserve)) st d env (.binary D.op el er)
        sp ret dst interp node m0 before := by
      simpa only [Nat.add_assoc] using entry
    exact evalStrCmpAllocator D C L request leftSem bounded
      leftIH rightIH before entry'

#print axioms evalAllocatorIH_strCmp

section Comparisons

variable {st middle final : Vsa.While.St} {d env : Nat} {el er : Expr} {sl sr : String}
  {costL costR maxRequest : Nat}
  (leftSem : EvalE st d env el middle (.str sl))
  (bounded : StoreClosuresBounded st.store)
  (leftIH : EvalAllocatorIH st d env el middle (.str sl) costL maxRequest)
  (rightIH : EvalAllocatorIH middle d env er final (.str sr) costR maxRequest)

include leftSem bounded leftIH rightIH

/-- String `<` consumes both child suppliers and preserves every caller reserve. -/
theorem evalAllocatorIH_strLt :
    EvalAllocatorIH st d env (.binary .lt el er) final (.bool (sl < sr))
      (costL + costR) maxRequest :=
  evalAllocatorIH_strCmp strCmpLt strCmpLt_cert leftSem bounded leftIH rightIH

/-- String `≤` consumes both child suppliers and preserves every caller reserve. -/
theorem evalAllocatorIH_strLe :
    EvalAllocatorIH st d env (.binary .le el er) final (.bool (sl < sr || sl == sr))
      (costL + costR) maxRequest :=
  evalAllocatorIH_strCmp strCmpLe strCmpLe_cert leftSem bounded leftIH rightIH

/-- String `>` consumes both child suppliers and preserves every caller reserve. -/
theorem evalAllocatorIH_strGt :
    EvalAllocatorIH st d env (.binary .gt el er) final (.bool (sr < sl))
      (costL + costR) maxRequest :=
  evalAllocatorIH_strCmp strCmpGt strCmpGt_cert leftSem bounded leftIH rightIH

/-- String `≥` consumes both child suppliers and preserves every caller reserve. -/
theorem evalAllocatorIH_strGe :
    EvalAllocatorIH st d env (.binary .ge el er) final (.bool (sr < sl || sl == sr))
      (costL + costR) maxRequest :=
  evalAllocatorIH_strCmp strCmpGe strCmpGe_cert leftSem bounded leftIH rightIH

end Comparisons

#print axioms evalAllocatorIH_strLt
#print axioms evalAllocatorIH_strLe
#print axioms evalAllocatorIH_strGt
#print axioms evalAllocatorIH_strGe

/-- Comparing two string literals needs no child supplier and consumes no allocation credit. -/
theorem evalAllocatorIH_strCmp_literals (D : StrCmpOp) (C : D.Cert)
    (st : Vsa.While.St) (d env : Nat) (sl sr : String)
    (bounded : StoreClosuresBounded st.store) :
    EvalAllocatorIH st d env (.binary D.op (.str sl) (.str sr))
      st (.bool (D.bres sl sr)) 0 0 :=
  evalAllocatorIH_strCmp D C (EvalE.str st d env sl) bounded
    (evalAllocatorIH_str st d env sl) (evalAllocatorIH_str st d env sr)

#print axioms evalAllocatorIH_strCmp_literals

end Vsa.Sim
