import Vsa.Sim.SeqClosureAllocatorReturn

namespace Vsa.Sim.SeqClosureDispatch

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The final normal child takes the reflected sequence exit and retains its reserve. -/
theorem consFinal
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve d env : Nat}
    {st st' : Vsa.While.St} {s : Stmt}
    {body base sp aRet interp : BitVec 64} {index count : Nat} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (head : ExecAllocatorAt N st d env s st' .normal cost request)
    (entry : ExecSeqAllocatorEntry .closureBody g N M phiF phiC alloc exts shared
      (cost + reserve) st d env [s] sp aRet m0 before)
    (I : LoopInput N A SL phiF shared st d env s [] body base sp aRet interp index count before) :
    ∃ after, Steps before after ∧
      ExecSeqAllocatorReturn .closureBody g N M phiF phiC st.store.frames.size
        st.store.closures.size shared reserve st' .normal sp aRet m0 after := by
  obtain ⟨called, stmt, dispatch, post⟩ := owned L entry I.toInput
  obtain ⟨returned, steps, child⟩ := head.run called.σ.regs.get? A SL gpv headroom maxReq M L
    hrequest phiF phiC alloc exts shared reserve sp 0x80003378#64 interp stmt
    (BitVec.ofNat 64 (phiF env)) aRet called.σ.mem called post.entry
  obtain ⟨resultF, resultC, repr⟩ := child.selected
  have carrier := post.returnCarrier entry I.toInput I.arenaBelow
  have ret := I.toInput.retAddress
  have countRead := (read32_agreeP post.agreement I.countCovered).symm.trans I.bodyCount
  have readback := SeqClosureNormalReadback.of_exit carrier child.exit
    post.entry.entry.ground.eval_call post.dispatch.savedBody (by omega)
    countRead I.countCovered repr.owned.shared_agree
  obtain ⟨_, _, _, _, _, indexReg, _, _, _, _⟩ := post.dispatch.args
  have finalData : SeqClosureNormalFinalData g called.σ.regs.get? A SL sp aRet body
      index count m0 called.σ.mem :=
    { toSeqClosureRetCarrier := carrier
      indexReg := indexReg, last := by simpa using I.remaining, countBound := I.countBound
      spLo := I.geometry.stackLo, spHi := I.geometry.stackHi
      spWin := by have := I.geometry.stackHtif; omega
      spAlign := I.geometry.stackAlign
      bodyLo := I.bodyLo, bodyHi := I.bodyHi, bodyWin := I.bodyWin, bodyAlign := I.bodyAlign }
  obtain ⟨after, resume, result⟩ := seqClosureNormalExitRun finalData returned child.exit
    readback.code readback.savedBody readback.bodyCount
  have sharedBefore : AgreeP shared m0 called.σ.mem := by
    rw [← entry.entry.mem]
    exact post.agreement
  have represented : ReturnRepr N A phiF phiC resultF resultC
      st.store.frames.size st.store.closures.size st'.store (statusResults aRet.toNat .normal)
      (AllocatorResult M N shared reserve st'.store (statusResults aRet.toNat .normal) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem := by
    rw [result.memory]
    exact { repr with owned := repr.owned.rebase (fun _ hv => hv) sharedBefore }
  exact ⟨after, dispatch.trans (steps.trans resume),
    { exit := result.exit
      selected := ⟨resultF, resultC, represented⟩
      gp := (result.exit.frame .x3 (by unfold ExecSeqFrameReg; decide)).trans
        ((entry.entry.frame .x3 (by unfold ExecSeqFrameReg; decide)).symm.trans entry.gp) }⟩

#print axioms consFinal

end Vsa.Sim.SeqClosureDispatch
