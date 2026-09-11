import Vsa.Sim.ExecSeqAllocatorAt
import Vsa.Sim.ExecAllocatorAt
import Vsa.Sim.SeqClosureNormalContinue
import Vsa.Sim.SeqClosureNormalReadback
import Vsa.While.StoreBodiesBoundPreservation

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open RuntimeOwnership

/-- Loop state retained at the actual closure-body statement call. The dispatch
supplies the saved body and ghost registers; owned AST reads supply the suffix. -/
structure SeqClosureContinueCarrier
    (g gExec : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (phiF : Addr → Nat) (shared : Nat → Prop)
    (d env : Nat) (sp aRet body base interp : BitVec 64) (index count : Nat)
    (ss : List Stmt) (m0 mCall : Mem) : Prop
    extends SeqClosureRetCarrier g gExec A SL sp aRet m0 mCall where
  indexReg : gExec .x8 = some (BitVec.ofNat 64 index)
  interpReg : gExec .x18 = some interp
  envReg : gExec .x19 = some (BitVec.ofNat 64 (phiF env))
  retSlot : aRet = sp + 144#64
  remaining : index + 1 + ss.length = count
  nonempty : ss ≠ []
  countBound : count < 2^31
  savedBody : read64 mCall sp.toNat = some body.toNat
  bodyBase : read64 mCall (body.toNat + 8) = some base.toNat
  baseCovered : Covers shared (body.toNat + 8) 8
  bodyCount : read32 mCall (body.toNat + 16) = some count
  countCovered : Covers shared (body.toNat + 16) 4
  suffix : SeqSuffixOwned mCall shared SL A sp aRet d
    (base.toNat + 8 * (index + 1)) ss
  spLo : 0x80000000 ≤ sp.toNat
  spHi : sp.toNat + 8 ≤ 0x100000000
  spWin : tohostAddr + 8 ≤ sp.toNat
  spAlign : sp.toNat % 8 = 0
  savedOffRet : sp.toNat + 8 ≤ aRet.toNat
  bodyLo : 0x80000000 ≤ body.toNat
  bodyHi : body.toNat + 20 ≤ 0x100000000
  bodyWin : tohostAddr + 8 ≤ body.toNat + 16
  bodyAlign : body.toNat % 4 = 0
  spill9 : ∃ v, gExec .x9 = some v
  spill20 : ∃ v, gExec .x20 = some v
  spill21 : ∃ v, gExec .x21 = some v

/-- Run the reflected back edge after an owned normal child return. All tail
reads, store facts, and allocation credit refer to that same execution. -/
theorem seqClosureAllocatorContinue_of_return
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {shared : Nat → Prop} {reserve d env : Nat}
    {st st' : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet body base interp : BitVec 64} {index count : Nat} {m0 mCall : Mem}
    {cfg : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (h : SeqClosureContinueCarrier g gExec A SL phiF shared d env
      sp aRet body base interp index count ss m0 mCall)
    (source : ExecS st d env s st' .normal) (envValid : EnvValid st env)
    (bodies : Stmt.bodiesBound perCallBudget s = true)
    (storeBodies : StoreBodiesBound st.store perCallBudget)
    (stackOK : StackOK SL sp (176 + 1088))
    (stackRam : 0x80000000 ≤ SL.lo ∧ SL.hi ≤ 0x100000000)
    (stackWin : tohostAddr + 16 ≤ SL.lo)
    (support : EvalCallSupport mCall SL A sp)
    (beforeShared : AgreeP shared m0 mCall)
    (child : ExecAllocatorReturn gExec N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve
      st' .normal sp 0x80003378#64 aRet mCall cfg) :
    ∃ after, Steps cfg after ∧ ∃ resultF resultC alloc exts returnedShared,
      SeqAllocatorContinueAt .closureBody g N M phiF phiC resultF resultC
        st.store.frames.size st.store.closures.size alloc exts shared returnedShared
        reserve st' d env ss sp aRet m0 after := by
  obtain ⟨resultF, resultC, repr⟩ := child.selected
  obtain ⟨alloc, exts, returnedShared, data⟩ := repr.owned.selected
  have readback := SeqClosureNormalReadback.of_exit h.toSeqClosureRetCarrier child.exit
    support h.savedBody h.savedOffRet h.bodyCount h.countCovered data.agreement
  have code := readback.code
  have saved := readback.savedBody
  have countRead := readback.bodyCount
  have baseRead : read64 cfg.σ.mem (body.toNat + 8) = some base.toNat :=
    (read64_agreeP data.agreement h.baseCovered).symm.trans h.bodyBase
  have tail := h.suffix.transport_execExit child.exit.1 child.exit.2.1
    data.agreement data.includes
  have pre : SeqClosureNormalContinuePre sp body index count cfg :=
    { good := child.exit.1.good
      tick := child.exit.1.tick
      pc := child.exit.1.pc
      minstret := child.exit.1.minstret
      status := child.exit.1.a0
      spReg := child.exit.1.spReg
      indexReg := (child.exit.1.frame .x8 (by decide)).trans h.indexReg
      more := by have := List.length_pos_iff.mpr h.nonempty; have := h.remaining; omega
      countBound := h.countBound
      savedBody := saved
      bodyCount := countRead
      code := code
      spLo := h.spLo, spHi := h.spHi, spWin := h.spWin, spAlign := h.spAlign
      bodyLo := h.bodyLo, bodyHi := h.bodyHi, bodyWin := h.bodyWin, bodyAlign := h.bodyAlign }
  obtain ⟨after, post, run⟩ := seqClosureNormalContinue_run pre
  have keep (R : Register) (hR : ExecSeqFrameReg .closureBody R) :
      after.σ.regs.get? R = gExec R :=
    (run.frame.regs.eq R (by
      simp [seqClosureNormalContinueEffect, seqClosureNormalKeep, hR.1.1, hR.2])).trans
      (child.exit.1.frame R hR.1)
  have environment : resultF env = phiF env := repr.frames env envValid
  have envReg : after.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 (resultF env)) := by
    rw [environment]
    exact (keep .x19 (by unfold ExecSeqFrameReg; decide)).trans h.envReg
  have interpReg : after.σ.regs.get? Register.x18 = some interp :=
    (keep .x18 (by unfold ExecSeqFrameReg; decide)).trans h.interpReg
  have reachedTail : SeqSuffixOwned after.σ.mem returnedShared SL A sp aRet d
      (base.toNat + 8 * (index + 1)) ss := by rw [post.mem]; exact tail
  have baseRead' : read64 after.σ.mem (body.toNat + 8) = some base.toNat := by
    rw [post.mem]; exact baseRead
  have allocator : RuntimeAllocatorState M N resultF resultC alloc exts returnedShared
      reserve st'.store after.σ.mem := by rw [post.mem]; exact data.allocator
  have survives : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → after.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A resultF resultC st'.store :=
    fun m' hm => ((allocator.runtime L).after_stack hm).repr
  have ready : ExecSeqLoopReady .closureBody N A SL resultF resultC
      st' d env ss sp aRet after :=
    { env_valid := envValid.mono (execS_store_mono source).1
      code := by rw [post.mem]; exact code
      cursor := ⟨body, base, index + 1, count, post.bodyReg, post.indexReg, envReg,
        post.spReg, h.retSlot, baseRead', by rw [post.mem]; exact countRead,
        h.remaining, h.countBound, reachedTail.ground.array⟩
      head_ground := by
        cases ss with
        | nil => exact False.elim (h.nonempty rfl)
        | cons s' ss' =>
          obtain ⟨p, cell, ground⟩ := reachedTail.head
          have hp : p < 2^64 := read64_lt_eg4 _ _ _ cell.read
          refine ⟨BitVec.ofNat 64 p, ?_, ?_, ⟨interp, interpReg, envReg, h.retSlot⟩,
            ?_, stackOK, ground.stackBudget, ground.bodies,
            StoreBodiesBound.afterExecS source bodies storeBodies⟩
          · exact ⟨body, base, index + 1, post.bodyReg, post.indexReg, baseRead',
              by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using cell.read⟩
          · simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using ground.stmt
          · simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp] using ground.ground
      store_survives := survives
      stack_ram := stackRam
      stack_win := stackWin }
  refine ⟨after, run.steps, resultF, resultC, alloc, exts, returnedShared,
    { entry :=
        { entry :=
            { good := post.good, tick := post.tick
              pc := by cases ss with
                | nil => exact False.elim (h.nonempty rfl)
                | cons _ _ => exact post.pc
              store := allocator.repr, store_survives := survives
              out := by simpa [OutRepr, output, post.output] using child.exit.1.out
              mem := rfl, ready := fun _ => ready
              empty_status := fun hempty => False.elim (h.nonempty hempty)
              frame := fun R hR => (keep R hR).trans (h.frame R hR)
              minstret := post.minstret }
          allocator := allocator
          suffix := fun _ => ⟨_, .closureBody post.bodyReg post.indexReg baseRead', reachedTail⟩
          interpResources := by intro impossible; cases impossible
          blockResources := by intro impossible; cases impossible
          closureResources := fun _ _ => ⟨body, post.bodyReg,
            { baseCovered := fun k hk => data.includes _ (h.baseCovered k hk)
              countCovered := fun k hk => data.includes _ (h.countCovered k hk)
              arenaBelow := h.childFrame.arenaBelow
              bodyLo := h.bodyLo, bodyHi := h.bodyHi
              bodyWin := h.bodyWin, bodyAlign := h.bodyAlign
              spill9 := h.spill9.imp (fun _ hv =>
                (keep .x9 (by unfold ExecSeqFrameReg; decide)).trans hv)
              spill20 := h.spill20.imp (fun _ hv =>
                (keep .x20 (by unfold ExecSeqFrameReg; decide)).trans hv)
              spill21 := h.spill21.imp (fun _ hv =>
                (keep .x21 (by unfold ExecSeqFrameReg; decide)).trans hv) }⟩
          gp := (run.frame.regs.eq .x3 (by
            unfold seqClosureNormalContinueEffect seqClosureNormalKeep; decide)).trans child.gp }
      frames := repr.frames, closures := repr.closures, includes := data.includes
      agreement := ?_, memFrame := ?_, highStack := ?_, presence := ?_ }⟩
  · intro k hk
    rw [post.mem]
    exact (beforeShared k hk).trans (data.agreement k hk)
  · intro k hs hA
    rw [post.mem]
    have hsp := h.spLe
    have hr := h.retInStack
    exact ((child.exit.1.memFrame k (by omega) hA).resolve_left (by omega)).trans
      (h.memFrame k hs hA)
  · rw [post.mem]
    exact h.highStack.trans (closureBodyStackFrame_of_execExitD h.childFrame child.exit)
  · rw [post.mem]
    exact h.memExtends.trans child.exit.2.1

#print axioms seqClosureAllocatorContinue_of_return

/-- Execute the owned statement and its back edge as one machine run. -/
theorem seqClosureAllocatorContinue
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve d env : Nat}
    {st st' : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet body base interp aStmt aEnv : BitVec 64} {index count : Nat} {m0 : Mem}
    {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (source : ExecS st d env s st' .normal)
    (ih : ExecAllocatorAt N st d env s st' .normal cost request)
    (entry : ExecAllocatorEntry gExec N M phiF phiC alloc exts shared (cost + reserve)
      st d env s sp 0x80003378#64 interp aStmt aEnv aRet before.σ.mem before)
    (h : SeqClosureContinueCarrier g gExec A SL phiF shared d env
      sp aRet body base interp index count ss m0 before.σ.mem)
    (beforeShared : AgreeP shared m0 before.σ.mem) :
    ∃ after, Steps before after ∧ ∃ resultF resultC resultAlloc resultExts returnedShared,
      SeqAllocatorContinueAt .closureBody g N M phiF phiC resultF resultC
        st.store.frames.size st.store.closures.size resultAlloc resultExts shared returnedShared
        reserve st' d env ss sp aRet m0 after := by
  obtain ⟨returned, steps, child⟩ := ih.run gExec A SL gpv headroom maxReq M L hrequest
    phiF phiC alloc exts shared reserve sp 0x80003378#64 interp aStmt aEnv aRet
    before.σ.mem before entry
  obtain ⟨after, resume, resultF, resultC, resultAlloc, resultExts, returnedShared, post⟩ :=
    seqClosureAllocatorContinue_of_return L h source entry.entry.env_valid
      entry.entry.stmt_bodies entry.entry.store_bodies entry.entry.stackOK
      entry.entry.stack_ram entry.entry.stack_win entry.entry.ground.eval_call beforeShared child
  exact ⟨after, steps.trans resume, resultF, resultC, resultAlloc, resultExts, returnedShared, post⟩

#print axioms seqClosureAllocatorContinue

/-- Complete a normally returning child, the concrete back edge, and the owned tail.
The two source suppliers choose independent costs and request ceilings. -/
theorem seqClosureAllocatorConsNormal
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {headCost tailCost headRequest tailRequest reserve d env : Nat}
    {st stMid st' : Vsa.While.St} {s : Stmt} {ss : List Stmt} {status : Status}
    {sp aRet body base interp aStmt aEnv : BitVec 64} {index count : Nat} {m0 : Mem}
    {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (hrequest : max headRequest tailRequest ≤ maxReq)
    (source : ExecS st d env s stMid .normal)
    (head : ExecAllocatorAt N st d env s stMid .normal headCost headRequest)
    (tail : ExecSeqAllocatorAt N .closureBody stMid d env ss st' status tailCost tailRequest)
    (entry : ExecAllocatorEntry gExec N M phiF phiC alloc exts shared
      (headCost + tailCost + reserve) st d env s sp 0x80003378#64
      interp aStmt aEnv aRet before.σ.mem before)
    (h : SeqClosureContinueCarrier g gExec A SL phiF shared d env
      sp aRet body base interp index count ss m0 before.σ.mem)
    (beforeShared : AgreeP shared m0 before.σ.mem) :
    ∃ after, Steps before after ∧
      ExecSeqAllocatorReturn .closureBody g N M phiF phiC
        st.store.frames.size st.store.closures.size shared reserve st' status sp aRet m0 after := by
  have entry' : ExecAllocatorEntry gExec N M phiF phiC alloc exts shared
      (headCost + (tailCost + reserve)) st d env s sp 0x80003378#64
      interp aStmt aEnv aRet before.σ.mem before := by
    simpa only [Nat.add_assoc] using entry
  obtain ⟨middle, headSteps, resultF, resultC, resultAlloc, resultExts, returnedShared, post⟩ :=
    seqClosureAllocatorContinue L (Nat.le_trans (Nat.le_max_left _ _) hrequest)
      source head entry' h beforeShared
  have growth := execS_store_mono source
  obtain ⟨after, tailSteps, result⟩ := post.run_tail L
    (Nat.le_trans (Nat.le_max_right _ _) hrequest) growth.1 growth.2 tail
  exact ⟨after, headSteps.trans tailSteps, result⟩

#print axioms seqClosureAllocatorConsNormal

end Vsa.Sim
