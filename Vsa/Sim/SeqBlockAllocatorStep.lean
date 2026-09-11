import Vsa.Sim.SeqBlockLoopInput
import Vsa.Sim.SeqBlockAllocatorContinue

namespace Vsa.Sim.SeqBlockDispatch

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Dispatch retains the next owned suffix and every continuation resource. -/
theorem OwnedPost.carrier
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {block base sp aRet interp stmt : BitVec 64} {index count : Nat} {m0 : Mem}
    {before called : Config}
    (h : OwnedPost N M phiF phiC alloc exts shared credits st d env s ss
      block base sp aRet interp stmt index before called)
    (entry : ExecSeqAllocatorEntry .blockBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (I : LoopInput N A SL phiF shared st d env s ss block base sp aRet interp index count before)
    (nonempty : ss ≠ []) :
    SeqBlockContinueCarrier g called.σ.regs.get? A SL phiF shared d env
      sp aRet block base interp index count ss m0 called.σ.mem := by
  obtain ⟨_, _, _, _, _, _, _, interpReg, retReg, envReg, _⟩ := h.dispatch.args
  exact
    { toSeqBlockNormalCarrier := h.normalCarrier entry I
      interpReg := interpReg, retReg := retReg, envReg := envReg
      baseRead := (read64_agreeP h.agreement I.baseCovered).symm.trans I.baseRead
      baseCovered := I.baseCovered, remaining := I.remaining, nonempty := nonempty
      suffix := by
        have eq : base.toNat + 8 * index + 8 = base.toNat + 8 * (index + 1) := by omega
        rw [← eq]
        exact h.suffix.tail
      stackHi := I.stackWrite.2
      spill20 := I.spill20.imp (fun _ hv => (h.dispatch.frame .x20 (by decide)).trans hv)
      spill21 := I.spill21.imp (fun _ hv => (h.dispatch.frame .x21 (by decide)).trans hv) }

/-- Execute block dispatch, a normal child, the back edge, and the recursive tail. -/
theorem consNormal
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {headCost tailCost headRequest tailRequest reserve d env : Nat}
    {st middle final : Vsa.While.St} {s : Stmt} {ss : List Stmt} {status : Status}
    {block base sp aRet interp : BitVec 64} {index count : Nat} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (request : max headRequest tailRequest ≤ maxReq)
    (source : ExecS st d env s middle .normal)
    (head : ExecAllocatorAt N st d env s middle .normal headCost headRequest)
    (tail : ExecSeqAllocatorAt N .blockBody middle d env ss final status tailCost tailRequest)
    (entry : ExecSeqAllocatorEntry .blockBody g N M phiF phiC alloc exts shared
      (headCost + tailCost + reserve) st d env (s :: ss) sp aRet m0 before)
    (I : LoopInput N A SL phiF shared st d env s ss block base sp aRet interp index count before)
    (nonempty : ss ≠ []) :
    ∃ after, Steps before after ∧ ExecSeqAllocatorReturn .blockBody g N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve final status sp aRet m0 after := by
  obtain ⟨called, stmt, dispatch, post⟩ := owned L entry I.toInput
  have carrier := post.carrier entry I nonempty
  have sharedBefore : AgreeP shared m0 called.σ.mem := by
    rw [← entry.entry.mem]
    exact post.agreement
  obtain ⟨returned, headSteps, child⟩ := head.run called.σ.regs.get? A SL gpv headroom maxReq M L
    (Nat.le_trans (Nat.le_max_left _ _) request) phiF phiC alloc exts shared (tailCost + reserve)
    sp 0x800041c8#64 interp stmt (BitVec.ofNat 64 (phiF env)) aRet called.σ.mem called
    (by simpa only [Nat.add_assoc] using post.entry)
  obtain ⟨next, resume, resultF, resultC, resultAlloc, resultExts, returnedShared, continued⟩ :=
    seqBlockAllocatorContinue_of_return L carrier source post.entry.entry.env_valid
      post.entry.entry.stmt_bodies post.entry.entry.store_bodies post.entry.entry.stackOK
      post.entry.entry.stack_ram post.entry.entry.stack_win post.entry.entry.ground.eval_call
      sharedBefore child
  have growth := execS_store_mono source
  obtain ⟨after, tailSteps, result⟩ := continued.run_tail L
    (Nat.le_trans (Nat.le_max_right _ _) request) growth.1 growth.2 tail
  exact ⟨after, dispatch.trans (headSteps.trans (resume.trans tailSteps)), result⟩

#print axioms OwnedPost.carrier
#print axioms consNormal

end Vsa.Sim.SeqBlockDispatch
