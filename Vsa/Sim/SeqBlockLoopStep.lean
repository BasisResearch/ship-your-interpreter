import Vsa.Sim.SeqBlockDispatchOwned
import Vsa.Sim.SeqBlockAllocatorExit

namespace Vsa.Sim.SeqBlockDispatch

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Header ownership and protected stack words retained for the block back edge. -/
structure LoopInput (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF : Addr → Nat) (shared : Nat → Prop) (st : Vsa.While.St) (d env : Nat)
    (s : Stmt) (ss : List Stmt) (block base sp aRet interp : BitVec 64)
    (index count : Nat) (before : Config) : Prop
    extends Input N A SL phiF shared st d env s ss block base sp aRet interp index before where
  baseCovered : Covers shared (block.toNat + 8) 8
  blockCount : read32 before.σ.mem (block.toNat + 16) = some count
  countCovered : Covers shared (block.toNat + 16) 4
  remaining : index + 1 + ss.length = count
  countBound : count < 2^31
  savedOffArena : sp.toNat + 16 ≤ A.lo ∨ A.hi ≤ sp.toNat + 8
  savedOffRet : sp.toNat + 16 ≤ aRet.toNat ∨ aRet.toNat + 24 ≤ sp.toNat + 8
  normalGeometry : SeqBlockNormal.Geometry sp block

/-- Dispatch preserves the caller frame needed by either block exit. -/
theorem OwnedPost.caller
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {block base sp aRet interp stmt : BitVec 64} {index : Nat} {m0 : Mem}
    {before called : Config}
    (h : OwnedPost N M phiF phiC alloc exts shared credits st d env s ss
      block base sp aRet interp stmt index before called)
    (entry : ExecSeqAllocatorEntry .blockBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (I : Input N A SL phiF shared st d env s ss block base sp aRet interp index before) :
    SeqBlockCaller g called.σ.regs.get? A SL sp aRet m0 called.σ.mem := by
  exact
    { spLe := by have := I.stackWrite; omega
      retInStack := h.entry.entry.ground.aret.inSL
      memFrame := fun k hs _ => (h.frame k hs).symm.trans (by rw [entry.entry.mem])
      highStack := by
        intro k hlo _ _ _
        rw [h.dispatch.memory, ← entry.entry.mem]
        apply writeLog_out
        simp only [OutL, and_true]
        omega
      presence := by rw [← entry.entry.mem]; exact h.presence
      frame := fun R hR => (h.dispatch.frame R hR.1).trans (entry.entry.frame R hR) }

/-- Dispatch supplies the normal route's saved index and immutable count. -/
theorem OwnedPost.normalCarrier
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
    (I : LoopInput N A SL phiF shared st d env s ss block base sp aRet interp index count before) :
    SeqBlockNormalCarrier g called.σ.regs.get? A SL shared
      sp aRet block index count m0 called.σ.mem := by
  obtain ⟨_, _, _, _, _, blockReg, _⟩ := h.dispatch.args
  exact
    { toSeqBlockCaller := h.caller entry I.toInput
      blockReg := blockReg, geometry := I.normalGeometry
      stackLo := by have := I.stackOK.1; omega
      savedOffArena := I.savedOffArena, savedOffRet := I.savedOffRet
      savedIndex := h.dispatch.savedIndex
      blockCount := (read32_agreeP h.agreement I.countCovered).symm.trans I.blockCount
      countCovered := I.countCovered
      nextBound := by have := I.remaining; omega
      countBound := I.countBound }

/-- Execute the singleton block sequence through its normal return. -/
theorem consFinal
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve d env : Nat}
    {st final : Vsa.While.St} {s : Stmt}
    {block base sp aRet interp : BitVec 64} {index count : Nat} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (head : ExecAllocatorAt N st d env s final .normal cost request)
    (entry : ExecSeqAllocatorEntry .blockBody g N M phiF phiC alloc exts shared
      (cost + reserve) st d env [s] sp aRet m0 before)
    (I : LoopInput N A SL phiF shared st d env s [] block base sp aRet interp index count before) :
    ∃ after, Steps before after ∧ ExecSeqAllocatorReturn .blockBody g N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve final .normal sp aRet m0 after := by
  obtain ⟨called, stmt, dispatch, post⟩ := owned L entry I.toInput
  obtain ⟨returned, steps, child⟩ := head.run called.σ.regs.get? A SL gpv headroom maxReq M L
    hrequest phiF phiC alloc exts shared reserve sp 0x800041c8#64 interp stmt
    (BitVec.ofNat 64 (phiF env)) aRet called.σ.mem called post.entry
  have sharedBefore : AgreeP shared m0 called.σ.mem := by
    rw [← entry.entry.mem]
    exact post.agreement
  obtain ⟨after, resume, result⟩ := seqBlockAllocatorFinal_of_return (post.normalCarrier entry I)
    post.entry.entry.ground.eval_call (by simpa using I.remaining) sharedBefore child
  exact ⟨after, dispatch.trans (steps.trans resume), result⟩

/-- Execute an abrupt first statement and propagate its status and return value. -/
theorem consAbrupt
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve d env : Nat}
    {st final : Vsa.While.St} {s : Stmt} {ss : List Stmt} {status : Status}
    {block base sp aRet interp : BitVec 64} {index : Nat} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (head : ExecAllocatorAt N st d env s final status cost request) (abrupt : status ≠ .normal)
    (entry : ExecSeqAllocatorEntry .blockBody g N M phiF phiC alloc exts shared
      (cost + reserve) st d env (s :: ss) sp aRet m0 before)
    (I : Input N A SL phiF shared st d env s ss block base sp aRet interp index before) :
    ∃ after, Steps before after ∧ ExecSeqAllocatorReturn .blockBody g N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve final status sp aRet m0 after := by
  obtain ⟨called, stmt, dispatch, post⟩ := owned L entry I
  obtain ⟨returned, steps, child⟩ := head.run called.σ.regs.get? A SL gpv headroom maxReq M L
    hrequest phiF phiC alloc exts shared reserve sp 0x800041c8#64 interp stmt
    (BitVec.ofNat 64 (phiF env)) aRet called.σ.mem called post.entry
  have sharedBefore : AgreeP shared m0 called.σ.mem := by
    rw [← entry.entry.mem]
    exact post.agreement
  obtain ⟨after, resume, result⟩ := seqBlockAllocatorAbrupt_of_return (post.caller entry I)
    post.entry.entry.ground.eval_call abrupt sharedBefore child
  exact ⟨after, dispatch.trans (steps.trans resume), result⟩

#print axioms OwnedPost.caller
#print axioms OwnedPost.normalCarrier
#print axioms consFinal
#print axioms consAbrupt

end Vsa.Sim.SeqBlockDispatch
