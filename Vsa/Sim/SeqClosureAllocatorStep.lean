import Vsa.Sim.SeqClosureDispatchOwned
import Vsa.Sim.SeqClosureAllocatorContinue

namespace Vsa.Sim.SeqClosureDispatch

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The represented closure header and caller frame used by the normal back edge. -/
structure LoopInput (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (phiF : Addr → Nat) (shared : Nat → Prop) (st : Vsa.While.St) (d env : Nat)
    (s : Stmt) (ss : List Stmt) (body base sp aRet interp : BitVec 64)
    (index count : Nat) (before : Config) : Prop
    extends Input N A SL phiF shared st d env s ss body base sp aRet interp index before where
  baseCovered : Covers shared (body.toNat + 8) 8
  bodyCount : read32 before.σ.mem (body.toNat + 16) = some count
  countCovered : Covers shared (body.toNat + 16) 4
  remaining : index + 1 + ss.length = count
  countBound : count < 2^31
  arenaBelow : A.hi ≤ SL.lo
  bodyLo : 0x80000000 ≤ body.toNat
  bodyHi : body.toNat + 20 ≤ 0x100000000
  bodyWin : tohostAddr + 8 ≤ body.toNat + 16
  bodyAlign : body.toNat % 4 = 0

/-- The actual dispatch retains the caller frame needed by every sequence return. -/
theorem OwnedPost.returnCarrier
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {body base sp aRet interp stmt : BitVec 64} {index : Nat} {m0 : Mem}
    {before after : Config}
    (h : OwnedPost N M phiF phiC alloc exts shared credits st d env s ss
      body base sp aRet interp stmt index before after)
    (entry : ExecSeqAllocatorEntry .closureBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (I : Input N A SL phiF shared st d env s ss body base sp aRet interp index before)
    (arenaBelow : A.hi ≤ SL.lo) :
    SeqClosureRetCarrier g after.σ.regs.get? A SL sp aRet m0 after.σ.mem := by
  have ret := I.retAddress
  exact
    { spLe := by have := I.stackWrite; omega
      retInStack := h.entry.entry.ground.aret.inSL
      childFrame :=
        { stackLo := I.stackWrite.1, arenaBelow := arenaBelow, retBelow := by omega }
      memFrame := fun k hs _ => (h.frame k hs).symm.trans (by rw [entry.entry.mem])
      highStack := by
        intro k hlo hhi
        rw [h.dispatch.memory, ← entry.entry.mem]
        apply writeLog_out
        simp only [OutL, and_true]
        omega
      memExtends := by rw [← entry.entry.mem]; exact h.presence
      frame := fun R hR => (h.dispatch.frame R hR.1).trans (entry.entry.frame R hR) }

/-- The actual dispatch supplies the complete continuation carrier. -/
theorem OwnedPost.carrier
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {body base sp aRet interp stmt : BitVec 64} {index count : Nat} {m0 : Mem}
    {before after : Config}
    (h : OwnedPost N M phiF phiC alloc exts shared credits st d env s ss
      body base sp aRet interp stmt index before after)
    (entry : ExecSeqAllocatorEntry .closureBody g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (I : LoopInput N A SL phiF shared st d env s ss body base sp aRet interp index count before)
    (nonempty : ss ≠ []) :
    SeqClosureContinueCarrier g after.σ.regs.get? A SL phiF shared d env
      sp aRet body base interp index count ss m0 after.σ.mem := by
  have ret := I.toInput.retAddress
  obtain ⟨_, _, _, _, _, indexReg, _, interpReg, envReg, _⟩ := h.dispatch.args
  exact
    { toSeqClosureRetCarrier := h.returnCarrier entry I.toInput I.arenaBelow
      indexReg := indexReg, interpReg := interpReg, envReg := envReg, retSlot := I.retSlot
      remaining := I.remaining, nonempty := nonempty, countBound := I.countBound
      savedBody := h.dispatch.savedBody
      bodyBase := (read64_agreeP h.agreement I.baseCovered).symm.trans I.baseRead
      baseCovered := I.baseCovered
      bodyCount := (read32_agreeP h.agreement I.countCovered).symm.trans I.bodyCount
      countCovered := I.countCovered
      suffix := by
        have eq : base.toNat + 8 * index + 8 = base.toNat + 8 * (index + 1) := by omega
        rw [← eq]
        exact h.suffix.tail
      spLo := I.geometry.stackLo, spHi := I.geometry.stackHi
      spWin := by have := I.geometry.stackHtif; omega
      spAlign := I.geometry.stackAlign, savedOffRet := by omega
      bodyLo := I.bodyLo, bodyHi := I.bodyHi, bodyWin := I.bodyWin, bodyAlign := I.bodyAlign
      spill9 := I.spill9.imp (fun _ hv => (h.dispatch.frame .x9 (by decide)).trans hv)
      spill20 := I.spill20.imp (fun _ hv => (h.dispatch.frame .x20 (by decide)).trans hv)
      spill21 := I.spill21.imp (fun _ hv => (h.dispatch.frame .x21 (by decide)).trans hv) }

/-- Execute closure dispatch, a normal child, the back edge, and the owned tail. -/
theorem consNormal
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {headCost tailCost headRequest tailRequest reserve d env : Nat}
    {st stMid st' : Vsa.While.St} {s : Stmt} {ss : List Stmt} {status : Status}
    {body base sp aRet interp : BitVec 64} {index count : Nat} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (request : max headRequest tailRequest ≤ maxReq)
    (source : ExecS st d env s stMid .normal)
    (head : ExecAllocatorAt N st d env s stMid .normal headCost headRequest)
    (tail : ExecSeqAllocatorAt N .closureBody stMid d env ss st' status tailCost tailRequest)
    (entry : ExecSeqAllocatorEntry .closureBody g N M phiF phiC alloc exts shared
      (headCost + tailCost + reserve) st d env (s :: ss) sp aRet m0 before)
    (I : LoopInput N A SL phiF shared st d env s ss body base sp aRet interp index count before)
    (nonempty : ss ≠ []) :
    ∃ after, Steps before after ∧
      ExecSeqAllocatorReturn .closureBody g N M phiF phiC
        st.store.frames.size st.store.closures.size shared reserve st' status sp aRet m0 after := by
  obtain ⟨called, stmt, dispatch, post⟩ := owned L entry I.toInput
  have carrier := post.carrier entry I nonempty
  have shared : AgreeP shared m0 called.σ.mem := by
    rw [← entry.entry.mem]
    exact post.agreement
  obtain ⟨after, steps, result⟩ := seqClosureAllocatorConsNormal L request source head tail
    post.entry carrier shared
  exact ⟨after, dispatch.trans steps, result⟩

#print axioms OwnedPost.returnCarrier
#print axioms OwnedPost.carrier
#print axioms consNormal

end Vsa.Sim.SeqClosureDispatch
