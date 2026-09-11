import Vsa.Sim.SeqInterpDispatchOwned
import Vsa.Sim.SeqInterpAllocatorStep

namespace Vsa.Sim.SeqInterpDispatch

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Cursor bounds and interpreter placement retained through normal iteration. -/
structure LoopInput (A : Arena) (SL : StackLayout) (phiF : Addr → Nat)
    (shared : Nat → Prop) (st : Vsa.While.St) (d env : Nat) (s : Stmt) (ss : List Stmt)
    (sp aRet cursor finish interp : BitVec 64) (before : Config) : Prop
    extends Input A SL phiF shared st d env s ss sp aRet cursor finish interp before where
  remaining : finish.toNat = cursor.toNat + 8 * (1 + ss.length)
  arenaBelow : A.hi ≤ SL.lo
  interpAbove : sp.toNat ≤ interp.toNat

/-- The actual dispatch retains the caller frame and all normal-route registers. -/
theorem OwnedPost.caller
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet cursor finish interp stmt : BitVec 64} {m0 : Mem} {before after : Config}
    (h : OwnedPost N M phiF phiC alloc exts shared credits st d env s ss
      sp aRet cursor interp stmt before after)
    (entry : ExecSeqAllocatorEntry .interpRun g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (I : Input A SL phiF shared st d env s ss sp aRet cursor finish interp before) :
    SeqInterpCaller g after.σ.regs.get? A SL sp aRet cursor finish m0 after.σ.mem := by
  obtain ⟨_, cursorReg, finishReg, breakReg, continueReg, _⟩ := I.registers
  exact
    { spLe := I.stackOK.2.1, retInStack := I.retWrite
      memFrame := fun k hs _ => (h.frame k hs).symm.trans (by rw [entry.entry.mem])
      presence := by rw [← entry.entry.mem]; exact h.presence
      frame := fun R hR =>
        (h.dispatch.frame R (by simp [SeqInterpHead.keep, hR.1.1, hR.2.2])).trans
          (entry.entry.frame R hR)
      cursorReg := (h.dispatch.frame .x8 (by decide)).trans cursorReg
      finishReg := (h.dispatch.frame .x18 (by decide)).trans finishReg
      breakReg := (h.dispatch.frame .x19 (by decide)).trans breakReg
      continueReg := (h.dispatch.frame .x20 (by decide)).trans continueReg }

/-- Protected saved words and the owned tail survive result initialization. -/
theorem OwnedPost.carrier
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits d env : Nat} {st : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet cursor finish interp stmt : BitVec 64} {m0 : Mem} {before after : Config}
    (h : OwnedPost N M phiF phiC alloc exts shared credits st d env s ss
      sp aRet cursor interp stmt before after)
    (entry : ExecSeqAllocatorEntry .interpRun g N M phiF phiC alloc exts shared credits
      st d env (s :: ss) sp aRet m0 before)
    (I : LoopInput A SL phiF shared st d env s ss sp aRet cursor finish interp before)
    (nonempty : ss ≠ []) :
    SeqInterpContinueCarrier g after.σ.regs.get? A SL phiF shared d env
      sp aRet cursor finish interp ss m0 after.σ.mem := by
  have word (a : Nat) (offRet : a + 8 ≤ (sp + 88#64).toNat ∨
      (sp + 88#64).toNat + 24 ≤ a) : read64 after.σ.mem a = read64 before.σ.mem a := by
    have agreement : AgreeP (fun k => a ≤ k ∧ k < a + 8) before.σ.mem after.σ.mem :=
      fun k hk => h.dispatch.outside k (by omega)
    exact (read64_agreeP agreement (fun k hk => ⟨by omega, by omega⟩)).symm
  exact
    { toSeqInterpCaller := h.caller entry I.toInput
      retSlot := I.retSlot, remaining := I.remaining, nonempty := nonempty
      stackLo := by have := I.stackOK.1; omega
      arenaBelow := I.arenaBelow, interpAbove := I.interpAbove
      interpHi := I.geometry.args.interpHi
      savedOffRet := by rw [I.retSlot]; exact I.geometry.savedOffRet
      interpOffRet := by rw [I.retSlot]; exact I.geometry.interpOffRet
      savedInterp := (word _ (Or.inl (by have := I.geometry.savedOffRet; omega))).trans I.saved
      script := (word _ (Or.inl I.geometry.savedOffRet)).trans I.script
      environment := (word _ I.geometry.interpOffRet).trans I.environment
      spill21 := I.spill21.imp (fun _ hv => (h.dispatch.frame .x21 (by decide)).trans hv)
      suffix := h.suffix.tail }

/-- Execute the loop-head dispatch, normal statement, back edge, and owned tail. -/
theorem consNormal
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {headCost tailCost headRequest tailRequest reserve d env : Nat}
    {st middle final : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet cursor finish interp : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (request : max headRequest tailRequest ≤ maxReq)
    (source : ExecS st d env s middle .normal)
    (head : ExecAllocatorAt N st d env s middle .normal headCost headRequest)
    (tail : ExecSeqAllocatorAt N .interpRun middle d env ss final .normal tailCost tailRequest)
    (entry : ExecSeqAllocatorEntry .interpRun g N M phiF phiC alloc exts shared
      (headCost + tailCost + reserve) st d env (s :: ss) sp aRet m0 before)
    (I : LoopInput A SL phiF shared st d env s ss sp aRet cursor finish interp before)
    (nonempty : ss ≠ []) :
    ∃ after, Steps before after ∧ ExecSeqAllocatorReturn .interpRun g N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve final .normal sp aRet m0 after := by
  obtain ⟨called, stmt, dispatch, post⟩ := owned L entry I.toInput
  have carrier := post.carrier entry I nonempty
  have shared : AgreeP shared m0 called.σ.mem := by
    rw [← entry.entry.mem]
    exact post.agreement
  obtain ⟨after, steps, result⟩ := seqInterpAllocatorConsNormal L request source head tail
    post.entry carrier shared
  exact ⟨after, dispatch.trans steps, result⟩

/-- Execute the last statement from the loop head through the interpreter's normal exit. -/
theorem consFinal
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve d env : Nat}
    {st final : Vsa.While.St} {s : Stmt}
    {sp aRet cursor finish interp : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (head : ExecAllocatorAt N st d env s final .normal cost request)
    (entry : ExecSeqAllocatorEntry .interpRun g N M phiF phiC alloc exts shared
      (cost + reserve) st d env [s] sp aRet m0 before)
    (I : LoopInput A SL phiF shared st d env s [] sp aRet cursor finish interp before) :
    ∃ after, Steps before after ∧ ExecSeqAllocatorReturn .interpRun g N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve final .normal sp aRet m0 after := by
  obtain ⟨called, stmt, dispatch, post⟩ := owned L entry I.toInput
  have last : cursor + 8#64 = finish := by
    apply BitVec.eq_of_toNat_eq
    have remaining := I.remaining
    simp only [List.length_nil, Nat.add_zero, Nat.mul_one] at remaining
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := finish.isLt; change cursor.toNat + 8 < 2^64; omega)]
    exact remaining.symm
  have shared : AgreeP shared m0 called.σ.mem := by
    rw [← entry.entry.mem]
    exact post.agreement
  obtain ⟨after, steps, result⟩ := seqInterpAllocatorFinal L hrequest head post.entry
    (post.caller entry I.toInput) last shared
  exact ⟨after, dispatch.trans steps, result⟩

#print axioms OwnedPost.caller
#print axioms OwnedPost.carrier
#print axioms consNormal
#print axioms consFinal

end Vsa.Sim.SeqInterpDispatch
