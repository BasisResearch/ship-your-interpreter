import Vsa.Sim.ExecSeqIndexed

namespace Vsa.Sim

open LeanRV64DExecutable Sail Register
open Vsa.Machine (Config Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc

/-- Facts retained by a reached closure-sequence child dispatch. The child
ghost frame and memory are exactly those used by its `ExecEntry`/`ExecExitD`.
Cursor and next-head geometry are unnecessary on a return exit. -/
structure SeqClosureRetCarrier
    (g gExec : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (sp aRet : BitVec 64)
    (m0 mCall : Mem) : Prop where
  spLe : sp.toNat ≤ SL.hi
  retInStack : SL.lo ≤ aRet.toNat ∧ aRet.toNat + 24 ≤ SL.hi
  childFrame : ClosureBodyFrameGeom A SL sp aRet
  memFrame : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < SL.hi) →
    ¬ (A.lo ≤ a ∧ a < A.hi) → mCall[a]? = m0[a]?
  highStack : ExecSeqStackFrame .closureBody A SL sp aRet m0 mCall
  memExtends : MemExtends m0 mCall
  frame : ∀ R : Register, ExecSeqFrameReg .closureBody R → gExec R = g R

/-- A returned closure-body statement is already at the sequence's return
boundary. Rebase its memory and ghost frame without executing an instruction. -/
theorem seqClosureRetResume
    {g gExec : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {φf φc : Addr → Nat}
    {nf nc : Nat} {st' : Vsa.While.St} {v : Value}
    {sp aRet : BitVec 64} {m0 mCall : Mem}
    (h : SeqClosureRetCarrier g gExec A SL sp aRet m0 mCall) :
    Triple
      (ExecExitD gExec N A SL φf φc nf nc st' (.ret v)
        sp 0x80003378#64 aRet mCall)
      (ExecSeqExitI .closureBody g N A SL φf φc nf nc
        st' (.ret v) sp aRet m0) := by
  intro cfg hChild
  refine ⟨cfg, Steps.refl cfg, ?_⟩
  exact
    { supported := Or.inr ⟨v, rfl⟩
      good := hChild.1.good
      tick := hChild.1.tick
      pc := by simpa [execSeqExitPC] using hChild.1.pc
      status_abi := hChild.1.a0
      store := hChild.1.store
      out := hChild.1.out
      retval := hChild.1.retval
      mem_frame := by
        intro a hstack hArena
        have hsp := h.spLe
        have hret := h.retInStack
        rcases hChild.1.memFrame a
            (by intro ha; exact hstack ⟨ha.1, by omega⟩) hArena with hr | heq
        · exact False.elim (hstack ⟨by omega, by omega⟩)
        · exact heq.trans (h.memFrame a hstack hArena)
      stack_frame := h.highStack.trans (closureBodyStackFrame_of_execExitD h.childFrame hChild)
      mem_extends := h.memExtends.trans hChild.2.1
      store_survives := hChild.2.2
      frame := fun R hR => (hChild.1.frame R hR.1).trans (h.frame R hR)
      minstret := hChild.1.minstret }

#print axioms seqClosureRetResume

end Vsa.Sim
