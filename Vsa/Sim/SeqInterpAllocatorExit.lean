import Vsa.Sim.SeqInterpNormal
import Vsa.Sim.ExecSeqAllocatorAt
import Vsa.Sim.ExecAllocatorAt
import Vsa.Sim.Code.FixedImage_Interp_run

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Caller memory and loop registers retained at the actual statement call. -/
structure SeqInterpCaller
    (g gExec : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (sp aRet cursor finish : BitVec 64)
    (m0 mCall : Mem) : Prop where
  spLe : sp.toNat ≤ SL.hi
  retInStack : SL.lo ≤ aRet.toNat ∧ aRet.toNat + 24 ≤ SL.hi
  memFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (A.lo ≤ k ∧ k < A.hi) →
    mCall[k]? = m0[k]?
  presence : MemExtends m0 mCall
  frame : ∀ R, ExecSeqFrameReg .interpRun R → gExec R = g R
  cursorReg : gExec .x8 = some cursor
  finishReg : gExec .x18 = some finish
  breakReg : gExec .x19 = some 3#64
  continueReg : gExec .x20 = some 1#64

/-- The actual child frame supplies code and all registers read by the normal route. -/
theorem SeqInterpCaller.normalPre
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat} {nf nc : Nat}
    {final : Vsa.While.St} {sp aRet cursor finish : BitVec 64} {m0 mCall : Mem}
    {cfg : Config} {done : Bool}
    (h : SeqInterpCaller g gExec A SL sp aRet cursor finish m0 mCall)
    (support : EvalCallSupport mCall SL A sp)
    (child : ExecExitD gExec N A SL phiF phiC nf nc final .normal
      sp 0x80004478#64 aRet mCall cfg)
    (branch : guardB bop.BEQ (cursor + 8#64) finish = done) :
    SeqInterpNormal.Pre cursor finish done cfg := by
  have image : EvalCallSupport cfg.σ.mem SL A sp :=
    support.transport_frame h.spLe h.retInStack child.1.memFrame
  exact
    { good := child.1.good, tick := child.1.tick, pc := child.1.pc
      minstret := child.1.minstret, branch := branch
      code := image.image.text.Interp_runLoaded
      registers := ⟨child.1.a0,
        (child.1.frame .x19 (by decide)).trans h.breakReg,
        (child.1.frame .x20 (by decide)).trans h.continueReg,
        (child.1.frame .x8 (by decide)).trans h.cursorReg,
        (child.1.frame .x18 (by decide)).trans h.finishReg, trivial⟩ }

/-- Finish the interpreter sequence after its last normal child. The selected
maps and allocation reserve remain those returned by that same child. -/
theorem seqInterpAllocatorFinal_of_return
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {nf nc reserve : Nat} {shared : Nat → Prop}
    {final : Vsa.While.St} {sp aRet cursor finish : BitVec 64} {m0 mCall : Mem}
    {cfg : Config}
    (h : SeqInterpCaller g gExec A SL sp aRet cursor finish m0 mCall)
    (support : EvalCallSupport mCall SL A sp)
    (last : cursor + 8#64 = finish)
    (beforeShared : AgreeP shared m0 mCall)
    (child : ExecAllocatorReturn gExec N M phiF phiC nf nc shared reserve
      final .normal sp 0x80004478#64 aRet mCall cfg) :
    ∃ after, Steps cfg after ∧ ExecSeqAllocatorReturn .interpRun g N M phiF phiC
      nf nc shared reserve final .normal sp aRet m0 after := by
  have pre := h.normalPre support child.exit (done := true) (by simp [last, guardB])
  obtain ⟨after, steps, post⟩ := SeqInterpNormal.run pre
  obtain ⟨resultF, resultC, repr⟩ := child.selected
  refine ⟨after, steps,
    { exit :=
        { supported := rfl, good := post.good, tick := post.tick, pc := post.pc
          status_abi := trivial
          store := by rw [post.memory]; exact child.exit.1.store
          out := by simpa [OutRepr, output, post.output] using child.exit.1.out
          retval := fun _ hv => by cases hv
          mem_frame := ?_
          stack_frame := trivial
          mem_extends := by rw [post.memory]; exact h.presence.trans child.exit.2.1
          store_survives := by rw [post.memory]; exact child.exit.2.2
          frame := fun R hR =>
            (post.frame R (by simp [SeqInterpNormal.keep, hR.1.1, hR.2.1])).trans
              ((child.exit.1.frame R hR.1).trans (h.frame R hR))
          minstret := post.minstret }
      selected := ⟨resultF, resultC, ?_⟩
      gp := (post.frame .x3 (by decide)).trans child.gp }⟩
  · intro k hs hA
    rw [post.memory]
    have spLe := h.spLe
    have ret := h.retInStack
    exact ((child.exit.1.memFrame k (by omega) hA).resolve_left (by omega)).trans
      (h.memFrame k hs hA)
  · rw [post.memory]
    exact { repr with owned := repr.owned.rebase (fun _ hv => hv) beforeShared }

#print axioms SeqInterpCaller.normalPre
#print axioms seqInterpAllocatorFinal_of_return

end Vsa.Sim
