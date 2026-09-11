import Vsa.Sim.ExecSeqAllocatorAt
import Vsa.Sim.ExecAllocatorAt
import Vsa.Sim.ExecSeqIndexed

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- The block caller's frame retained at its actual statement call. -/
structure SeqBlockCaller
    (g gExec : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (sp aRet : BitVec 64) (m0 mCall : Mem) : Prop where
  spLe : sp.toNat ≤ SL.hi
  retInStack : SL.lo ≤ aRet.toNat ∧ aRet.toNat + 24 ≤ SL.hi
  memFrame : ∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → ¬ (A.lo ≤ k ∧ k < A.hi) →
    mCall[k]? = m0[k]?
  highStack : ExecSeqStackFrame .blockBody A SL sp aRet m0 mCall
  presence : MemExtends m0 mCall
  frame : ∀ R, ExecSeqFrameReg .blockBody R → gExec R = g R

/-- A reflected block return route preserves the child's memory and status. -/
structure SeqBlockExitRoute (status : Status) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x8000409c#64
  statusReg : after.σ.regs.get? Register.x10 = some (StatusCode status)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Rebase the actual child and route at the child's selected maps and reserve. -/
theorem SeqBlockCaller.return_of_route
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {nf nc reserve : Nat} {shared : Nat → Prop}
    {final : Vsa.While.St} {status : Status} {sp aRet : BitVec 64}
    {m0 mCall : Mem} {returned after : Config}
    (h : SeqBlockCaller g gExec A SL sp aRet m0 mCall)
    (beforeShared : AgreeP shared m0 mCall)
    (child : ExecAllocatorReturn gExec N M phiF phiC nf nc shared reserve
      final status sp 0x800041c8#64 aRet mCall returned)
    (route : SeqBlockExitRoute status returned after) :
    ExecSeqAllocatorReturn .blockBody g N M phiF phiC nf nc shared reserve
      final status sp aRet m0 after := by
  obtain ⟨resultF, resultC, repr⟩ := child.selected
  refine
    { exit :=
        { supported := trivial, good := route.good, tick := route.tick, pc := route.pc
          status_abi := route.statusReg
          store := by rw [route.memory]; exact child.exit.1.store
          out := by simpa [OutRepr, output, route.output] using child.exit.1.out
          retval := by intro v hv; rw [route.memory]; exact child.exit.1.retval v hv
          mem_frame := ?_
          stack_frame := by
            rw [route.memory]
            exact h.highStack.trans (blockBodyStackFrame_of_execExitD child.exit)
          mem_extends := by rw [route.memory]; exact h.presence.trans child.exit.2.1
          store_survives := by rw [route.memory]; exact child.exit.2.2
          frame := fun R hR => (route.frame R hR.1.1).trans
            ((child.exit.1.frame R hR.1).trans (h.frame R hR))
          minstret := route.minstret }
      selected := ⟨resultF, resultC, ?_⟩
      gp := (route.frame .x3 (by decide)).trans child.gp }
  · intro k hs hA
    rw [route.memory]
    have spLe := h.spLe
    have ret := h.retInStack
    exact ((child.exit.1.memFrame k (by omega) hA).resolve_left (by omega)).trans
      (h.memFrame k hs hA)
  · rw [route.memory]
    exact { repr with owned := repr.owned.rebase (fun _ hv => hv) beforeShared }

#print axioms SeqBlockCaller.return_of_route

end Vsa.Sim
