import Vsa.Sim.SeqBlockReadback
import Vsa.Sim.SeqBlockAbrupt

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- Complete the last normal block iteration at its actual child-selected maps. -/
theorem seqBlockAllocatorFinal_of_return
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {nf nc reserve : Nat} {shared : Nat → Prop}
    {final : Vsa.While.St} {sp aRet block : BitVec 64} {index count : Nat}
    {m0 mCall : Mem} {returned : Config}
    (h : SeqBlockNormalCarrier g gExec A SL shared sp aRet block index count m0 mCall)
    (support : EvalCallSupport mCall SL A sp) (last : index + 1 = count)
    (beforeShared : AgreeP shared m0 mCall)
    (child : ExecAllocatorReturn gExec N M phiF phiC nf nc shared reserve
      final .normal sp 0x800041c8#64 aRet mCall returned) :
    ∃ after, Steps returned after ∧ ExecSeqAllocatorReturn .blockBody g N M phiF phiC
      nf nc shared reserve final .normal sp aRet m0 after := by
  obtain ⟨_, _, repr⟩ := child.selected
  obtain ⟨_, _, _, data⟩ := repr.owned.selected
  have pre := h.normalPre support child.exit data.agreement (more := false) (by simp [last])
  obtain ⟨after, steps, post⟩ := SeqBlockNormal.run pre
  obtain ⟨_, _, _, statusReg, _⟩ := post.registers
  have route : SeqBlockExitRoute .normal returned after :=
    { good := post.good, tick := post.tick, pc := post.pc
      statusReg := statusReg, minstret := post.minstret
      memory := post.memory, output := post.output, frame := post.frame }
  exact ⟨after, steps, h.toSeqBlockCaller.return_of_route beforeShared child route⟩

/-- Complete any abrupt block iteration while retaining the child's status and value. -/
theorem seqBlockAllocatorAbrupt_of_return
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {nf nc reserve : Nat} {shared : Nat → Prop}
    {final : Vsa.While.St} {status : Status} {sp aRet : BitVec 64}
    {m0 mCall : Mem} {returned : Config}
    (h : SeqBlockCaller g gExec A SL sp aRet m0 mCall)
    (support : EvalCallSupport mCall SL A sp) (abrupt : status ≠ .normal)
    (beforeShared : AgreeP shared m0 mCall)
    (child : ExecAllocatorReturn gExec N M phiF phiC nf nc shared reserve
      final status sp 0x800041c8#64 aRet mCall returned) :
    ∃ after, Steps returned after ∧ ExecSeqAllocatorReturn .blockBody g N M phiF phiC
      nf nc shared reserve final status sp aRet m0 after := by
  have image : EvalCallSupport returned.σ.mem SL A sp :=
    support.transport_frame h.spLe h.retInStack child.exit.1.memFrame
  obtain ⟨after, steps, route⟩ := SeqBlockAbrupt.run status returned abrupt
    child.exit.1.good child.exit.1.tick child.exit.1.pc child.exit.1.minstret child.exit.1.a0
    image.image.text.Exec_stmtLoaded
  exact ⟨after, steps, h.return_of_route beforeShared child route⟩

#print axioms seqBlockAllocatorFinal_of_return
#print axioms seqBlockAllocatorAbrupt_of_return

end Vsa.Sim
