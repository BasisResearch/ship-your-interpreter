import Vsa.Sim.SeqClosureAllocatorStep

namespace Vsa.Sim.SeqClosureDispatch

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- A value-returning child completes the closure sequence with its selected maps. -/
theorem consRet
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve d env : Nat}
    {st st' : Vsa.While.St} {s : Stmt} {ss : List Stmt} {v : Value}
    {body base sp aRet interp : BitVec 64} {index : Nat} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (head : ExecAllocatorAt N st d env s st' (.ret v) cost request)
    (entry : ExecSeqAllocatorEntry .closureBody g N M phiF phiC alloc exts shared
      (cost + reserve) st d env (s :: ss) sp aRet m0 before)
    (I : Input N A SL phiF shared st d env s ss body base sp aRet interp index before)
    (arenaBelow : A.hi ≤ SL.lo) :
    ∃ after, Steps before after ∧
      ExecSeqAllocatorReturn .closureBody g N M phiF phiC st.store.frames.size
        st.store.closures.size shared reserve st' (.ret v) sp aRet m0 after := by
  obtain ⟨called, stmt, dispatch, post⟩ := owned L entry I
  obtain ⟨after, steps, child⟩ := head.run called.σ.regs.get? A SL gpv headroom maxReq M L
    hrequest phiF phiC alloc exts shared reserve sp 0x80003378#64 interp stmt
    (BitVec.ofNat 64 (phiF env)) aRet called.σ.mem called post.entry
  obtain ⟨resultF, resultC, repr⟩ := child.selected
  have carrier := post.returnCarrier entry I arenaBelow
  have sharedBefore : AgreeP shared m0 called.σ.mem := by
    rw [← entry.entry.mem]
    exact post.agreement
  exact ⟨after, dispatch.trans steps,
    { exit := carrier.exit child.exit
      selected := ⟨resultF, resultC,
        { repr with owned := repr.owned.rebase (fun _ hv => hv) sharedBefore }⟩
      gp := child.gp }⟩

#print axioms consRet

end Vsa.Sim.SeqClosureDispatch
