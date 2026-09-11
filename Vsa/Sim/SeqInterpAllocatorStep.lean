import Vsa.Sim.SeqInterpAllocatorContinue

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- Execute the owned statement and interpreter back edge into the tail entry. -/
theorem seqInterpAllocatorContinue
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve d env : Nat}
    {st final : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet cursor finish interp aStmt aEnv : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (source : ExecS st d env s final .normal)
    (head : ExecAllocatorAt N st d env s final .normal cost request)
    (entry : ExecAllocatorEntry gExec N M phiF phiC alloc exts shared (cost + reserve)
      st d env s sp 0x80004478#64 interp aStmt aEnv aRet before.σ.mem before)
    (h : SeqInterpContinueCarrier g gExec A SL phiF shared d env
      sp aRet cursor finish interp ss m0 before.σ.mem)
    (beforeShared : AgreeP shared m0 before.σ.mem) :
    ∃ after, Steps before after ∧ ∃ resultF resultC resultAlloc resultExts returnedShared,
      SeqAllocatorContinueAt .interpRun g N M phiF phiC resultF resultC
        st.store.frames.size st.store.closures.size resultAlloc resultExts shared returnedShared
        reserve final d env ss sp aRet m0 after := by
  obtain ⟨returned, steps, child⟩ := head.run gExec A SL gpv headroom maxReq M L hrequest
    phiF phiC alloc exts shared reserve sp 0x80004478#64 interp aStmt aEnv aRet
    before.σ.mem before entry
  obtain ⟨after, resume, resultF, resultC, resultAlloc, resultExts, returnedShared, post⟩ :=
    seqInterpAllocatorContinue_of_return L h source entry.entry.env_valid
      entry.entry.stmt_bodies entry.entry.store_bodies entry.entry.stackOK
      entry.entry.stack_ram entry.entry.stack_win entry.entry.ground.eval_call beforeShared child
  exact ⟨after, steps.trans resume, resultF, resultC, resultAlloc, resultExts, returnedShared, post⟩

/-- Compose the actual statement, interpreter back edge, and recursive owned tail. -/
theorem seqInterpAllocatorConsNormal
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {headCost tailCost headRequest tailRequest reserve d env : Nat}
    {st middle final : Vsa.While.St} {s : Stmt} {ss : List Stmt}
    {sp aRet cursor finish interp aStmt aEnv : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (hrequest : max headRequest tailRequest ≤ maxReq)
    (source : ExecS st d env s middle .normal)
    (head : ExecAllocatorAt N st d env s middle .normal headCost headRequest)
    (tail : ExecSeqAllocatorAt N .interpRun middle d env ss final .normal tailCost tailRequest)
    (entry : ExecAllocatorEntry gExec N M phiF phiC alloc exts shared
      (headCost + tailCost + reserve) st d env s sp 0x80004478#64
      interp aStmt aEnv aRet before.σ.mem before)
    (h : SeqInterpContinueCarrier g gExec A SL phiF shared d env
      sp aRet cursor finish interp ss m0 before.σ.mem)
    (beforeShared : AgreeP shared m0 before.σ.mem) :
    ∃ after, Steps before after ∧ ExecSeqAllocatorReturn .interpRun g N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve final .normal sp aRet m0 after := by
  have entry' : ExecAllocatorEntry gExec N M phiF phiC alloc exts shared
      (headCost + (tailCost + reserve)) st d env s sp 0x80004478#64
      interp aStmt aEnv aRet before.σ.mem before := by
    simpa only [Nat.add_assoc] using entry
  obtain ⟨next, headSteps, resultF, resultC, resultAlloc, resultExts, returnedShared, post⟩ :=
    seqInterpAllocatorContinue L (Nat.le_trans (Nat.le_max_left _ _) hrequest)
      source head entry' h beforeShared
  have growth := execS_store_mono source
  obtain ⟨after, tailSteps, result⟩ := post.run_tail L
    (Nat.le_trans (Nat.le_max_right _ _) hrequest) growth.1 growth.2 tail
  exact ⟨after, headSteps.trans tailSteps, result⟩

/-- Execute the final owned statement and the interpreter's five-instruction exit. -/
theorem seqInterpAllocatorFinal
    {g gExec : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve d env : Nat}
    {st final : Vsa.While.St} {s : Stmt}
    {sp aRet cursor finish interp aStmt aEnv : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (head : ExecAllocatorAt N st d env s final .normal cost request)
    (entry : ExecAllocatorEntry gExec N M phiF phiC alloc exts shared (cost + reserve)
      st d env s sp 0x80004478#64 interp aStmt aEnv aRet before.σ.mem before)
    (h : SeqInterpCaller g gExec A SL sp aRet cursor finish m0 before.σ.mem)
    (last : cursor + 8#64 = finish)
    (beforeShared : AgreeP shared m0 before.σ.mem) :
    ∃ after, Steps before after ∧ ExecSeqAllocatorReturn .interpRun g N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve final .normal sp aRet m0 after := by
  obtain ⟨returned, steps, child⟩ := head.run gExec A SL gpv headroom maxReq M L hrequest
    phiF phiC alloc exts shared reserve sp 0x80004478#64 interp aStmt aEnv aRet
    before.σ.mem before entry
  obtain ⟨after, resume, result⟩ := seqInterpAllocatorFinal_of_return h
    entry.entry.ground.eval_call last beforeShared child
  exact ⟨after, steps.trans resume, result⟩

#print axioms seqInterpAllocatorContinue
#print axioms seqInterpAllocatorConsNormal
#print axioms seqInterpAllocatorFinal

end Vsa.Sim
