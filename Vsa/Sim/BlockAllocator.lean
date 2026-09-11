import Vsa.Sim.BlockAllocatorEntry
import Vsa.Sim.ExecSeqAllocatorAt
import Vsa.Sim.ExecAllocatorAt
import Vsa.Sim.AllocatorReturnAdapters

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open RuntimeOwnership

/-- Run the owned block body and restore its enclosing statement frame. -/
theorem BlockAllocatorPost.run_body
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {cost request reserve : Nat} {st final : Vsa.While.St} {d env : Nat}
    {ss : List Stmt} {status : Status} {sp r aRet p : BitVec 64} {m0 : Mem} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (h : BlockAllocatorPost g N M phiF phiC alloc exts shared (cost + reserve) st d env ss
      sp r aRet p m0 before)
    (body : ExecSeqAllocatorAt N .blockBody ⟨(st.store.allocFrame (some env)).1, st.out⟩
      d st.store.frames.size ss final status cost request) :
    ∃ after, Steps before after ∧ ExecAllocatorReturn g N M phiF phiC
      st.store.frames.size st.store.closures.size shared reserve final status sp r aRet m0 after := by
  obtain ⟨returned, steps, child⟩ := body.run before.σ.regs.get? A SL gpv headroom maxReq M L
    hrequest (pushFrameMap phiF st.store.frames.size p.toNat) phiC
    (alloc.insert (.frame st.store.frames.size) p.toNat 32) ((p.toNat, 32) :: exts)
    shared reserve (sp - 176#64) aRet before.σ.mem before h.entry
  obtain ⟨after, epilogue, result⟩ := blockEpilogue_memory h.parent returned child.exit
  obtain ⟨resultF, resultC, repr⟩ := child.selected
  have coherent : ReturnRepr N A phiF phiC resultF resultC
      st.store.frames.size st.store.closures.size final.store (statusResults aRet.toNat status)
      (AllocatorResult M N shared reserve final.store (statusResults aRet.toNat status) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) after.σ.mem := by
    rw [result.memory]
    exact
      { frames := h.parent.frames.trans (PhiExtends.mono h.parent.frames_le repr.frames)
        closures := h.parent.closures.trans (PhiExtends.mono h.parent.closures_le repr.closures)
        values := repr.values
        owned := repr.owned.rebase (fun _ hv => hv) h.agreement
        survives := repr.survives }
  have ghostGp : g Register.x3 = some gpv :=
    (h.parent.seqFrame .x3 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).symm.trans h.entry.gp
  exact ⟨after, steps.trans epilogue, result.exit.withAllocatorRepr coherent L
    ((result.exit.1.frame .x3 (by decide)).trans ghostGp)⟩

/-- A block consumes one scope credit, then the credits of its owned sequence. -/
theorem execAllocatorAt_block
    {N : NativeAddrs} {st final : Vsa.While.St} {d env : Nat} {ss : List Stmt}
    {status : Status} {cost request : Nat}
    (body : ExecSeqAllocatorAt N .blockBody ⟨(st.store.allocFrame (some env)).1, st.out⟩
      d st.store.frames.size ss final status cost request) :
    ExecAllocatorAt N st d env (.block ss) final status (cost + 1) (max 32 request) where
  run := by
    intro g A SL gpv headroom maxReq M L hrequest phiF phiC alloc exts shared reserve
      sp r aInterp aStmt aEnv aRet m0 before entry
    have entry' : ExecAllocatorEntry g N M phiF phiC alloc exts shared (cost + reserve + 1)
        st d env (.block ss) sp r aInterp aStmt aEnv aRet m0 before := by
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using entry
    obtain ⟨called, p, setupSteps, post⟩ := blockAllocatorEntry_run L entry'
    obtain ⟨after, bodySteps, result⟩ := post.run_body L (by omega) body
    exact ⟨after, setupSteps.trans bodySteps, result⟩

#print axioms BlockAllocatorPost.run_body
#print axioms execAllocatorAt_block

end Vsa.Sim
