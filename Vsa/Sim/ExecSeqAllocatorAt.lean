import Vsa.Sim.ExecSeqAllocatorEntry
import Vsa.Sim.AllocatorIH
import Vsa.Sim.ExecSeqIndexed

namespace Vsa.Sim

open LeanRV64DExecutable Vsa.Machine Vsa.Logic Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open RuntimeOwnership

/-- Sequence status and allocator ownership refer to one selected return memory. -/
structure ExecSeqAllocatorReturn
    (copy : ExecSeqCopy) (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (phiF phiC : Addr → Nat)
    (nf nc : Nat) (shared : Nat → Prop) (credits : Nat)
    (st : Vsa.While.St) (status : Status) (sp aRet : BitVec 64)
    (m0 : Mem) (c : Config) : Prop where
  exit : ExecSeqExitI copy g N A SL phiF phiC nf nc st status sp aRet m0 c
  selected : ∃ resultF resultC,
    ReturnRepr N A phiF phiC resultF resultC nf nc st.store (statusResults aRet.toNat status)
      (AllocatorResult M N shared credits st.store (statusResults aRet.toNat status) m0)
      (fun k => SL.lo ≤ k ∧ k < SL.hi) c.σ.mem
  gp : c.σ.regs.get? Register.x3 = some gpv

/-- Owned execution of a sequence in one physical loop copy. -/
structure ExecSeqAllocatorAt (N : NativeAddrs) (copy : ExecSeqCopy)
    (st : Vsa.While.St) (d env : Nat) (ss : List Stmt)
    (st' : Vsa.While.St) (status : Status) (cost maxRequest : Nat) : Prop where
  run : ∀ (g : (R : Register) → Option (RegisterType R))
    (A : Arena) (SL : StackLayout) (gpv : BitVec 64)
    (headroom maxReq : Nat) (M : MallocContract A SL gpv headroom maxReq)
    (_L : AllocLedger A SL gpv headroom maxReq M), maxRequest ≤ maxReq →
    ∀ (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (reserve : Nat) (sp aRet : BitVec 64) (m0 : Mem),
    Triple (ExecSeqAllocatorEntry copy g N M phiF phiC alloc exts shared (cost + reserve)
      st d env ss sp aRet m0)
      (ExecSeqAllocatorReturn copy g N M phiF phiC st.store.frames.size st.store.closures.size
        shared reserve st' status sp aRet m0)

/-- The next sequence entry uses the child return's selected heap and maps. -/
structure SeqAllocatorContinueAt
    (copy : ExecSeqCopy) (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (entryF entryC resultF resultC : Addr → Nat) (nf nc : Nat)
    (alloc : Allocations) (exts : List Extent) (entryShared shared : Nat → Prop)
    (credits : Nat) (st : Vsa.While.St) (d env : Nat) (ss : List Stmt)
    (sp aRet : BitVec 64) (m0 : Mem) (cfg : Config) : Prop where
  entry : ExecSeqAllocatorEntry copy g N M resultF resultC alloc exts shared credits
    st d env ss sp aRet cfg.σ.mem cfg
  frames : PhiExtends entryF resultF nf
  closures : PhiExtends entryC resultC nc
  includes : ∀ k, entryShared k → shared k
  agreement : AgreeP entryShared m0 cfg.σ.mem
  memFrame : ∀ a, ¬ (SL.lo ≤ a ∧ a < SL.hi) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    cfg.σ.mem[a]? = m0[a]?
  highStack : ExecSeqStackFrame copy A SL sp aRet m0 cfg.σ.mem
  presence : MemExtends m0 cfg.σ.mem

/-- Consume the owned tail entry and rebase its return to the sequence caller. -/
theorem SeqAllocatorContinueAt.run_tail
    {copy : ExecSeqCopy} {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {entryF entryC middleF middleC : Addr → Nat} {nf nc : Nat}
    {alloc : Allocations} {exts : List Extent} {entryShared shared : Nat → Prop}
    {cost request reserve d env : Nat} {st st' : Vsa.While.St} {ss : List Stmt}
    {status : Status} {sp aRet : BitVec 64} {m0 : Mem} {before : Config}
    (h : SeqAllocatorContinueAt copy g N M entryF entryC middleF middleC nf nc alloc exts
      entryShared shared (cost + reserve) st d env ss sp aRet m0 before)
    (L : AllocLedger A SL gpv headroom maxReq M) (hrequest : request ≤ maxReq)
    (framesBound : nf ≤ st.store.frames.size) (closuresBound : nc ≤ st.store.closures.size)
    (ih : ExecSeqAllocatorAt N copy st d env ss st' status cost request) :
    ∃ after, Steps before after ∧
      ExecSeqAllocatorReturn copy g N M entryF entryC nf nc entryShared reserve
        st' status sp aRet m0 after := by
  obtain ⟨after, steps, result⟩ := ih.run g A SL gpv headroom maxReq M L hrequest
    middleF middleC alloc exts shared reserve sp aRet before.σ.mem before h.entry
  obtain ⟨resultF, resultC, repr⟩ := result.selected
  refine ⟨after, steps,
    { exit := execSeqExitI_extend copy g N A SL entryF entryC middleF middleC nf nc
        st.store.frames.size st.store.closures.size st' status sp aRet m0 before.σ.mem after
        framesBound closuresBound h.frames h.closures h.memFrame h.highStack h.presence result.exit
      selected := ⟨resultF, resultC,
        { frames := h.frames.trans (PhiExtends.mono framesBound repr.frames)
          closures := h.closures.trans (PhiExtends.mono closuresBound repr.closures)
          values := repr.values
          owned := repr.owned.rebase_shared h.includes (fun _ hv => hv) h.agreement
          survives := repr.survives }⟩
      gp := result.gp }⟩

#print axioms SeqAllocatorContinueAt.run_tail


end Vsa.Sim
