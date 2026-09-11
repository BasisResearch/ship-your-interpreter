import Vsa.Sim.EnvNewAllocatorReturn
import Vsa.Sim.rows.EnvNewContractSupply

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The fresh pointer, ordinary return, and remaining reserve share one endpoint. -/
structure EnvNewAllocatorPost
    (g : (R : Register) → Option (RegisterType R)) (N : NativeAddrs)
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    (phiF phiC : Addr → Nat) (alloc : Allocations) (exts : List Extent)
    (shared : Nat → Prop) (credits : Nat) (st : Vsa.While.St) (env : Addr)
    (esp r p : BitVec 64) (m : Mem) (out : Array String) (after : Config) : Prop where
  exit : EnvNewReturnState g N A SL phiF phiC st env esp r m out after
  result : after.σ.regs.get? Register.x10 = some p
  fresh : EnvNewFresh N A SL phiF phiC st env p
    (pushFrameMap phiF st.store.frames.size p.toNat) after.σ.mem
  allocator : RuntimeAllocatorState M N (pushFrameMap phiF st.store.frames.size p.toNat) phiC
    (alloc.insert (.frame st.store.frames.size) p.toNat 32) ((p.toNat, 32) :: exts)
    shared credits (st.store.allocFrame (some env)).1 after.σ.mem
  agreement : AgreeP shared m after.σ.mem
  capacity : read32 after.σ.mem (p.toNat + 4) = some 0
  gp : after.σ.regs.get? Register.x3 = some gpv

/-- Run env_new from the current owned store, consuming one allocation credit. -/
theorem envNewAllocator_run
    {g : (R : Register) → Option (RegisterType R)} {N : NativeAddrs}
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    {phiF phiC : Addr → Nat} {alloc : Allocations} {exts : List Extent}
    {shared : Nat → Prop} {credits : Nat} {st : Vsa.While.St} {env : Addr}
    {esp aEnv r : BitVec 64} {m : Mem} {out : Array String} {before : Config}
    (L : AllocLedger A SL gpv headroom maxReq M)
    (entry : EnvNewEntryState g N A SL phiF phiC st env esp aEnv r m out before)
    (allocator : RuntimeAllocatorState M N phiF phiC alloc exts shared (credits + 1) st.store m)
    (gp : before.σ.regs.get? Register.x3 = some gpv)
    (spill : ∃ v, before.σ.regs.get? Register.x8 = some v) :
    ∃ after p, Steps before after ∧
      EnvNewAllocatorPost g N M phiF phiC alloc exts shared credits
        st env esp r p m out after := by
  have ghostGp : g Register.x3 = some gpv := (entry.frame .x3 (by decide)).symm.trans gp
  have ledger : EnvNewLedger g N A SL phiF phiC st env esp aEnv r m M exts :=
    { gp := ghostGp
      s0_present := by
        obtain ⟨v, hv⟩ := spill
        exact Option.isSome_iff_exists.mpr ⟨v, (entry.frame .x8 (by decide)).symm.trans hv⟩
      ainv_entry := allocator.ainv, stack_hi := entry.facts.stack.2.1
      alloc := L, parents := allocator.parents
      budget := allocator.budget.mono (by omega)
      reserve := allocator.reserve.mono (by omega)
      owned := ⟨alloc, shared, InitialReadableByte, InitialWriteByte SL, allocator.heap,
        fun _ hlo hhi => Or.inr ⟨hlo, hhi⟩⟩ }
  obtain ⟨after, steps, returned⟩ := envNewRetainedReturn_of_ledger ledger allocator.budget allocator.reserve before entry
  obtain ⟨p, savedS0, allocated, facts⟩ := returned.allocation
  have gp' := (returned.exit.frame .x3 (by decide)).trans ghostGp
  exact ⟨after, p, steps,
    { exit := returned.exit, result := facts.initialized.result, fresh := facts.fresh
      allocator := facts.runtime L allocator entry.facts.env_valid gp'
      agreement := facts.shared_agree L allocator gp'
      capacity := (envNewInitializedReads_of_success facts.initialized).capacity, gp := gp' }⟩

#print axioms envNewAllocator_run

end Vsa.Sim
