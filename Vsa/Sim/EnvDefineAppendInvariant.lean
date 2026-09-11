import Vsa.Sim.EnvDefineAppendStoreRun
import Vsa.Sim.AllocRuns

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The append writes touch live data allocations, preserving allocator-private bytes. -/
theorem EnvDefineAppendMemory.allocatorInvariant
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared readable writes : Nat → Prop}
    {store : Store} {target : Addr} {valid : target < store.frames.size}
    {env src copied sp : BitVec 64} {name : String} {v : Value} {cap names vals : Nat}
    {before after : Config} {gpv : BitVec 64} {headroom maxReq : Nat}
    {M : MallocContract A SL gpv headroom maxReq}
    (post : EnvDefineAppendMemory N A phiF phiC env src copied sp store.frames[target].parent
      store.frames[target].vars name v cap names vals before after)
    (heap : HeapOwned A exts before.σ.mem phiF phiC alloc shared readable writes store)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (envAddr : env.toNat = phiF target)
    (capRead : read32 before.σ.mem (phiF target + 4) = some cap)
    (namesRead : read64 before.σ.mem (phiF target + 8) = some names)
    (valuesRead : read64 before.σ.mem (phiF target + 16) = some vals)
    (room : store.frames[target].vars.length < cap)
    (entry : M.AInv before.σ ((copied.toNat, name.length + 1) :: exts))
    (gp : before.σ.regs.get? Register.x3 = after.σ.regs.get? Register.x3) :
    M.AInv after.σ ((copied.toNat, name.length + 1) :: exts) := by
  have frame := heap.store.frames target valid
  obtain ⟨a, fields⟩ := frame.arrays
  have ec := Option.some.inj (fields.capRead.symm.trans capRead)
  have en := Option.some.inj (fields.namesRead.symm.trans namesRead)
  have ev := Option.some.inj (fields.valuesRead.symm.trans valuesRead)
  have hn : Allocated alloc (.names target) names (8 * cap) := by
    simpa only [ec, en] using fields.names.nonempty (by omega : 0 < a.cap)
  have hv : Allocated alloc (.values target) vals (24 * cap) := by
    simpa only [ec, ev] using fields.values.nonempty (by omega : 0 < a.cap)
  have off : ∀ role p n, Allocated alloc role p n → ∀ k, M.privFoot k → k < p ∨ p + n ≤ k := by
    intro role p n allocated k privateByte
    have live := List.mem_cons_of_mem (copied.toNat, name.length + 1) (heap.ledger.live role p n allocated)
    by_cases below : k < p
    · exact Or.inl below
    · by_cases above : p + n ≤ k
      · exact Or.inr above
      · have forbidden := M.privFoot_disjoint before.σ _ entry (p, n) live (k - p) (by omega)
        rw [show p + (k - p) = k by omega] at forbidden
        exact False.elim (forbidden privateByte)
  apply L.ainv_private _ before.σ after.σ gp _ entry
  intro k privateByte
  apply post.agreement
  rw [envAddr]
  have namesOff := off _ _ _ hn k privateByte
  have valuesOff := off _ _ _ hv k privateByte
  have recordOff := off _ _ _ frame.record k privateByte
  unfold AppendUntouched
  exact ⟨by omega, by omega, by omega⟩

#print axioms EnvDefineAppendMemory.allocatorInvariant

end Vsa.Sim
