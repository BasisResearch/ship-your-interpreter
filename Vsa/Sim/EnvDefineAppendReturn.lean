import Vsa.Sim.EnvDefineAppendTail
import Vsa.Sim.EnvDefineAppendOwnership
import Vsa.Sim.EnvDefineAllocatorReturn

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The actual append readback and untouched store footprints give the exact defined store. -/
theorem EnvDefineAppendMemory.store_repr
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared readable writes : Nat → Prop}
    {store : Store} {target : Addr} {valid : target < store.frames.size}
    {env src copied sp : BitVec 64} {name : String} {v : Value} {cap names vals : Nat}
    {before after : Config}
    (post : EnvDefineAppendMemory N A phiF phiC env src copied sp store.frames[target].parent
      store.frames[target].vars name v cap names vals before after)
    (heap : HeapOwned A exts before.σ.mem phiF phiC alloc shared readable writes store)
    (repr : StoreRepr before.σ.mem N A phiF phiC store)
    (envAddr : env.toNat = phiF target)
    (capRead : read32 before.σ.mem (phiF target + 4) = some cap)
    (namesRead : read64 before.σ.mem (phiF target + 8) = some names)
    (valuesRead : read64 before.σ.mem (phiF target + 16) = some vals)
    (room : store.frames[target].vars.length < cap)
    (missing : ∀ i (hi : i < store.frames[target].vars.length), store.frames[target].vars[i].1 ≠ name) :
    StoreRepr after.σ.mem N A phiF phiC (store.define target name v) := by
  have agreement : AgreeP (AppendUntouched (phiF target) names vals store.frames[target].vars.length)
      before.σ.mem after.σ.mem := by rw [← envAddr]; exact post.agreement
  have footprint := StoreAppendFootprint.of_runtime_owned (N := N) valid heap capRead namesRead valuesRead room agreement
  have frame : FrameRepr after.σ.mem N phiF phiC (phiF target)
      ⟨store.frames[target].parent, store.frames[target].vars ++ [(name, v)]⟩ := by
    rw [← envAddr]; exact post.readback.frame
  have advance := storeDefineAdvance_of_append repr
    (Array.getElem?_eq_some_iff.mpr ⟨valid, rfl⟩)
    (any_false_of_miss store.frames[target].vars name missing) frame agreement footprint
  exact advance.toStoreRepr

/-- The append endpoint supplies the full caller return contract from its owned defined store. -/
theorem EnvDefineAppendReturned.toReturn
    {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {A : Arena} {SL : StackLayout} {phiF phiC : Addr → Nat}
    {st : Vsa.While.St} {target : Addr} {valid : target < st.store.frames.size}
    {env src copied esp r : BitVec 64} {name : String} {v : Value} {cap names vals : Nat}
    {m : Mem} {out : Array String} {before after : Config}
    {gpv : BitVec 64} {headroom maxReq : Nat} {M : MallocContract A SL gpv headroom maxReq}
    {alloc : Allocations} {exts : List Extent} {shared : Nat → Prop}
    (post : EnvDefineAppendReturned (envDefineSaved g r) N A phiF phiC env src copied (esp - 64#64)
      st.store.frames[target].parent st.store.frames[target].vars name v cap names vals before after)
    (L : AllocLedger A SL gpv headroom maxReq M)
    (present : EnvDefineSavedPresent g) (ghostSp : g Register.x2 = some esp)
    (retAlign : r.toNat % 4 = 0)
    (heap : HeapOwned A exts after.σ.mem phiF phiC alloc shared InitialReadableByte (InitialWriteByte SL)
      (st.store.define target name v))
    (repr : StoreRepr after.σ.mem N A phiF phiC (st.store.define target name v))
    (memoryFrame : ∀ k, ¬ (A.lo ≤ k ∧ k < A.hi) → ¬ (SL.lo ≤ k ∧ k < esp.toNat) →
      before.σ.mem[k]? = m[k]?)
    (presence : MemExtends m before.σ.mem)
    (output : before.σ.sailOutput = out)
    (rest : ∀ R, AbiPreserved R = true → EnvDefineRestored R = false → R ≠ Register.x2 →
      before.σ.regs.get? R = g R) :
    EnvDefineReturnState g N A SL phiF phiC st target name v esp r m out after := by
  have survives : ∀ m', (∀ k, ¬ (SL.lo ≤ k ∧ k < SL.hi) → after.σ.mem[k]? = m'[k]?) →
      StoreRepr m' N A phiF phiC (st.store.define target name v) := by
    intro m' agree
    apply heap.store.repr_transport repr agree
    · intro role p n allocated k within
      have bounds := (heap.ledger.arena.1 _ (heap.ledger.live role p n allocated)).2
      have separate := L.arena_stack
      change A.lo ≤ p ∧ p + n ≤ A.hi at bounds
      change p ≤ k ∧ k < p + n at within
      omega
    · intro k sharedByte stackByte
      exact heap.immutable.outsideWrites k sharedByte (Or.inr stackByte)
  have returned := post.returned
  have core : EnvDefineReturnCore g N A SL phiF phiC st target name v esp r m after :=
    { good := returned.good, tick := returned.tick
      pc := by rw [returned.pc, envDefineSaved_x1, Option.getD_some, bitvec_update_self r retAlign]
      ra := by rw [returned.ra, envDefineSaved_x1]; rfl
      sp := by rw [returned.spReg, BitVec.sub_add_cancel]
      minstret := returned.good.minstret, restored := returned.restored present
      store := repr, store_survives := survives
      mem_frame := fun k arenaOff stackOff =>
        (post.outsideArena k arenaOff).symm.trans (memoryFrame k arenaOff stackOff)
      mem_extends := presence.trans post.presence }
  exact core.toReturn ghostSp
    { out := post.output.trans output, a0 := post.resultReg
      rest := fun R abi unrestored notSp =>
        (post.rest R abi unrestored notSp).trans (rest R abi unrestored notSp) }

#print axioms EnvDefineAppendMemory.store_repr
#print axioms EnvDefineAppendReturned.toReturn

end Vsa.Sim
