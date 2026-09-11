import Vsa.Sim.EnvDefineAppendStoreRun
import Vsa.Sim.RuntimeOwnershipAppendStore
import Vsa.Sim.RuntimeOwnershipBinding
import Vsa.Sim.RuntimeOwnershipCopy

namespace Vsa.Sim

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While
open RuntimeOwnership

/-- The three append write windows avoid all previously shared bytes. -/
theorem RuntimeOwnership.FrameOwned.sharedOutsideAppend
    {m : Mem} {phiF : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {target : Addr} {f : Vsa.While.Frame}
    {cap names vals : Nat}
    (h : FrameOwned m phiF alloc shared target f)
    (immutable : Immutable alloc shared readable writes)
    (capRead : read32 m (phiF target + 4) = some cap)
    (namesRead : read64 m (phiF target + 8) = some names)
    (valuesRead : read64 m (phiF target + 16) = some vals)
    (room : f.vars.length < cap) :
    ∀ k, shared k → AppendUntouched (phiF target) names vals f.vars.length k := by
  obtain ⟨a, fields⟩ := h.arrays
  have ec := Option.some.inj (fields.capRead.symm.trans capRead)
  have en := Option.some.inj (fields.namesRead.symm.trans namesRead)
  have ev := Option.some.inj (fields.valuesRead.symm.trans valuesRead)
  have hn : Allocated alloc (.names target) names (8 * cap) := by
    simpa only [ec, en] using fields.names.nonempty (by omega : 0 < a.cap)
  have hv : Allocated alloc (.values target) vals (24 * cap) := by
    simpa only [ec, ev] using fields.values.nonempty (by omega : 0 < a.cap)
  have nsub : ∀ k, names + 8 * f.vars.length ≤ k ∧ k < names + 8 * f.vars.length + 8 →
      ExtentByte (names, 8 * cap) k := by intro k hk; change names ≤ k ∧ k < names + 8 * cap; omega
  have vsub : ∀ k, vals + 24 * f.vars.length ≤ k ∧ k < vals + 24 * f.vars.length + 24 →
      ExtentByte (vals, 24 * cap) k := by intro k hk; change vals ≤ k ∧ k < vals + 24 * cap; omega
  have rsub : ∀ k, phiF target ≤ k ∧ k < phiF target + 4 →
      ExtentByte (phiF target, 32) k := by intro k hk; change phiF target ≤ k ∧ k < phiF target + 32; omega
  intro k hk
  exact ⟨immutable.outsideWindow (by trivial) hn nsub k hk,
    immutable.outsideWindow (by trivial) hv vsub k hk,
    immutable.outsideWindow (by trivial) h.record rsub k hk⟩

/-- The actual append stores assign and freeze the copied name while extending the owned store. -/
theorem EnvDefineAppendMemory.heap_owned
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {exts : List Extent} {shared readable writes : Nat → Prop}
    {store : Store} {target : Addr} {valid : target < store.frames.size}
    {env src copied sp : BitVec 64} {name : String} {v : Value} {cap names vals : Nat}
    {before after : Config}
    (post : EnvDefineAppendMemory N A phiF phiC env src copied sp store.frames[target].parent
      store.frames[target].vars name v cap names vals before after)
    (heap : HeapOwned A exts before.σ.mem phiF phiC alloc shared readable writes store)
    (envAddr : env.toNat = phiF target)
    (capRead : read32 before.σ.mem (phiF target + 4) = some cap)
    (namesRead : read64 before.σ.mem (phiF target + 8) = some names)
    (valuesRead : read64 before.σ.mem (phiF target + 16) = some vals)
    (room : store.frames[target].vars.length < cap)
    (missing : ∀ i (hi : i < store.frames[target].vars.length), store.frames[target].vars[i].1 ≠ name)
    (source : ValueOwned before.σ.mem shared src.toNat v)
    (bounded : ValueClosuresBounded store.closures.size v)
    (arena : A.contains copied.toNat (name.length + 1))
    (fresh : ∀ e ∈ exts, ExtDisjoint (copied.toNat, name.length + 1) e)
    (readableNew : ∀ k, ExtentByte (copied.toNat, name.length + 1) k → readable k)
    (outsideWrites : ∀ k, ExtentByte (copied.toNat, name.length + 1) k → ¬ writes k) :
    HeapOwned A ((copied.toNat, name.length + 1) :: exts) after.σ.mem phiF phiC
      (alloc.insert (.binding target store.frames[target].vars.length) copied.toNat (name.length + 1))
      (BindingShared shared copied.toNat (name.length + 1)) readable writes (store.define target name v) := by
  have frame := heap.store.frames target valid
  have sharedOff := frame.sharedOutsideAppend heap.immutable capRead namesRead valuesRead room
  have agreement : AgreeP (AppendUntouched (phiF target) names vals store.frames[target].vars.length)
      before.σ.mem after.σ.mem := by rw [← envAddr]; exact post.agreement
  have sharedAgreement : AgreeP shared before.σ.mem after.σ.mem := fun k hk => agreement k (sharedOff k hk)
  have footprint := appendFootprint_of_owned heap valid capRead namesRead valuesRead room fresh
    (Nat.le_refl (name.length + 1)) source
  obtain ⟨a, fields⟩ := frame.arrays
  have capEq := Option.some.inj (fields.capRead.symm.trans capRead)
  have namesEq := Option.some.inj (fields.namesRead.symm.trans namesRead)
  have valuesEq := Option.some.inj (fields.valuesRead.symm.trans valuesRead)
  have arraysEq : a = ⟨cap, names, vals⟩ := by cases a; simp_all
  rw [arraysEq] at fields
  have newName : SharedCString after.σ.mem (BindingShared shared copied.toNat (name.length + 1))
      copied.toNat name :=
    ⟨post.nameString, fun k hk => Or.inr (by unfold ExtentByte; omega)⟩
  have newValue := (source.copy_total post.copy sharedAgreement).mono
    (fun k hk => Or.inl hk : ∀ k, shared k → BindingShared shared copied.toNat (name.length + 1) k)
  have targetFrame := frame.append fields room
    (by rw [← envAddr]; exact post.readback.capRead)
    (by rw [← envAddr]; exact post.readback.namesRead)
    (by rw [← envAddr]; exact post.readback.valsRead)
    post.nameRead newName newValue agreement footprint.oldNameSlots footprint.oldValueHeaders sharedOff
    (fun k hk => Or.inl hk)
  exact
    { ledger := heap.ledger.insert (by omega) arena fresh
      immutable := heap.immutable.binding heap.ledger heap.reserved arena fresh readableNew outsideWrites
      reserved := heap.reserved.binding
      store := heap.store.append heap.ledger heap.immutable valid missing capRead namesRead valuesRead room
        targetFrame bounded agreement sharedOff (fun k hk => Or.inl hk) }

#print axioms RuntimeOwnership.FrameOwned.sharedOutsideAppend
#print axioms EnvDefineAppendMemory.heap_owned

end Vsa.Sim
