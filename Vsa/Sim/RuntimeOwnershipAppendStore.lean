import Vsa.Sim.RuntimeOwnershipAppendFrame
import Vsa.Sim.RuntimeOwnershipSeparation
import Vsa.Sim.rows.EnvDefineAppendLane

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- Extend the target frame while retaining all other frames and closure data. -/
theorem StoreOwned.append
    {m m' : Mem} {A : Arena} {exts : List Extent} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {shared shared' readable writes : Nat → Prop}
    {store : Store} {target : Addr} {name : String} {v : Value} {copied cap names vals : Nat}
    (h : StoreOwned m phiF phiC alloc shared store)
    (ledger : Ledger A exts alloc) (immutable : Immutable alloc shared readable writes)
    (valid : target < store.frames.size)
    (missing : ∀ i (hi : i < store.frames[target].vars.length), store.frames[target].vars[i].1 ≠ name)
    (capRead : read32 m (phiF target + 4) = some cap)
    (namesRead : read64 m (phiF target + 8) = some names)
    (valuesRead : read64 m (phiF target + 16) = some vals)
    (room : store.frames[target].vars.length < cap)
    (targetFrame : FrameOwned m' phiF
      (alloc.insert (.binding target store.frames[target].vars.length) copied (name.length + 1))
      shared' target { store.frames[target] with vars := store.frames[target].vars ++ [(name, v)] })
    (bounded : ValueClosuresBounded store.closures.size v)
    (agreement : AgreeP (AppendOutside (phiF target) names vals store.frames[target].vars.length) m m')
    (sharedCovered : ∀ k, shared k → AppendOutside (phiF target) names vals store.frames[target].vars.length k)
    (includes : ∀ k, shared k → shared' k) :
    StoreOwned m' phiF phiC
      (alloc.insert (.binding target store.frames[target].vars.length) copied (name.length + 1))
      shared' (store.define target name v) := by
  obtain ⟨frames, closures⟩ := h.appendSeparated ledger immutable target valid cap names vals
    capRead namesRead valuesRead room
  have absent := any_false_of_miss store.frames[target].vars name missing
  refine ⟨?_, ?_, h.valueClosures.define bounded, ?_, ?_⟩
  · intro fa hf
    have hf0 : fa < store.frames.size := by simpa [Store.define] using hf
    by_cases same : fa = target
    · subst fa
      simpa only [Store.define, Array.getElem_modify, if_pos, absent, Bool.false_eq_true, if_false]
        using targetFrame
    · have original := ((h.frames fa hf0).transport agreement (frames fa hf0 same)
        sharedCovered).mono_shared includes
      have retained : FrameOwned m' phiF
          (alloc.insert (.binding target store.frames[target].vars.length) copied (name.length + 1))
          shared' fa store.frames[fa] := original.congrAlloc
        (Allocations.insert_other (by intro eq; cases eq))
        (Allocations.insert_other (by intro eq; cases eq))
        (Allocations.insert_other (by intro eq; cases eq))
        (fun i => Allocations.insert_other (by intro eq; exact same (Role.binding.inj eq).1))
      simpa [Store.define, Array.getElem_modify, same, Ne.symm same] using retained
  · intro ca hc
    show alloc.insert (.binding target store.frames[target].vars.length) copied
      (name.length + 1) (.closure ca) = _
    rw [Allocations.insert_other (by intro eq; cases eq)]
    exact h.closures ca hc
  · intro ca hc
    simpa [Store.define] using h.capturedEnvs ca hc
  · intro ca hc q read k within
    have footprint := closures ca hc
    have header := (extent_covers footprint.header (by decide : 0 + 8 ≤ 16)).read64_eq agreement
    have originalRead : read64 m (phiC ca) = some q := by simpa using header.trans read
    apply includes
    exact h.closureAsts ca hc q originalRead k
      (within.pullback agreement (fun j hj => sharedCovered j (h.closureAsts ca hc q originalRead j hj)))

#print axioms StoreOwned.append

end Vsa.Sim.RuntimeOwnership
