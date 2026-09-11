import Vsa.Sim.RuntimeOwnershipUpdate
import Vsa.Sim.RuntimeOwnershipInitial

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- A hit preserves array alignment and replaces exactly one readable value slot. -/
theorem StoreArraysReady.defineHit
    {m m' : Mem} {N : NativeAddrs} {A : Arena} {exts : List Extent}
    {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {store : Store}
    {target : Addr} {name : String} {v : Value} {hit vals : Nat}
    (h : StoreArraysReady m phiF store)
    (owned : HeapOwned A exts m phiF phiC alloc shared readable writes store)
    (ht : target < store.frames.size)
    (hhit : hit < store.frames[target].vars.length)
    (hmatch : store.frames[target].vars[hit].1 = name)
    (hvals : read64 m (phiF target + 16) = some vals)
    (word : ValueWordsTotal m' (vals + 24 * hit))
    (agreement : AgreeP (SetOutside (vals + 24 * hit)) m m') :
    StoreArraysReady m' phiF (store.define target name v) := by
  have targetShell := StoreSetFootprint.target_of_runtime_owned (N := N)
    ht hhit hvals rfl owned
  have otherShells := StoreSetFootprint.of_runtime_owned (N := N)
    ht hhit hvals rfl owned agreement
  have headers : ∀ fa, fa < store.frames.size → ∀ k,
      envHeader (phiF fa) k → SetOutside (vals + 24 * hit) k := by
    intro fa hf k hk
    by_cases same : fa = target
    · subst fa; exact targetShell.header k hk
    · exact (otherShells.frames fa hf same).header k hk
  have namesRead : ∀ fa, fa < store.frames.size →
      read64 m (phiF fa + 8) = read64 m' (phiF fa + 8) := by
    intro fa hf
    exact (extent_covers (headers fa hf) (by decide : 8 + 8 ≤ 32)).read64_eq agreement
  have valuesRead : ∀ fa, fa < store.frames.size →
      read64 m (phiF fa + 16) = read64 m' (phiF fa + 16) := by
    intro fa hf
    exact (extent_covers (headers fa hf) (by decide : 16 + 8 ≤ 32)).read64_eq agreement
  have sizeEq : (store.define target name v).frames.size = store.frames.size := by
    simp [Store.define]
  have lengths : ∀ fa, (hf : fa < store.frames.size) →
      ((store.define target name v).frames[fa]'(by omega)).vars.length =
        store.frames[fa].vars.length := by
    intro fa hf
    by_cases same : fa = target
    · subst fa
      simp only [Store.define, Array.getElem_modify, if_pos,
        any_true_of_hit store.frames[target] name hit hhit hmatch, List.length_map]
    · simp [Store.define, Array.getElem_modify, Ne.symm same]
  refine
    { namesAligned := fun fa hf pn hp =>
        h.namesAligned fa (by omega) pn ((namesRead fa (by omega)).trans hp)
      valuesAligned := fun fa hf pv hp =>
        h.valuesAligned fa (by omega) pv ((valuesRead fa (by omega)).trans hp)
      valueWords := ?_ }
  intro fa hf pv hp i hi
  have hf0 : fa < store.frames.size := by omega
  have hi0 : i < store.frames[fa].vars.length := by rw [lengths fa hf0] at hi; exact hi
  have hp0 := (valuesRead fa hf0).trans hp
  obtain ⟨arrays, fields⟩ := (owned.store.frames fa hf0).arrays
  by_cases same : fa = target
  · subst fa
    have eq : pv = vals := Option.some.inj (hp0.symm.trans hvals)
    subst pv
    by_cases selected : i = hit
    · subst i; exact word
    · exact valueWordsTotal_transport (h.valueWords target hf0 vals hp0 i hi0)
        agreement (targetShell.otherValueHeaders arrays.names vals
          fields.namesRead hp0 i hi0 selected)
  · exact valueWordsTotal_transport (h.valueWords fa hf0 pv hp0 i hi0) agreement
      ((otherShells.frames fa hf0 same).slots arrays.names pv fields.namesRead hp0 i hi0).2

#print axioms StoreArraysReady.defineHit

end Vsa.Sim.RuntimeOwnership
