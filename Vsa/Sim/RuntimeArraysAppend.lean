import Vsa.Sim.RuntimeOwnershipInitial
import Vsa.Sim.RuntimeOwnershipSeparation
import Vsa.Sim.RuntimeOwnershipTransport
import Vsa.Sim.rows.EnvDefineAppendLane

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- Appending one binding retains array alignment and initializes its three copied words. -/
theorem StoreArraysReady.defineAppend
    {m m' : Mem} {A : Arena} {exts : List Extent} {phiF phiC : Addr → Nat}
    {alloc : Allocations} {shared readable writes : Nat → Prop}
    {store : Store} {target : Addr} {name : String} {v : Value} {cap names vals : Nat}
    (h : StoreArraysReady m phiF store)
    (heap : HeapOwned A exts m phiF phiC alloc shared readable writes store)
    (valid : target < store.frames.size)
    (missing : ∀ i (hi : i < store.frames[target].vars.length), store.frames[target].vars[i].1 ≠ name)
    (capRead : read32 m (phiF target + 4) = some cap)
    (namesRead : read64 m (phiF target + 8) = some names)
    (valuesRead : read64 m (phiF target + 16) = some vals)
    (room : store.frames[target].vars.length < cap)
    (newNamesRead : read64 m' (phiF target + 8) = some names)
    (newValuesRead : read64 m' (phiF target + 16) = some vals)
    (newWord : ValueWordsTotal m' (vals + 24 * store.frames[target].vars.length))
    (agreement : AgreeP (AppendOutside (phiF target) names vals store.frames[target].vars.length) m m')
    (oldValues : ∀ i, i < store.frames[target].vars.length → ∀ k,
      valHeader (vals + 24 * i) k → AppendOutside (phiF target) names vals store.frames[target].vars.length k) :
    StoreArraysReady m' phiF (store.define target name v) := by
  obtain ⟨frames, _⟩ := heap.store.appendSeparated heap.ledger heap.immutable target valid cap names vals
    capRead namesRead valuesRead room
  have absent := any_false_of_miss store.frames[target].vars name missing
  have sizeEq : (store.define target name v).frames.size = store.frames.size := by simp [Store.define]
  have nameHeaders : ∀ fa, fa < store.frames.size →
      read64 m (phiF fa + 8) = read64 m' (phiF fa + 8) := by
    intro fa hf
    by_cases same : fa = target
    · subst fa; exact namesRead.trans newNamesRead.symm
    · exact (extent_covers (frames fa hf same).header (by decide : 8 + 8 ≤ 32)).read64_eq agreement
  have valueHeaders : ∀ fa, fa < store.frames.size →
      read64 m (phiF fa + 16) = read64 m' (phiF fa + 16) := by
    intro fa hf
    by_cases same : fa = target
    · subst fa; exact valuesRead.trans newValuesRead.symm
    · exact (extent_covers (frames fa hf same).header (by decide : 16 + 8 ≤ 32)).read64_eq agreement
  refine
    { namesAligned := fun fa hf pn read => h.namesAligned fa (by omega) pn
        ((nameHeaders fa (by omega)).trans read)
      valuesAligned := fun fa hf pv read => h.valuesAligned fa (by omega) pv
        ((valueHeaders fa (by omega)).trans read)
      valueWords := ?_ }
  intro fa hf pv read i hi
  have hf0 : fa < store.frames.size := by omega
  have oldRead := (valueHeaders fa hf0).trans read
  by_cases same : fa = target
  · subst fa
    have eq := Option.some.inj (oldRead.symm.trans valuesRead)
    subst pv
    have bound : i < store.frames[target].vars.length + 1 := by
      simpa [Store.define, Array.getElem_modify, absent] using hi
    by_cases old : i < store.frames[target].vars.length
    · exact valueWordsTotal_transport (h.valueWords target valid vals valuesRead i old)
        agreement (oldValues i old)
    · have eq : i = store.frames[target].vars.length := by omega
      subst i; exact newWord
  · have hi0 : i < store.frames[fa].vars.length := by
      simpa [Store.define, Array.getElem_modify, same, Ne.symm same] using hi
    obtain ⟨arrays, fields⟩ := (heap.store.frames fa hf0).arrays
    exact valueWordsTotal_transport (h.valueWords fa hf0 pv oldRead i hi0) agreement
      ((frames fa hf0 same).slots arrays.names pv fields.namesRead oldRead i hi0).2

#print axioms StoreArraysReady.defineAppend

end Vsa.Sim.RuntimeOwnership
