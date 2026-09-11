import Vsa.Sim.RuntimeOwnershipShared
import Vsa.Sim.RuntimeOwnershipArrays
import Vsa.Sim.RuntimeOwnershipTransport
import Vsa.Sim.rows.EnvDefineAppendExact

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- Existing frame data survives extension of the immutable byte domain. -/
theorem FrameOwned.mono_shared
    {m : Mem} {phiF : Addr → Nat} {alloc : Allocations} {shared shared' : Nat → Prop}
    {fa : Addr} {f : Vsa.While.Frame}
    (h : FrameOwned m phiF alloc shared fa f) (includes : ∀ k, shared k → shared' k) :
    FrameOwned m phiF alloc shared' fa f := by
  obtain ⟨a, arrays⟩ := h.arrays
  refine ⟨h.record, ⟨a, arrays.capRead, arrays.namesRead, arrays.valuesRead,
    arrays.bound, arrays.names, arrays.values, ?_⟩, ?_⟩
  · intro i hi
    obtain ⟨q, read, key⟩ := arrays.keys i hi
    exact ⟨q, read, ⟨key.allocated, key.immutable.mono includes⟩⟩
  · intro vals read i hi
    exact (h.values vals read i hi).mono includes

/-- The new terminal name and value slots extend the target frame's ownership. -/
theorem FrameOwned.append
    {m m' : Mem} {phiF : Addr → Nat} {alloc : Allocations}
    {shared shared' P : Nat → Prop} {fa : Addr} {f : Vsa.While.Frame}
    {name : String} {v : Value} {copied : Nat} {a : ArrayState}
    (h : FrameOwned m phiF alloc shared fa f)
    (arrays : FrameArraysOwned m phiF alloc shared fa f a)
    (room : f.vars.length < a.cap)
    (capRead : read32 m' (phiF fa + 4) = some a.cap)
    (namesRead : read64 m' (phiF fa + 8) = some a.names)
    (valuesRead : read64 m' (phiF fa + 16) = some a.values)
    (newNameRead : read64 m' (a.names + 8 * f.vars.length) = some copied)
    (newName : SharedCString m' shared' copied name)
    (newValue : ValueOwned m' shared' (a.values + 24 * f.vars.length) v)
    (agreement : AgreeP P m m')
    (oldNames : ∀ i, i < f.vars.length → ∀ k, k < 8 → P (a.names + 8 * i + k))
    (oldValues : ∀ i, i < f.vars.length → ∀ k, valHeader (a.values + 24 * i) k → P k)
    (sharedCovered : ∀ k, shared k → P k)
    (includes : ∀ k, shared k → shared' k) :
    FrameOwned m' phiF (alloc.insert (.binding fa f.vars.length) copied (name.length + 1))
      shared' fa { f with vars := f.vars ++ [(name, v)] } := by
  let alloc' := alloc.insert (.binding fa f.vars.length) copied (name.length + 1)
  have sharedAgreement : AgreeP shared m m' := fun k hk => agreement k (sharedCovered k hk)
  have oldBinding : ∀ i, i < f.vars.length →
      alloc' (.binding fa i) = alloc (.binding fa i) := by
    intro i hi
    apply Allocations.insert_other
    intro eq
    have := (Role.binding.inj eq).2
    omega
  refine ⟨?_, ⟨a, capRead, namesRead, valuesRead, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show alloc' (.frame fa) = _
    dsimp only [alloc']
    rw [Allocations.insert_other (by intro eq; cases eq)]
    exact h.record
  · simp only [List.length_append, List.length_singleton]
    omega
  · exact arrays.names.congr (Allocations.insert_other (by intro eq; cases eq))
  · exact arrays.values.congr (Allocations.insert_other (by intro eq; cases eq))
  · intro i hi
    by_cases old : i < f.vars.length
    · obtain ⟨q, read, key⟩ := arrays.keys i old
      have read' : read64 m' (a.names + 8 * i) = some q :=
        (read64_agreeP agreement (oldNames i old)).symm.trans read
      refine ⟨q, read', ?_⟩
      simp only [List.getElem_append_left old]
      exact ⟨by show alloc' (.binding fa i) = _; rw [oldBinding i old]; exact key.allocated,
        (key.immutable.transport sharedAgreement).mono includes⟩
    · have eq : i = f.vars.length := by
        simp only [List.length_append, List.length_singleton] at hi; omega
      subst i
      simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_cons_zero]
      exact ⟨copied, newNameRead, ⟨Allocations.insert_same, newName⟩⟩
  · intro vals read i hi
    have eq := Option.some.inj (read.symm.trans valuesRead)
    subst vals
    by_cases old : i < f.vars.length
    · simp only [List.getElem_append_left old]
      exact ((h.values a.values arrays.valuesRead i old).transport
        agreement (oldValues i old) sharedCovered).mono includes
    · have eq : i = f.vars.length := by
        simp only [List.length_append, List.length_singleton] at hi; omega
      subst i
      simpa only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
        List.getElem_cons_zero] using newValue

#print axioms FrameOwned.mono_shared
#print axioms FrameOwned.append

end Vsa.Sim.RuntimeOwnership
