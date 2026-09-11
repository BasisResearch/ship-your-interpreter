import Vsa.Sim.RuntimeOwnershipArrays
import Vsa.Sim.rows.StoreWF
import Vsa.Sim.rows.CallClosureEnvNewMarshal

namespace Vsa.Sim.RuntimeOwnership

open Vsa Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

/-- A frame uses its map only at its own semantic address. -/
theorem FrameOwned.congrFrameMap
    {m : Mem} {phiF phiF' : Addr → Nat} {alloc : Allocations} {shared : Nat → Prop}
    {fa : Addr} {f : Vsa.While.Frame} (h : FrameOwned m phiF alloc shared fa f)
    (same : phiF' fa = phiF fa) : FrameOwned m phiF' alloc shared fa f := by
  obtain ⟨a, arrays⟩ := h.arrays
  refine
    { record := by rw [same]; exact h.record
      arrays := ⟨a,
        { capRead := by rw [same]; exact arrays.capRead
          namesRead := by rw [same]; exact arrays.namesRead
          valuesRead := by rw [same]; exact arrays.valuesRead
          bound := arrays.bound, names := arrays.names, values := arrays.values
          keys := arrays.keys }⟩
      values := ?_ }
  intro pv read i hi
  rw [same] at read
  exact h.values pv read i hi

/-- Insert the initialized empty frame while retaining every old allocation role. -/
theorem StoreOwned.pushFrame
    {m : Mem} {phiF phiF' phiC : Addr → Nat} {alloc : Allocations}
    {shared : Nat → Prop} {s : Store} {parent : Option Addr} {p : Nat}
    (h : StoreOwned m phiF phiC alloc shared s)
    (extension : PhiExtends phiF phiF' s.frames.size)
    (fresh : FrameOwned m phiF' (alloc.insert (.frame s.frames.size) p 32)
      shared s.frames.size ⟨parent, []⟩) :
    StoreOwned m phiF' phiC (alloc.insert (.frame s.frames.size) p 32)
      shared (s.allocFrame parent).1 := by
  refine
    { frames := ?_
      closures := ?_
      valueClosures := StoreClosuresBounded.allocFrame rfl h.valueClosures
      capturedEnvs := ?_
      closureAsts := h.closureAsts }
  · intro fa hf
    have bound : fa < s.frames.size + 1 := by simpa [Store.allocFrame] using hf
    by_cases old : fa < s.frames.size
    · have same : (s.allocFrame parent).1.frames[fa]'hf = s.frames[fa] :=
        Array.getElem_push_lt old
      rw [same]
      apply ((h.frames fa old).congrFrameMap (extension fa old)).congrAlloc
      · apply Allocations.insert_other
        intro equal
        have : fa = s.frames.size := by cases equal; rfl
        omega
      · exact Allocations.insert_other (by intro equal; cases equal)
      · exact Allocations.insert_other (by intro equal; cases equal)
      · intro i
        exact Allocations.insert_other (by intro equal; cases equal)
    · have same : fa = s.frames.size := by omega
      subst fa
      have pushed : (s.allocFrame parent).1.frames[s.frames.size]'hf = ⟨parent, []⟩ :=
        Array.getElem_push_eq
      rw [pushed]
      exact fresh
  · intro ca hc
    show alloc.insert (.frame s.frames.size) p 32 (.closure ca) = _
    rw [Allocations.insert_other (by intro equal; cases equal)]
    exact h.closures ca hc
  · intro ca hc
    exact Nat.lt_trans (h.capturedEnvs ca hc)
      (by simpa [Store.allocFrame] using Nat.lt_succ_self s.frames.size)

/-- Canonical NULL arrays make the new frame immediately ready for lookups. -/
theorem StoreArraysReady.pushFrame
    {m : Mem} {phiF phiF' : Addr → Nat} {s : Store} {parent : Option Addr} {p : Nat}
    (h : StoreArraysReady m phiF s)
    (extension : PhiExtends phiF phiF' s.frames.size) (address : phiF' s.frames.size = p)
    (namesNull : read64 m (p + 8) = some 0) (valuesNull : read64 m (p + 16) = some 0) :
    StoreArraysReady m phiF' (s.allocFrame parent).1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro fa hf pn read
    have bound : fa < s.frames.size + 1 := by simpa [Store.allocFrame] using hf
    by_cases old : fa < s.frames.size
    · rw [extension fa old] at read
      exact h.namesAligned fa old pn read
    · have same : fa = s.frames.size := by omega
      subst fa
      rw [address, namesNull] at read
      have zero : pn = 0 := Option.some.inj read.symm
      rw [zero]
  · intro fa hf pv read
    have bound : fa < s.frames.size + 1 := by simpa [Store.allocFrame] using hf
    by_cases old : fa < s.frames.size
    · rw [extension fa old] at read
      exact h.valuesAligned fa old pv read
    · have same : fa = s.frames.size := by omega
      subst fa
      rw [address, valuesNull] at read
      have zero : pv = 0 := Option.some.inj read.symm
      rw [zero]
  · intro fa hf pv read i hi
    have bound : fa < s.frames.size + 1 := by simpa [Store.allocFrame] using hf
    by_cases old : fa < s.frames.size
    · rw [extension fa old] at read
      have same : (s.allocFrame parent).1.frames[fa]'hf = s.frames[fa] :=
        Array.getElem_push_lt old
      rw [same] at hi
      exact h.valueWords fa old pv read i hi
    · have same : fa = s.frames.size := by omega
      subst fa
      have pushed : (s.allocFrame parent).1.frames[s.frames.size]'hf = ⟨parent, []⟩ :=
        Array.getElem_push_eq
      rw [pushed] at hi
      exact False.elim (Nat.not_lt_zero i hi)

#print axioms FrameOwned.congrFrameMap
#print axioms StoreOwned.pushFrame
#print axioms StoreArraysReady.pushFrame

end Vsa.Sim.RuntimeOwnership
