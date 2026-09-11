import Vsa.Sim.RuntimeOwnershipArrays
import Vsa.Sim.RuntimeOwnershipInitial
import Vsa.Sim.RuntimeOwnershipTransport

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- A copied value slot retains all three readable words. -/
theorem valueWordsTotal_shift {m m' : Mem} {src dst : Nat}
    (h : ValueWordsTotal m src)
    (copy : ∀ k, k < 24 → m'[dst + k]? = m[src + k]?) : ValueWordsTotal m' dst := by
  have reads : ∀ off, off + 8 ≤ 24 → read64 m' (dst + off) = read64 m (src + off) := by
    intro off bound
    apply read64_shift
    intro k hk
    rw [show dst + off + k = dst + (off + k) by omega,
      show src + off + k = src + (off + k) by omega]
    exact copy (off + k) (by omega)
  obtain ⟨a, b, c, ha, hb, hc⟩ := h
  exact ⟨a, b, c, (by simpa using (reads 0 (by decide)).trans ha),
    (reads 8 (by decide)).trans hb, (reads 16 (by decide)).trans hc⟩

/-- Reallocated arrays retain alignment and readable occupied value slots. -/
theorem StoreArraysReady.replaceArrays
    {m m' : Mem} {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared P : Nat → Prop} {store : Store} {target : Addr} {pv pn' pv' : Nat}
    (h : StoreArraysReady m phiF store)
    (owned : StoreOwned m phiF phiC alloc shared store)
    (valid : target < store.frames.size)
    (oldValues : read64 m (phiF target + 16) = some pv)
    (namesRead : read64 m' (phiF target + 8) = some pn')
    (valuesRead : read64 m' (phiF target + 16) = some pv')
    (namesAligned : pn' % 8 = 0) (valuesAligned : pv' % 8 = 0)
    (agreement : AgreeP P m m')
    (other : ∀ role q n, role ≠ .frame target → role ≠ .names target → role ≠ .values target →
      Allocated alloc role q n → ∀ k, ExtentByte (q, n) k → P k)
    (sharedCovered : ∀ k, shared k → P k)
    (copy : ∀ i, i < store.frames[target].vars.length → ∀ k, k < 24 →
      m'[pv' + 24 * i + k]? = m[pv + 24 * i + k]?) :
    StoreArraysReady m' phiF store := by
  have otherFrame : ∀ fa (hf : fa < store.frames.size), fa ≠ target →
      FrameFootprintCovered m phiF fa store.frames[fa] P := by
    intro fa hf ne
    apply (owned.frames fa hf).footprint
    · exact other (.frame fa) _ _ (fun e => ne (Role.frame.inj e)) nofun nofun
        (owned.frames fa hf).record
    · intro q n allocated
      rcases allocated with names | values
      · exact other (.names fa) q n nofun (fun e => ne (Role.names.inj e)) nofun names
      · exact other (.values fa) q n nofun nofun (fun e => ne (Role.values.inj e)) values
    · exact sharedCovered
  refine ⟨?_, ?_, ?_⟩
  · intro fa hf pn read
    by_cases same : fa = target
    · subst fa
      have eq := Option.some.inj (read.symm.trans namesRead)
      subst pn; exact namesAligned
    · have eq := (extent_covers (otherFrame fa hf same).header
        (by decide : 8 + 8 ≤ 32)).read64_eq agreement
      exact h.namesAligned fa hf pn (eq.trans read)
  · intro fa hf vals read
    by_cases same : fa = target
    · subst fa
      have eq := Option.some.inj (read.symm.trans valuesRead)
      subst vals; exact valuesAligned
    · have eq := (extent_covers (otherFrame fa hf same).header
        (by decide : 16 + 8 ≤ 32)).read64_eq agreement
      exact h.valuesAligned fa hf vals (eq.trans read)
  · intro fa hf vals read i hi
    by_cases same : fa = target
    · subst fa
      have eq := Option.some.inj (read.symm.trans valuesRead)
      subst vals
      exact valueWordsTotal_shift (h.valueWords target valid pv oldValues i hi) (copy i hi)
    · have footprint := otherFrame fa hf same
      have eq := (extent_covers footprint.header (by decide : 16 + 8 ≤ 32)).read64_eq agreement
      have oldRead := eq.trans read
      obtain ⟨arrays, fields⟩ := (owned.frames fa hf).arrays
      exact valueWordsTotal_transport (h.valueWords fa hf vals oldRead i hi) agreement
        (footprint.slots arrays.names vals fields.namesRead oldRead i hi).2

#print axioms valueWordsTotal_shift
#print axioms StoreArraysReady.replaceArrays

end Vsa.Sim.RuntimeOwnership
