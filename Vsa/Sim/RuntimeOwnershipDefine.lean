import Vsa.Sim.RuntimeOwnershipTransport
import Vsa.Sim.RuntimeOwnershipSeparation
import Vsa.Sim.EnvDefSpec3
import Vsa.Sim.rows.StoreWF

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- A hit update retains frame allocations and copied keys, replacing only
one value's ownership. Name uniqueness identifies the semantic update slot. -/
theorem FrameOwned.defineHit {m m' : Mem} {phiF : Addr → Nat}
    {alloc : Allocations} {shared P : Nat → Prop} {fa : Addr}
    {f : Vsa.While.Frame} {name : String} {v : Value} {hit vals : Nat}
    (h : FrameOwned m phiF alloc shared fa f)
    (hhit : hit < f.vars.length) (hmatch : f.vars[hit].1 = name)
    (huniq : FrameUnique f)
    (hvals : read64 m (phiF fa + 16) = some vals)
    (hnew : ValueOwned m' shared (vals + 24 * hit) v)
    (hag : AgreeP P m m')
    (hf : TargetFrameFootprintCovered m phiF fa f hit P)
    (hs : ∀ k, shared k → P k) :
    FrameOwned m' phiF alloc shared fa
      { f with vars := if f.vars.any (·.1 == name) then
          f.vars.map fun p => if p.1 == name then (name, v) else p
        else f.vars ++ [(name, v)] } := by
  simp only [any_true_of_hit f name hit hhit hmatch, if_true]
  have hc := (extent_covers hf.header (by decide : 4 + 4 ≤ 32)).read32_eq hag
  have hn := (extent_covers hf.header (by decide : 8 + 8 ≤ 32)).read64_eq hag
  have hv := (extent_covers hf.header (by decide : 16 + 8 ≤ 32)).read64_eq hag
  obtain ⟨a, arrays⟩ := h.arrays
  refine ⟨h.record, ⟨a, ?_⟩, ?_⟩
  · refine ⟨hc.symm.trans arrays.capRead, hn.symm.trans arrays.namesRead,
      hv.symm.trans arrays.valuesRead, ?_, arrays.names, arrays.values, ?_⟩
    · simpa only [List.length_map] using arrays.bound
    · intro i hi
      have hi0 : i < f.vars.length := by simpa only [List.length_map] using hi
      obtain ⟨q, hq, key⟩ := arrays.keys i hi0
      have heq := read64_agreeP hag
        (hf.nameSlots a.names a.values arrays.namesRead arrays.valuesRead i hi0)
      have hname : ((f.vars.map fun p => if p.1 == name then (name, v) else p)[i]).1
          = f.vars[i].1 := by
        rw [List.getElem_map]
        by_cases he : f.vars[i].1 == name
        · simp only [if_pos he]; exact (beq_iff_eq.mp he).symm
        · simp only [if_neg he]
      refine ⟨q, heq.symm.trans hq, ?_⟩
      rw [hname]
      exact ⟨key.allocated, key.immutable.transport (fun k hk => hag k (hs k hk))⟩
  · intro pv hpv i hi
    have hi0 : i < f.vars.length := by simpa only [List.length_map] using hi
    have hpv0 := hv.trans hpv
    have he := define_update_first_getElem f name v hit hhit hmatch huniq i hi0
    change ValueOwned m' shared (pv + 24 * i) ((f.vars.map fun p => if p.1 == name then (name, v) else p)[i]).2
    rw [he]
    by_cases heq : i = hit
    · subst i
      rw [if_pos rfl]
      have ep : pv = vals := Option.some.inj (hpv0.symm.trans hvals)
      simpa only [ep] using hnew
    · rw [if_neg heq]
      exact (h.values pv hpv0 i hi0).transport hag
        (hf.otherValueHeaders a.names pv arrays.namesRead hpv0 i hi0 heq) hs

/-- Reconstruct the exact semantic store after a one-slot hit update.
The allocation ledger is unchanged; untouched frames and closure ASTs survive
through the footprint derived from the existing runtime ownership. -/
theorem HeapOwned.defineHit
    {m m' : Mem} {A : Arena} {exts : List Extent}
    {phiF phiC : Addr → Nat} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {store : Store}
    {target : Addr} {name : String} {v : Value} {hit vals : Nat}
    (h : HeapOwned A exts m phiF phiC alloc shared readable writes store)
    (ht : target < store.frames.size)
    (hhit : hit < store.frames[target].vars.length)
    (hmatch : store.frames[target].vars[hit].1 = name)
    (huniq : FrameUnique store.frames[target])
    (hvals : read64 m (phiF target + 16) = some vals)
    (hnew : ValueOwned m' shared (vals + 24 * hit) v)
    (hbounded : ValueClosuresBounded store.closures.size v)
    (hag : AgreeP (SetOutside (vals + 24 * hit)) m m') :
    HeapOwned A exts m' phiF phiC alloc shared readable writes
      (store.define target name v) := by
  obtain ⟨htarget, hframes, hclosures⟩ :=
    h.store.setSeparated h.ledger h.immutable target ht hit hhit vals hvals
  have hshared : ∀ k, shared k → SetOutside (vals + 24 * hit) k :=
    (h.store.frames target ht).sharedOutsideSet h.immutable hhit hvals
  refine ⟨h.ledger, h.immutable, h.reserved, ?_⟩
  refine ⟨?_, ?_, h.store.valueClosures.define hbounded, ?_, ?_⟩
  · intro fa hfa
    have hfa0 : fa < store.frames.size := by simpa [Store.define] using hfa
    by_cases he : fa = target
    · subst fa
      simpa only [Store.define, Array.getElem_modify, if_pos] using
        (h.store.frames target ht).defineHit hhit hmatch huniq hvals hnew
          hag htarget hshared
    · have hf := (h.store.frames fa hfa0).transport hag (hframes fa hfa0 he) hshared
      simpa [Store.define, Array.getElem_modify, he, Ne.symm he] using hf
  · intro ca hc
    exact h.store.closures ca hc
  · intro ca hc
    simpa [Store.define] using h.store.capturedEnvs ca hc
  · intro ca hc q hq k hk
    have hf := hclosures ca hc
    have heq : read64 m (phiC ca) = read64 m' (phiC ca) := by
      simpa only [Nat.add_zero] using
        (extent_covers hf.header (by decide : 0 + 8 ≤ 16)).read64_eq hag
    have hq0 := heq.trans hq
    exact h.store.closureAsts ca hc q hq0 k
      (hk.pullback hag (fun j hj => hshared j (h.store.closureAsts ca hc q hq0 j hj)))

#print axioms FrameOwned.defineHit
#print axioms HeapOwned.defineHit

end Vsa.Sim.RuntimeOwnership
