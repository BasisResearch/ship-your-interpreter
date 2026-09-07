import Vsa.Sim.rows.StoreReprPhicRebase

/-! Component obstructions to equality's entry-map and global-injectivity
requirements. These do not construct a loaded machine execution. -/

namespace Vsa.Sim

open Vsa.RuntimeRepr Vsa.While Vsa.MemRepr Vsa.Alloc

/-- Any represented store with bounded closure references also has a
representing map that aliases indices beyond its allocated prefix. -/
theorem storeRepr_noninjective_extension
    {m : Mem} {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    {s : Store} (hb : StoreClosuresBounded s)
    (hs : StoreRepr m N A phiF phiC s) :
    ∃ phiC', PhiExtends phiC phiC' s.closures.size ∧
      StoreRepr m N A phiF phiC' s ∧
      ¬ (∀ a b, phiC' a = phiC' b → a = b) := by
  let phiC' := fun k => if k < s.closures.size then phiC k else 0
  have he : PhiExtends phiC phiC' s.closures.size := by
    intro k hk
    simp [phiC', hk]
  refine ⟨phiC', he, storeRepr_phic_mono hb he hs, ?_⟩
  intro hinj
  have halias : phiC' s.closures.size = phiC' (s.closures.size + 1) := by
    have hnot : ¬ s.closures.size + 1 < s.closures.size := by omega
    simp [phiC', hnot]
  have heq := hinj s.closures.size (s.closures.size + 1) halias
  exact (Nat.ne_of_lt (Nat.lt_succ_self s.closures.size)) heq

/-- A represented closure outside the old prefix need not be represented at
an entry map that agrees with the return map on that prefix. -/
theorem valueRepr_fresh_map_obstruction
    {m : Mem} {N : NativeAddrs} {phiC : Addr → Nat} {box ca size : Nat}
    (hfresh : size ≤ ca) (hv : ValueRepr m N phiC box (.closure ca)) :
    ∃ before, PhiExtends before phiC size ∧
      ValueRepr m N phiC box (.closure ca) ∧
      ¬ ValueRepr m N before box (.closure ca) := by
  let before := fun k => if k = ca then 0 else phiC k
  have he : PhiExtends before phiC size := by
    intro k hk
    have hne : k ≠ ca := by omega
    simp [before, hne]
  refine ⟨before, he, hv, ?_⟩
  intro hbefore
  obtain ⟨_, _, hnz⟩ := hbefore
  exact hnz (by simp [before])

end Vsa.Sim
