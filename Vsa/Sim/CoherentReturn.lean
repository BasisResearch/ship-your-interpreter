import Vsa.Sim.rows.StoreReprPhicRebase
import Vsa.Sim.ReprSurvival

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Machine

namespace Vsa.Sim

/-- Results, store survival, and ownership use the same selected maps and memory.
`Owned` is supplied by the reached producer. `True` explicitly forgets ownership.
The result list supports unary and binary callers without changing the contract. -/
structure ReturnRepr (N : NativeAddrs) (A : Arena)
    (entryF entryC resultF resultC : Addr → Nat) (nf nc : Nat)
    (store : Store) (results : List (Nat × Value))
    (Owned : (Addr → Nat) → (Addr → Nat) → Mem → Prop)
    (writes : Nat → Prop) (m : Mem) : Prop where
  frames : PhiExtends entryF resultF nf
  closures : PhiExtends entryC resultC nc
  values : ∀ a v, (a, v) ∈ results → ValueRepr m N resultC a v
  owned : Owned resultF resultC m
  survives : ∀ m', AgreeP (fun k => ¬ writes k) m m' →
    StoreRepr m' N A resultF resultC store

namespace ReturnRepr

variable {N : NativeAddrs} {A : Arena}
    {entryF entryC resultF resultC : Addr → Nat} {nf nc : Nat}
    {store : Store} {results : List (Nat × Value)}
    {Owned : (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    {writes : Nat → Prop} {m : Mem}

theorem storeRepr
    (h : ReturnRepr N A entryF entryC resultF resultC nf nc store results Owned writes m) :
    StoreRepr m N A resultF resultC store :=
  h.survives m (fun _ _ => rfl)

/-- Attach ownership established for this selected map pair at this return. -/
theorem withOwnership {Owned' : (Addr → Nat) → (Addr → Nat) → Mem → Prop}
    (h : ReturnRepr N A entryF entryC resultF resultC nf nc store results Owned writes m)
    (ho : Owned' resultF resultC m) :
    ReturnRepr N A entryF entryC resultF resultC nf nc store results Owned' writes m :=
  { h with owned := ho }

/-- Rebase an existing result onto the selected store map using an exact prefix. -/
theorem value_of_bounded {valueMap : Addr → Nat} {a : Nat} {v : Value}
    (h : ReturnRepr N A entryF entryC resultF resultC nf nc store results Owned writes m)
    (he : PhiExtends entryC valueMap nc) (hb : ValueClosuresBounded nc v)
    (hv : ValueRepr m N valueMap a v) : ValueRepr m N resultC a v :=
  valueRepr_phic_mono hb (fun k hk => (h.closures k hk).trans (he k hk).symm) hv

end ReturnRepr

#print axioms ReturnRepr.storeRepr
#print axioms ReturnRepr.withOwnership
#print axioms ReturnRepr.value_of_bounded

end Vsa.Sim
