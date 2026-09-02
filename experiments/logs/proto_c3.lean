import Vsa.Sim.TermAssembly
open Vsa Vsa.Sim Vsa.MemRepr
open Std (ExtHashMap)

-- Can we build a map = some 1 on [0,N) and prove the population premise WITHOUT
-- enumerating? Use List.range folded into inserts, prove membership generically.
def constMap (N : Nat) : ExtHashMap Nat (BitVec 8) :=
  (List.range N).foldl (fun m k => m.insert k (0x1 : BitVec 8)) ∅

-- Does the population premise hold provably & cheaply?
example : ∀ k, k < 5 → (constMap 5)[k]? = some (0x1 : BitVec 8) := by
  intro k hk
  interval_cases k <;> (simp [constMap, List.range] ; rfl)
