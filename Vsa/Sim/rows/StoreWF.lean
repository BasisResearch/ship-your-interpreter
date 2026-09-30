import Vsa.While.Cost
import Vsa.Sim.InterpEntry
import Vsa.Sim.StoreInvariant

open Vsa Vsa.While Vsa.Sim

namespace Vsa.Sim

theorem ValueClosuresBounded.mono {k k' : Nat} (hk : k ≤ k') :
    ∀ {v : Value}, ValueClosuresBounded k v → ValueClosuresBounded k' v
  | .null, h => h
  | .bool _, h => h
  | .int _, h => h
  | .str _, h => h
  | .native _, h => h
  | .closure _ca, h => Nat.lt_of_lt_of_le h hk

def StatusClosuresBounded (k : Nat) : Status → Prop
  | .ret v => ValueClosuresBounded k v
  | _ => True

def ValuesClosuresBounded (k : Nat) (vs : List Value) : Prop :=
  ∀ w ∈ vs, ValueClosuresBounded k w

theorem StatusClosuresBounded.mono {k k' : Nat} (hk : k ≤ k') :
    ∀ {status : Status}, StatusClosuresBounded k status → StatusClosuresBounded k' status
  | .normal, h => h
  | .brk, h => h
  | .cont, h => h
  | .ret _, h => ValueClosuresBounded.mono hk h

theorem ValuesClosuresBounded.mono {k k' : Nat} (hk : k ≤ k') {vs : List Value}
    (h : ValuesClosuresBounded k vs) : ValuesClosuresBounded k' vs :=
  fun w hw => (h w hw).mono hk

end Vsa.Sim
