import Vsa.RuntimeRepr

namespace Vsa.Sim

open Vsa.RuntimeRepr

def physSize (n : Nat) : Nat := max 32 (16 * ((n + 8 + 15) / 16))

theorem physSize_mono {m n : Nat} (h : m ≤ n) : physSize m ≤ physSize n := by
  unfold physSize
  omega

theorem physSize_min (n : Nat) : 32 ≤ physSize n := Nat.le_max_left _ _

def physTotal (exts : List (Nat × Nat)) : Nat :=
  (exts.map (fun e => physSize e.2)).sum

def ResourceBudget (A : Arena) (maxReq : Nat) (exts : List (Nat × Nat))
    (k : Nat) : Prop :=
  physTotal exts + k * physSize maxReq ≤ A.hi - A.lo

end Vsa.Sim
