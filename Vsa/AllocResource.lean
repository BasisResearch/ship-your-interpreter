import Vsa.RuntimeRepr

namespace Vsa.Sim

open Vsa.RuntimeRepr

/-- Minimum chunk size for a request: eight overhead bytes, sixteen-byte
alignment, and dlmalloc's thirty-two-byte minimum. An unsplit free chunk may
occupy more; this accounting does not establish concrete placement. -/
def physSize (n : Nat) : Nat := max 32 (16 * ((n + 8 + 15) / 16))

theorem physSize_mono {m n : Nat} (h : m ≤ n) : physSize m ≤ physSize n := by
  unfold physSize
  omega

/-- Every request reserves at least the allocator's minimum chunk. -/
theorem physSize_min (n : Nat) : 32 ≤ physSize n := Nat.le_max_left _ _

/-- Sum of the requested minimum chunk sizes in the live ledger. -/
def physTotal (exts : List (Nat × Nat)) : Nat :=
  (exts.map (fun e => physSize e.2)).sum

/-- Numeric credit for further requests at the ceiling. Concrete allocator
metadata and contiguous placement are separate entry obligations. -/
def ResourceBudget (A : Arena) (maxReq : Nat) (exts : List (Nat × Nat))
    (k : Nat) : Prop :=
  physTotal exts + k * physSize maxReq ≤ A.hi - A.lo

end Vsa.Sim
