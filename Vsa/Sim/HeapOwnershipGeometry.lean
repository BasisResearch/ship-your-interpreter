import Vsa.Alloc
import Vsa.Sim.AstTransport

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

abbrev Extent := Nat × Nat

def HeapArena (A : Arena) (exts : List Extent) : Prop :=
  (∀ e ∈ exts, 0 < e.2 ∧ A.contains e.1 e.2) ∧
  exts.Pairwise ExtDisjoint

end Vsa.Sim
