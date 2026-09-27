import Vsa.Alloc
import Vsa.Sim.AstTransport

/-! Data-only live extent geometry and representation footprints.
These definitions do not depend on interpreter entries or allocator operations. -/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

abbrev Extent := Nat × Nat

/-- Live extents are nonempty, inside the arena, and pairwise disjoint. -/
def HeapArena (A : Arena) (exts : List Extent) : Prop :=
  (∀ e ∈ exts, 0 < e.2 ∧ A.contains e.1 e.2) ∧
  exts.Pairwise ExtDisjoint

end Vsa.Sim
