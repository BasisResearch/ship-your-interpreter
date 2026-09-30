import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.RuntimeOwnershipInitial

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

theorem ArrayOwned.congr {alloc alloc' : Allocations} {role : Role} {p width cap : Nat}
    (h : ArrayOwned alloc role p width cap) (he : alloc' role = alloc role) :
    ArrayOwned alloc' role p width cap := by
  rcases h with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h2, by show alloc' role = _; rw [he]; exact h3⟩

end Vsa.Sim.RuntimeOwnership
