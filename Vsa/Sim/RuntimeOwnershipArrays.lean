import Vsa.Sim.EnvDefSpec2
import Vsa.Sim.RuntimeOwnershipInitial

/-!
# `RuntimeOwnershipArrays` — one frame's backing arrays replaced

`env_define`'s grow path (and the empty frame's first allocation) replaces the
target frame's `names`/`vals` arrays through `realloc`: the new extents are
fresh, the old slots are copied, every other allocation and every shared byte
is untouched.  This file lands the ownership and representation algebra of
that replacement, once, over the array-owned ledger (`ArrayOwned` admits the
empty `NULL` arrays of a fresh frame):

* `Ledger.replaceArray` / `Immutable.replaceArray` / `Reserved.replaceArray`
  — the ledger after one array role is replaced (grow or first allocation);
* `StoreOwned.replaceArrays` / `HeapOwned.replaceArrays` — ownership at the
  memory holding the replaced arrays;
* `frameRepr_replaceArrays` / `storeRepr_replaceArrays` — the semantic store
  is unchanged, represented with the new arrays.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- An array role that is not the replaced one keeps its ownership. -/
theorem ArrayOwned.congr {alloc alloc' : Allocations} {role : Role} {p width cap : Nat}
    (h : ArrayOwned alloc role p width cap) (he : alloc' role = alloc role) :
    ArrayOwned alloc' role p width cap := by
  rcases h with h1 | ⟨h2, h3⟩
  · exact Or.inl h1
  · exact Or.inr ⟨h2, by show alloc' role = _; rw [he]; exact h3⟩

end Vsa.Sim.RuntimeOwnership
