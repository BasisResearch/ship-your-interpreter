import Vsa.Sim.RuntimeOwnershipAllocation

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- The freshly copied binding string becomes immutable runtime data. -/
def BindingShared (shared : Nat → Prop) (p n : Nat) (k : Nat) : Prop :=
  shared k ∨ ExtentByte (p, n) k

/-- Assigning a fresh name allocation preserves old reservations and reserves its bytes. -/
theorem Reserved.binding
    {A : Arena} {exts : List Extent} {shared : Nat → Prop} {p n : Nat}
    (h : Reserved A exts shared) :
    Reserved A ((p, n) :: exts) (BindingShared shared p n) := by
  constructor
  intro k hk lo hi
  rcases hk with old | fresh
  · obtain ⟨e, he, covers⟩ := h.live k old lo hi
    exact ⟨e, List.mem_cons_of_mem _ he, covers⟩
  · exact ⟨(p, n), List.mem_cons_self, fresh⟩

/-- A fresh binding is immutable and disjoint from all mutable allocations. -/
theorem Immutable.binding
    {A : Arena} {exts : List Extent} {alloc : Allocations}
    {shared readable writes : Nat → Prop} {fa index p n : Nat}
    (h : Immutable alloc shared readable writes)
    (ledger : Ledger A exts alloc) (reserved : Reserved A exts shared)
    (arena : A.contains p n) (fresh : ∀ e ∈ exts, ExtDisjoint (p, n) e)
    (readableNew : ∀ k, ExtentByte (p, n) k → readable k)
    (outsideWrites : ∀ k, ExtentByte (p, n) k → ¬ writes k) :
    Immutable (alloc.insert (.binding fa index) p n) (BindingShared shared p n) readable writes := by
  have old := h.insert reserved arena fresh (role := .binding fa index)
  refine ⟨?_, ?_, ?_⟩
  · intro k hk; rcases hk with hk | hk
    · exact h.readable k hk
    · exact readableNew k hk
  · intro k hk; rcases hk with hk | hk
    · exact h.outsideWrites k hk
    · exact outsideWrites k hk
  · intro role q size mutable allocated k hk
    rcases hk with hk | hk
    · exact old.outsideMutable role q size mutable allocated k hk
    · have ne : role ≠ .binding fa index := by
        intro eq; subst role; exact mutable
      have original : Allocated alloc role q size := by
        simpa only [Allocated, Allocations.insert_other ne] using allocated
      have disjoint := fresh (q, size) (ledger.live role q size original)
      intro other
      change p + n ≤ q ∨ q + size ≤ p at disjoint
      change p ≤ k ∧ k < p + n at hk
      change q ≤ k ∧ k < q + size at other
      omega

#print axioms Reserved.binding
#print axioms Immutable.binding

end Vsa.Sim.RuntimeOwnership
