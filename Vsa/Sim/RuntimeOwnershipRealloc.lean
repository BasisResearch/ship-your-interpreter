import Vsa.Sim.RuntimeOwnershipAllocation
import Vsa.Sim.ReallocSpec

/-! Reallocation geometry for one old mutable role. The replacement may overlap
its old extent. Freshness is required only against surviving live extents,
exactly as in ReallocGrowResult. No old-extent byte preservation is asserted. -/

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- Remove the role whose old extent is being freed. -/
def Allocations.erase (alloc : Allocations) (role : Role) : Allocations :=
  fun r => if r = role then none else alloc r

theorem Allocations.erase_other {alloc : Allocations} {role r : Role}
    (hne : r ≠ role) : alloc.erase role r = alloc r := by
  simp only [Allocations.erase, if_neg hne]

theorem Allocations.insert_erase {alloc : Allocations} {role : Role} {p n : Nat} :
    (alloc.erase role).insert role p n = alloc.insert role p n := by
  funext r
  by_cases hr : r = role <;> simp [Allocations.insert, Allocations.erase, hr]

private theorem heapArena_nodup {A : Arena} {exts : List Extent}
    (h : HeapArena A exts) : exts.Nodup := by
  apply List.Pairwise.imp_of_mem (p := h.2)
  intro a b ha _ hd he
  subst b
  have hp := (h.1 a ha).1
  change a.1 + a.2 ≤ a.1 ∨ a.1 + a.2 ≤ a.1 at hd
  omega

/-- The contract's old-excepted freshness is precisely freshness against erase.
Positive disjoint extents cannot contain duplicate occurrences of the old one. -/
theorem Ledger.freshAfterErase {A : Arena} {exts : List Extent} {alloc : Allocations}
    (h : Ledger A exts alloc) {pOld nOld pNew nNew : Nat}
    (hf : ∀ e ∈ exts, e ≠ (pOld, nOld) → ExtDisjoint (pNew, nNew) e) :
    ∀ e ∈ exts.erase (pOld, nOld), ExtDisjoint (pNew, nNew) e := by
  intro e he
  apply hf e (List.mem_of_mem_erase he)
  intro eq
  subst e
  exact (heapArena_nodup h.arena).not_mem_erase he

/-- Erasing a role's live extent retains every other allocation role. -/
theorem Ledger.erase {A : Arena} {exts : List Extent} {alloc : Allocations}
    (h : Ledger A exts alloc) {role : Role} {p n : Nat}
    (ha : Allocated alloc role p n) :
    Ledger A (exts.erase (p, n)) (alloc.erase role) := by
  have hpositive := (h.arena.1 _ (h.live _ _ _ ha)).1
  have old : ∀ r q size, Allocated (alloc.erase role) r q size →
      r ≠ role ∧ Allocated alloc r q size := by
    intro r q size hr
    by_cases he : r = role
    · subst r
      simp [Allocated, Allocations.erase] at hr
    · exact ⟨he, by simpa only [Allocated, Allocations.erase_other he] using hr⟩
  refine ⟨⟨?_, List.Pairwise.erase (p, n) h.arena.2⟩, ?_, ?_⟩
  · intro e he
    exact h.arena.1 e (List.mem_of_mem_erase he)
  · intro r q size hr
    obtain ⟨hne, hold⟩ := old r q size hr
    have hdiff : (q, size) ≠ (p, n) := by
      intro he
      have hd := h.separated r role q size p n hold ha hne
      rw [he] at hd
      change p + n ≤ p ∨ p + n ≤ p at hd
      omega
    exact (List.mem_erase_of_ne hdiff).mpr (h.live r q size hold)
  · intro r s q size b width hr hs hne
    exact h.separated r s q size b width (old r q size hr).2 (old s b width hs).2 hne

/-- Geometry after successful realloc. Only surviving extents must be fresh. -/
theorem Ledger.replace {A : Arena} {exts : List Extent} {alloc : Allocations}
    (h : Ledger A exts alloc) {role : Role} {pOld nOld pNew nNew : Nat}
    (hold : Allocated alloc role pOld nOld) (hpos : 0 < nNew)
    (ha : A.contains pNew nNew)
    (hf : ∀ e ∈ exts, e ≠ (pOld, nOld) → ExtDisjoint (pNew, nNew) e) :
    Ledger A ((pNew, nNew) :: exts.erase (pOld, nOld)) (alloc.insert role pNew nNew) := by
  simpa only [Allocations.insert_erase] using
    (h.erase hold).insert (role := role) hpos ha (h.freshAfterErase hf)

/-- Immutable bytes were outside the old mutable allocation, so their live
cover cannot be the erased extent. -/
theorem Reserved.erase {A : Arena} {exts : List Extent} {alloc : Allocations}
    {shared readable writes : Nat → Prop}
    (h : Reserved A exts shared) (hi : Immutable alloc shared readable writes)
    {role : Role} {p n : Nat} (hm : Role.mutable role) (ha : Allocated alloc role p n) :
    Reserved A (exts.erase (p, n)) shared := by
  constructor
  intro k hk hlo hhi
  obtain ⟨e, he, heb⟩ := h.live k hk hlo hhi
  have hne : e ≠ (p, n) := by
    intro eq
    subst e
    exact hi.outsideMutable role p n hm ha k hk heb
  exact ⟨e, (List.mem_erase_of_ne hne).mpr he, heb⟩

/-- Replacement retains reserved bytes through the surviving ledger. -/
theorem Reserved.replace {A : Arena} {exts : List Extent} {alloc : Allocations}
    {shared readable writes : Nat → Prop}
    (h : Reserved A exts shared) (hi : Immutable alloc shared readable writes)
    {role : Role} {pOld nOld pNew nNew : Nat}
    (hm : Role.mutable role) (ha : Allocated alloc role pOld nOld) :
    Reserved A ((pNew, nNew) :: exts.erase (pOld, nOld)) shared :=
  (h.erase hi hm ha).mono (fun _ he => List.mem_cons.mpr (Or.inr he))

/-- Removing a mutable role adds no new possible write locations. -/
theorem Immutable.erase {alloc : Allocations} {shared readable writes : Nat → Prop}
    (h : Immutable alloc shared readable writes) (role : Role) :
    Immutable (alloc.erase role) shared readable writes := by
  refine ⟨h.readable, h.outsideWrites, ?_⟩
  intro r q size hm hr k hk
  by_cases he : r = role
  · subst r
    simp [Allocated, Allocations.erase] at hr
  · have hold : Allocated alloc r q size := by
      simpa only [Allocated, Allocations.erase_other he] using hr
    exact h.outsideMutable r q size hm hold k hk

/-- The new allocation avoids shared bytes even if it reuses the old region. -/
theorem Immutable.replace {A : Arena} {exts : List Extent} {alloc : Allocations}
    {shared readable writes : Nat → Prop}
    (h : Immutable alloc shared readable writes) (hl : Ledger A exts alloc)
    (hr : Reserved A exts shared) {role : Role} {pOld nOld pNew nNew : Nat}
    (hm : Role.mutable role) (hold : Allocated alloc role pOld nOld)
    (ha : A.contains pNew nNew)
    (hf : ∀ e ∈ exts, e ≠ (pOld, nOld) → ExtDisjoint (pNew, nNew) e) :
    Immutable (alloc.insert role pNew nNew) shared readable writes := by
  simpa only [Allocations.insert_erase] using
    (h.erase role).insert (role := role) (hr.erase h hm hold) ha (hl.freshAfterErase hf)

/-- The successful realloc public frame preserves shared bytes. Both excluded
extents are discharged by geometry. No bytes inside the freed extent are
assumed preserved. Exact stack/private exclusions remain explicit caller facts. -/
theorem shared_agree_realloc
    {A : Arena} {exts : List Extent} {alloc : Allocations}
    {shared readable writes privFoot : Nat → Prop} {SL : StackLayout} {sp : BitVec 64}
    {m0 m : Mem} (hi : Immutable alloc shared readable writes)
    (hl : Ledger A exts alloc) (hr : Reserved A exts shared)
    {role : Role} {pOld nOld pNew nNew : Nat}
    (hm : Role.mutable role) (hold : Allocated alloc role pOld nOld)
    (ha : A.contains pNew nNew)
    (hf : ∀ e ∈ exts, e ≠ (pOld, nOld) → ExtDisjoint (pNew, nNew) e)
    (hpriv : ∀ k, shared k → ¬ privFoot k)
    (hstack : ∀ k, SL.lo ≤ k ∧ k < sp.toNat → writes k)
    (hmem : HeapPublicFrame privFoot SL sp [(pOld, nOld), (pNew, nNew)] m0 m) :
    AgreeP shared m0 m := by
  intro k hk
  have oldOut := hi.outsideMutable role pOld nOld hm hold k hk
  have newOut := (hr.erase hi hm hold).outsideFresh ha (hl.freshAfterErase hf) k hk
  apply Eq.symm
  apply hmem k
  · exact hpriv k hk
  · exact fun hs => hi.outsideWrites k hk (hstack k hs)
  · intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      change ¬ (pOld ≤ k ∧ k < pOld + nOld) at oldOut
      omega
    · rcases List.mem_cons.mp he with he | he
      · subst e
        change ¬ (pNew ≤ k ∧ k < pNew + nNew) at newOut
        omega
      · simp only [List.not_mem_nil] at he

/-- Derive realloc shared-byte preservation from live allocator footprint facts. -/
theorem shared_agree_realloc_of_private
    {A : Arena} {exts : List Extent} {alloc : Allocations}
    {shared readable writes privFoot : Nat → Prop} {SL : StackLayout} {sp : BitVec 64}
    {m0 m : Mem} (hi : Immutable alloc shared readable writes)
    (hl : Ledger A exts alloc) (hr : Reserved A exts shared)
    {role : Role} {pOld nOld pNew nNew : Nat}
    (hm : Role.mutable role) (hold : Allocated alloc role pOld nOld)
    (ha : A.contains pNew nNew)
    (hf : ∀ e ∈ exts, e ≠ (pOld, nOld) → ExtDisjoint (pNew, nNew) e)
    (hprivLive : ∀ e ∈ exts, ∀ i < e.2, ¬ privFoot (e.1 + i))
    (hprivOutside : ∀ k, privFoot k → ¬ (A.lo ≤ k ∧ k < A.hi) → writes k)
    (hstack : ∀ k, SL.lo ≤ k ∧ k < sp.toNat → writes k)
    (hmem : HeapPublicFrame privFoot SL sp [(pOld, nOld), (pNew, nNew)] m0 m) :
    AgreeP shared m0 m :=
  shared_agree_realloc hi hl hr hm hold ha hf
    (hr.outsidePrivate hi hprivLive hprivOutside) hstack hmem

#print axioms Allocations.erase_other
#print axioms Allocations.insert_erase
#print axioms Ledger.erase
#print axioms Ledger.freshAfterErase
#print axioms Ledger.replace
#print axioms Reserved.erase
#print axioms Reserved.replace
#print axioms Immutable.erase
#print axioms Immutable.replace
#print axioms shared_agree_realloc
#print axioms shared_agree_realloc_of_private

end Vsa.Sim.RuntimeOwnership
