import Vsa.Sim.RuntimeOwnership

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

/-- Shared bytes inside the arena occupy live extents, so a fresh allocation
cannot reclaim them. Shared static bytes outside the arena need no extent. -/
structure Reserved (A : Arena) (exts : List Extent) (shared : Nat → Prop) : Prop where
  live : ∀ k, shared k → A.lo ≤ k → k < A.hi →
    ∃ e ∈ exts, ExtentByte e k

/-- A fresh allocated extent cannot overlap a reserved immutable byte. -/
theorem Reserved.outsideFresh {A : Arena} {exts : List Extent} {shared : Nat → Prop}
    (h : Reserved A exts shared) {p n : Nat} (ha : A.contains p n)
    (hf : ∀ e ∈ exts, ExtDisjoint (p, n) e) :
    ∀ k, shared k → ¬ ExtentByte (p, n) k := by
  intro k hk hin
  obtain ⟨hlo, hhi⟩ := ha
  obtain ⟨hkl, hkh⟩ := hin
  obtain ⟨e, he, hek⟩ := h.live k hk (by omega) (by omega)
  have hd := hf e he
  obtain ⟨hel, heh⟩ := hek
  change p + n ≤ e.1 ∨ e.1 + e.2 ≤ p at hd
  omega

/-- Extending a ledger retains every previously reserved immutable byte. -/
theorem Reserved.mono {A : Arena} {exts exts' : List Extent} {shared : Nat → Prop}
    (h : Reserved A exts shared) (he : ∀ e ∈ exts, e ∈ exts') :
    Reserved A exts' shared := by
  constructor
  intro k hk hlo hhi
  obtain ⟨e, hem, heb⟩ := h.live k hk hlo hhi
  exact ⟨e, he e hem, heb⟩

/-- Live reservations protect in-arena shared bytes from private metadata.
Outside the arena, private writes must belong to the caller's write footprint. -/
theorem Reserved.outsidePrivate
    {A : Arena} {exts : List Extent} {alloc : Allocations}
    {shared readable writes privFoot : Nat → Prop}
    (h : Reserved A exts shared) (hi : Immutable alloc shared readable writes)
    (hlive : ∀ e ∈ exts, ∀ i < e.2, ¬ privFoot (e.1 + i))
    (hout : ∀ k, privFoot k → ¬ (A.lo ≤ k ∧ k < A.hi) → writes k) :
    ∀ k, shared k → ¬ privFoot k := by
  intro k hk hp
  by_cases ha : A.lo ≤ k ∧ k < A.hi
  · obtain ⟨e, he, hbyte⟩ := h.live k hk ha.1 ha.2
    obtain ⟨hlo, hhi⟩ := hbyte
    have hbound : k - e.1 < e.2 := by omega
    have heq : e.1 + (k - e.1) = k := by omega
    have hn := hlive e he (k - e.1) hbound
    rw [heq] at hn
    exact hn hp
  · exact hi.outsideWrites k hk (hout k hp ha)

/-- Assign a newly allocated extent to one runtime role. -/
def Allocations.insert (alloc : Allocations) (role : Role) (p n : Nat) : Allocations :=
  fun r => if r = role then some (p, n) else alloc r

theorem Allocations.insert_same {alloc : Allocations} {role : Role} {p n : Nat} :
    Allocated (alloc.insert role p n) role p n := by
  simp [Allocated, Allocations.insert]

theorem Allocations.insert_other {alloc : Allocations} {role r : Role} {p n : Nat}
    (hne : r ≠ role) : alloc.insert role p n r = alloc r := by
  simp only [Allocations.insert, if_neg hne]

/-- Fresh extent geometry extends the role ledger. Allocation success and
metadata preservation must come from the actual allocator operation. -/
theorem Ledger.insert {A : Arena} {exts : List Extent} {alloc : Allocations}
    (h : Ledger A exts alloc) {role : Role} {p n : Nat}
    (hpos : 0 < n) (ha : A.contains p n)
    (hf : ∀ e ∈ exts, ExtDisjoint (p, n) e) :
    Ledger A ((p, n) :: exts) (alloc.insert role p n) := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e
        exact ⟨hpos, ha⟩
      · exact h.arena.1 e he
    · exact List.pairwise_cons.mpr ⟨hf, h.arena.2⟩
  · intro r q size hr
    by_cases heq : r = role
    · subst r
      have he : (p, n) = (q, size) := by
        exact Option.some.inj ((show alloc.insert role p n role = some (p, n)
          from Allocations.insert_same).symm.trans hr)
      exact List.mem_cons.mpr (Or.inl he.symm)
    · have old : Allocated alloc r q size := by
        simpa only [Allocated, Allocations.insert_other heq] using hr
      exact List.mem_cons.mpr (Or.inr (h.live r q size old))
  · intro r s q size b width hr hs hne
    by_cases er : r = role
    · subst r
      have e : (p, n) = (q, size) := Option.some.inj
        ((show alloc.insert role p n role = some (p, n)
          from Allocations.insert_same).symm.trans hr)
      have old : Allocated alloc s b width := by
        simpa only [Allocated, Allocations.insert_other (Ne.symm hne)] using hs
      simpa only [e] using hf (b, width) (h.live s b width old)
    · have oldr : Allocated alloc r q size := by
        simpa only [Allocated, Allocations.insert_other er] using hr
      by_cases es : s = role
      · subst s
        have e : (p, n) = (b, width) := Option.some.inj
          ((show alloc.insert role p n role = some (p, n)
            from Allocations.insert_same).symm.trans hs)
        have hd := hf (q, size) (h.live r q size oldr)
        rw [e] at hd
        exact hd.symm
      · have olds : Allocated alloc s b width := by
          simpa only [Allocated, Allocations.insert_other es] using hs
        exact h.separated r s q size b width oldr olds hne

/-- Reserved immutable bytes survive adding a fresh allocation role. -/
theorem Immutable.insert {A : Arena} {exts : List Extent} {alloc : Allocations}
    {shared readable writes : Nat → Prop}
    (h : Immutable alloc shared readable writes) (hr : Reserved A exts shared)
    {role : Role} {p n : Nat} (ha : A.contains p n)
    (hf : ∀ e ∈ exts, ExtDisjoint (p, n) e) :
    Immutable (alloc.insert role p n) shared readable writes := by
  refine ⟨h.readable, h.outsideWrites, ?_⟩
  intro r q size hm halloc k hk
  by_cases heq : r = role
  · subst r
    have e : (p, n) = (q, size) := Option.some.inj
      ((show alloc.insert role p n role = some (p, n)
        from Allocations.insert_same).symm.trans halloc)
    simpa only [e] using hr.outsideFresh ha hf k hk
  · have old : Allocated alloc r q size := by
      simpa only [Allocated, Allocations.insert_other heq] using halloc
    exact h.outsideMutable r q size hm old k hk

/-- Runtime memory ownership over the allocator's current live extent ledger.
It contains data and byte geometry only; allocator execution is proved separately. -/
structure HeapOwned (A : Arena) (exts : List Extent) (m : Mem)
    (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) : Prop where
  ledger : Ledger A exts alloc
  immutable : Immutable alloc shared readable writes
  reserved : Reserved A exts shared
  store : StoreOwned m phiF phiC alloc shared s

#print axioms Allocations.insert_same
#print axioms Allocations.insert_other
#print axioms Ledger.insert
#print axioms Immutable.insert
#print axioms Reserved.outsideFresh
#print axioms Reserved.mono
#print axioms Reserved.outsidePrivate

end Vsa.Sim.RuntimeOwnership
