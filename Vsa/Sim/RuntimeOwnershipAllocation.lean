import Vsa.Sim.RuntimeOwnership

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim.RuntimeOwnership

structure Reserved (A : Arena) (exts : List Extent) (shared : Nat → Prop) : Prop where
  live : ∀ k, shared k → A.lo ≤ k → k < A.hi →
    ∃ e ∈ exts, ExtentByte e k

def Allocations.insert (alloc : Allocations) (role : Role) (p n : Nat) : Allocations :=
  fun r => if r = role then some (p, n) else alloc r

theorem Allocations.insert_same {alloc : Allocations} {role : Role} {p n : Nat} :
    Allocated (alloc.insert role p n) role p n := by
  simp [Allocated, Allocations.insert]

theorem Allocations.insert_other {alloc : Allocations} {role r : Role} {p n : Nat}
    (hne : r ≠ role) : alloc.insert role p n r = alloc r := by
  simp only [Allocations.insert, if_neg hne]

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

structure HeapOwned (A : Arena) (exts : List Extent) (m : Mem)
    (phiF phiC : Addr → Nat) (alloc : Allocations)
    (shared readable writes : Nat → Prop) (s : Store) : Prop where
  ledger : Ledger A exts alloc
  immutable : Immutable alloc shared readable writes
  reserved : Reserved A exts shared
  store : StoreOwned m phiF phiC alloc shared s

end Vsa.Sim.RuntimeOwnership
