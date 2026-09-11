import Vsa.Sim.SharedGeometry

open Vsa.Alloc

namespace Vsa.Sim

/-- Shared reads may lie on either side of code and HTIF, including ELF rodata. -/
structure SharedReadGeom (shared : Nat → Prop) (SL : StackLayout) : Prop where
  ram : ∀ k, shared k → 0x80000000 ≤ k ∧ k + 8 ≤ 0x100000000
  code : ∀ k, shared k → k + 8 ≤ 0x80006ea0 ∨ 0x80006fcc ≤ k
  htif : ∀ k, shared k → k + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ k
  stack : ∀ k, shared k → k < SL.lo ∨ SL.hi ≤ k

/-- The previous above-image geometry remains a sufficient special case. -/
theorem SharedGeom.toReadGeom {shared : Nat → Prop} {SL : StackLayout}
    (h : SharedGeom shared SL) : SharedReadGeom shared SL where
  ram := fun k hk => by have := h.ram k hk; omega
  code := fun k hk => by have := h.ram k hk; omega
  htif := fun k hk => by have := h.htif k hk; omega
  stack := h.stack

/-- A contiguous shared string cannot cross an excluded interval. -/
theorem shared_string_window {shared : Nat → Prop} {p len lo hi : Nat}
    (hgap : lo < hi)
    (hexclude : ∀ k, shared k → k + 8 ≤ lo ∨ hi ≤ k)
    (hbytes : ∀ i, i ≤ len → shared (p + i)) :
    p + len + 8 ≤ lo ∨ hi ≤ p := by
  have hs := hexclude _ (hbytes 0 (Nat.zero_le _))
  have he := hexclude _ (hbytes len (Nat.le_refl _))
  rcases hs with hs | hs
  · rcases he with he | he
    · exact Or.inl he
    · have hc := hexclude _ (hbytes (lo - p) (by omega))
      omega
  · exact Or.inr (by simpa using hs)

#print axioms SharedGeom.toReadGeom
#print axioms shared_string_window

end Vsa.Sim
