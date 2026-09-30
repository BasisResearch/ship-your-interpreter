import Vsa.Alloc

open Vsa Vsa.Alloc Vsa.MemRepr

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

abbrev ramLo : Nat := 0x80000000

abbrev ramHi : Nat := 0x100000000

theorem tohostAddr_val : tohostAddr = 0x8001ad00 := rfl

abbrev Region : Type := Nat × Nat

def mem_region (a : Nat) (r : Region) : Prop := r.1 ≤ a ∧ a < r.1 + r.2

def RDisjoint (r s : Region) : Prop := r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1

def RSub (r s : Region) : Prop := s.1 ≤ r.1 ∧ r.1 + r.2 ≤ s.1 + s.2

theorem RSub.trans {r s t : Region} (h1 : RSub r s) (h2 : RSub s t) : RSub r t :=
  ⟨Nat.le_trans h2.1 h1.1, Nat.le_trans h1.2 h2.2⟩

def ramRegion : Region := (ramLo, ramHi - ramLo)

abbrev writeMap4_rg (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    Std.ExtHashMap Nat (BitVec 8) :=
  ((((mem.insert a (d.extractLsb' 0 8)).insert (a + 1) (d.extractLsb' 8 8)).insert
    (a + 2) (d.extractLsb' 16 8)).insert (a + 3) (d.extractLsb' 24 8))

def AgreeOn (r : Region) (m1 m2 : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ a, mem_region a r → m1[a]? = m2[a]?

theorem AgreeOn.trans {r : Region} {m1 m2 m3 : Std.ExtHashMap Nat (BitVec 8)}
    (h1 : AgreeOn r m1 m2) (h2 : AgreeOn r m2 m3) : AgreeOn r m1 m3 :=
  fun a ha => (h1 a ha).trans (h2 a ha)

theorem AgreeOn.mono {r r' : Region} {m1 m2 : Std.ExtHashMap Nat (BitVec 8)}
    (hsub : RSub r' r) (h : AgreeOn r m1 m2) : AgreeOn r' m1 m2 := by
  intro a ha; obtain ⟨hlo, hhi⟩ := ha; obtain ⟨slo, shi⟩ := hsub
  exact h a ⟨by omega, by omega⟩

structure FixedMap (block code stack : Region) : Prop where

  in_ram : RSub block ramRegion

  above_tohost : tohostAddr + 16 ≤ block.1

  aligned : block.1 % 8 = 0

  code_disjoint : RDisjoint block code

  stack_disjoint : RDisjoint block stack

theorem FixedMap.lo {block code stack : Region} (h : FixedMap block code stack) :
    ramLo ≤ block.1 := by
  have := h.in_ram; simp only [RSub, ramRegion] at this
  have hr : ramLo ≤ ramHi := by decide
  omega

theorem FixedMap.hi {block code stack : Region} (h : FixedMap block code stack) :
    block.1 + block.2 ≤ ramHi := by
  have := h.in_ram; simp only [RSub, ramRegion] at this
  have hr : ramLo ≤ ramHi := by decide
  omega

end Vsa.Sim
