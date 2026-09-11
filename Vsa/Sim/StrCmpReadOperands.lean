import Vsa.Sim.StrCmpCellClauses
import Vsa.Sim.EnvGetReflected.EnvGetOwnedNames

open LeanRV64DExecutable Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim
open RuntimeOwnership

/-- Shared read geometry separates each string from the comparison spill. -/
theorem strCmpRegion_of_readShared {shared : Nat → Prop} {SL : StackLayout}
    (hG : SharedReadGeom shared SL) {sp' p : BitVec 64} {len : Nat}
    (hsplo : SL.lo ≤ sp'.toNat) (hsphi : sp'.toNat + 8 ≤ SL.hi)
    (hbytes : ∀ k, k ≤ len → shared (p.toNat + k)) : StrCmpRegion sp' p len := by
  refine ⟨strcmpWSlack_of_shared hG hbytes, ?_⟩
  rcases hG.stack _ (hbytes 0 (Nat.zero_le _)) with hlo | hhi
  · by_cases hend : p.toNat + len < SL.lo
    · exact Or.inl (by omega)
    · exfalso
      have hk := hG.stack _ (hbytes (SL.lo - p.toNat) (by omega))
      omega
  · exact Or.inr (by omega)

/-- An owned string read supplies its region at the actual pointer. -/
theorem RuntimeOwnership.SharedCString.comparisonRegion
    {shared : Nat → Prop} {SL : StackLayout} {m : Mem} {a : Nat} {s : String}
    {sp' p : BitVec 64} (h : SharedCString m shared a s)
    (hG : SharedReadGeom shared SL) (hp : p.toNat = a)
    (hsplo : SL.lo ≤ sp'.toNat) (hsphi : sp'.toNat + 8 ≤ SL.hi) :
    ∀ cs, CStr m p.toNat cs → StrCmpRegion sp' p cs.length := by
  intro cs hcs
  obtain ⟨cs0, hcs0, hs⟩ := h.repr
  rw [hp] at hcs
  have heq := cstr_unique_eg9 m a cs cs0 hcs hcs0
  subst cs
  apply strCmpRegion_of_readShared hG hsplo hsphi
  intro k hk
  rw [hp]
  exact h.bytes k (by rw [hs, String.length_ofList]; exact hk)

/-- Both owned operand slots supply comparison geometry after allocating children. -/
theorem strCmpOperandsAt_of_readOwned {shared : Nat → Prop} {SL : StackLayout}
    {sp : BitVec 64} {m : Mem} {sl sr : String}
    (hG : SharedReadGeom shared SL) (hsp : SL.lo + 1088 ≤ sp.toNat)
    (hspHi : sp.toNat ≤ SL.hi)
    (hl : ValueOwned m shared (sp.toNat - 968) (.str sl))
    (hr : ValueOwned m shared (sp.toNat - 944) (.str sr)) :
    StrCmpOperandsAt sp m := by
  have hsub := sp_sub1088_toNat sp (by omega)
  obtain ⟨pl, hpl, hsl⟩ := hl
  obtain ⟨pr, hpr, hsr⟩ := hr
  have left : (strLeftPtr m sp).toNat = pl := by
    unfold strLeftPtr
    exact bytesT8_toNat_of_read64
      (by rw [show sp.toNat - 960 = sp.toNat - 968 + 8 by omega]; exact hpl)
  have right : (strRightPtr m sp).toNat = pr := by
    unfold strRightPtr
    exact bytesT8_toNat_of_read64
      (by rw [show sp.toNat - 936 = sp.toNat - 944 + 8 by omega]; exact hpr)
  exact ⟨hsl.comparisonRegion hG left (by rw [hsub]; omega) (by rw [hsub]; omega),
    hsr.comparisonRegion hG right (by rw [hsub]; omega) (by rw [hsub]; omega)⟩

#print axioms strCmpRegion_of_readShared
#print axioms RuntimeOwnership.SharedCString.comparisonRegion
#print axioms strCmpOperandsAt_of_readOwned

end Vsa.Sim
