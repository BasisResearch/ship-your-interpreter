import Vsa.Sim.ValueEqualPresent
import Vsa.Sim.EnvGetReflected.EnvGetOwnedNames
import Vsa.Sim.StaticImageSupport

open LeanRV64DExecutable Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc Vsa.While

namespace Vsa.Sim
open RuntimeOwnership

/-- A shared string lies wholly outside the caller stack. -/
theorem RuntimeOwnership.SharedCString.outside_stack
    {m : Mem} {shared : Nat → Prop} {SL : StackLayout} {p : Nat} {s : String}
    (h : SharedCString m shared p s) (geometry : SharedReadGeom shared SL)
    (nonempty : SL.lo < SL.hi) :
    p + s.length < SL.lo ∨ SL.hi ≤ p := by
  have first := geometry.stack _ (h.bytes 0 (Nat.zero_le _))
  rcases first with low | high
  · by_cases last : p + s.length < SL.lo
    · exact Or.inl last
    · have crossed := geometry.stack _ (h.bytes (SL.lo - p) (by omega))
      omega
  · exact Or.inr (by simpa using high)

/-- Owned operands supply the equality helper's complete string witness. -/
theorem ValueEqualStringData.of_owned
    {m : Mem} {shared : Nat → Prop} {SL : StackLayout} {A : Arena}
    {bufa bufb sp : BitVec 64} {sa sb : String}
    (left : ValueOwned m shared bufa.toNat (.str sa))
    (right : ValueOwned m shared bufb.toNat (.str sb))
    (geometry : SharedReadGeom shared SL) (image : StaticImageSupport m SL A)
    (room : SL.lo + 16 ≤ sp.toNat) (high : sp.toNat ≤ SL.hi)
    (ramLow : 0x80000000 ≤ SL.lo) (ramHigh : SL.hi ≤ 0x100000000)
    (htif : tohostAddr + 16 ≤ SL.lo) (aligned : sp.toNat % 8 = 0) :
    ValueEqualStringData bufa bufb sp sa sb m := by
  obtain ⟨pa, leftPointer, leftOwned⟩ := left
  obtain ⟨pb, rightPointer, rightOwned⟩ := right
  obtain ⟨csa, leftString, leftValue⟩ := leftOwned.repr
  obtain ⟨csb, rightString, rightValue⟩ := rightOwned.repr
  have leftOutside := leftOwned.outside_stack geometry (by omega)
  have rightOutside := rightOwned.outside_stack geometry (by omega)
  have leftLength : sa.length = csa.length := by rw [leftValue, String.length_ofList]
  have rightLength : sb.length = csb.length := by rw [rightValue, String.length_ofList]
  have code := image.stack_disjoint (lo := 0x80006ea0) (hi := 0x80006fcc)
    (by decide) (by decide)
  have mask := image.stack_disjoint (lo := maskAddr) (hi := maskAddr + 8)
    (by decide) (by decide)
  have equalCode := image.stack_disjoint (lo := 0x8000285c) (hi := 0x800028fc)
    (by decide) (by decide)
  refine ⟨pa, pb, csa, csb,
    { leftPointer := leftPointer, rightPointer := rightPointer
      leftString := leftString, rightString := rightString
      leftValue := leftValue, rightValue := rightValue
      leftRegion := leftOwned.strcmpSlack geometry csa leftString
      rightRegion := rightOwned.strcmpSlack geometry csb rightString
      stack := ?_ }⟩
  exact
    { sp16 := by omega
      win_lo := by omega
      win_hi := by omega
      win_htif := by omega
      win_align := by omega
      str_a := by omega
      str_b := by omega
      code := by omega
      mask := by omega
      vecode := by omega }

#print axioms RuntimeOwnership.SharedCString.outside_stack
#print axioms ValueEqualStringData.of_owned

end Vsa.Sim
