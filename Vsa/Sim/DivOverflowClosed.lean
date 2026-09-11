import Vsa.Sim.IntegerCellSuppliers

open LeanRV64DExecutable Vsa
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc Vsa.Sim.Code

namespace Vsa.Sim

/-- Division-tail geometry is independent of the quotient's signed overflow. -/
theorem ScaffoldRows.field_hIDiv_wrap : BinIntCell .div DivResid (fun _ _ => True) :=
  binIntCell_of_postGeom (slotDef := DivSlotPinned) (valLoaded := Value_intLoaded)
    (viLo := 0x8000280c) (viHi := 0x8000281c) (tblOff := 20)
    (fun _ => FixedRodataLoaded.divSlot) (fun _ => FixedTextLoaded.Value_intLoaded)
    (by decide) (by decide) (by decide) (fun image h => divResid_of_armPostGeomV h
      image.text.__divdi3Loaded image.text.__umoddi3Loaded image.text.__hidden___udivdi3Loaded
      (image.stackPrefixDisjoint h.spSLhi (by decide) (by decide)))

/-- The exact division-overflow residual, including both recursive children and the outer return. -/
theorem ScaffoldRows.field_hDivOv : BinDivOverflowCell := by
  intro st d env el er middle final a b left right leftIH rightIH ha hb
  subst a b
  intro g N A SL phiF phiC sp ret dst interp node m0 before entry
  exact binRow_div_wrap g N A SL phiF phiC st middle final d env el er (-2^63) (-1)
    sp ret dst interp node m0 (by decide) left leftIH rightIH
    (EvalE.binary st d env .div el er middle final (.int (-2^63)) (.int (-1)) _
      left right (by simp [binOpSem]))
    (ScaffoldRows.field_hIDiv_wrap g N A SL phiF phiC st middle final d env el er
      (-2^63) (-1) left right leftIH rightIH trivial sp ret dst interp node m0 before entry)
    before entry

#print axioms ScaffoldRows.field_hIDiv_wrap
#print axioms ScaffoldRows.field_hDivOv

end Vsa.Sim
