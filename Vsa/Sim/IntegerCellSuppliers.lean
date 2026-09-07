import Vsa.Sim.BinaryPostGeom
import Vsa.Sim.FixedOperatorTable
import Vsa.Sim.rows.BinIntReadback
import Vsa.Sim.Code.FixedImage_Value_int
import Vsa.Sim.Code.FixedImage_Value_bool
import Vsa.Sim.Code.FixedImage___muldi3
import Vsa.Sim.Code.FixedImage___divdi3
import Vsa.Sim.Code.FixedImage___umoddi3
import Vsa.Sim.Code.FixedImage___hidden___udivdi3
import Vsa.Sim.Code.FixedImage___moddi3

open LeanRV64DExecutable Vsa Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-- Supply an integer cell from fixed-image projections and shared return geometry. -/
theorem binIntCell_of_postGeom
    {op : BinOp}
    {Resid : ((R : Register) → Option (RegisterType R)) → NativeAddrs → Arena →
      StackLayout → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64 →
      Vsa.Machine.Config → Prop}
    {slotDef valLoaded : Mem → Prop} {viLo viHi tblOff : Nat}
    {guard : Int → Int → Prop}
    (hslot : ∀ m, FixedRodataLoaded m → slotDef m)
    (hcode : ∀ m, FixedTextLoaded m → valLoaded m)
    (hvlo : 0x80000000 ≤ viLo) (hvhi : viHi ≤ 0x8001acf0)
    (htable : tblOff ≤ 52)
    (adapt : ∀ {gpre : (R : Register) → Option (RegisterType R)}
      {N : NativeAddrs} {A : Arena} {SL : StackLayout}
      {sp r sret aExpr : BitVec 64} {c' : Vsa.Machine.Config},
      StaticImageSupport c'.σ.mem SL A →
      ArmPostGeomV gpre N A SL (binOpTok op) slotDef valLoaded viLo viHi tblOff
        sp r sret aExpr c' → Resid gpre N A SL sp r sret aExpr c') :
    BinIntCell op Resid guard := by
  intro g N A SL phiF phiC st st' st'' d env el er a b _hl _hr _ihl _ihr _guard
    sp r sret aEnv aExpr m0 c he gpre v8 v9 v18 v19 hf c' hret
  exact adapt (he.binaryReturnImage hret)
    (he.binaryPostGeom hf hret hslot hcode hvlo hvhi htable)

/-- Restrict whole-stack code exclusion to the active stack prefix. -/
theorem StaticImageSupport.stackPrefixDisjoint
    {m : Mem} {SL : StackLayout} {A : Arena} (h : StaticImageSupport m SL A)
    {sp lo hi : Nat} (hsp : sp ≤ SL.hi)
    (hlo : 0x80000000 ≤ lo) (hhi : hi ≤ 0x8001acf0) :
    sp ≤ lo ∨ hi ≤ SL.lo :=
  (h.stack_disjoint hlo hhi).imp (Nat.le_trans hsp) id

theorem ScaffoldRows.field_hIAdd : BinIntCell .add AddResid (fun _ _ => True) :=
  binIntCell_of_postGeom (slotDef := AddSlotPinned) (valLoaded := Value_intLoaded)
    (viLo := 0x8000280c) (viHi := 0x8000281c) (tblOff := 4)
    (fun _ => FixedRodataLoaded.addSlot) (fun _ => FixedTextLoaded.Value_intLoaded)
    (by decide) (by decide) (by decide) (fun _ h => addResid_of_armPostGeomV h)

theorem ScaffoldRows.field_hISub : BinIntCell .sub SubResid (fun _ _ => True) :=
  binIntCell_of_postGeom (slotDef := SubSlotPinned) (valLoaded := Value_intLoaded)
    (viLo := 0x8000280c) (viHi := 0x8000281c) (tblOff := 4)
    (fun _ => FixedRodataLoaded.subSlot) (fun _ => FixedTextLoaded.Value_intLoaded)
    (by decide) (by decide) (by decide) (fun _ h => subResid_of_armPostGeomV h)

theorem ScaffoldRows.field_hILt : BinIntCell .lt LtResid (fun _ _ => True) :=
  binIntCell_of_postGeom (slotDef := LtSlotPinned) (valLoaded := Value_boolLoaded)
    (viLo := 0x800027f8) (viHi := 0x8000280c) (tblOff := 4)
    (fun _ => FixedRodataLoaded.ltSlot) (fun _ => FixedTextLoaded.Value_boolLoaded)
    (by decide) (by decide) (by decide) (fun _ h => ltResid_of_armPostGeomV h)

theorem ScaffoldRows.field_hILe : BinIntCell .le LeResid (fun _ _ => True) :=
  binIntCell_of_postGeom (slotDef := LeSlotPinned) (valLoaded := Value_boolLoaded)
    (viLo := 0x800027f8) (viHi := 0x8000280c) (tblOff := 4)
    (fun _ => FixedRodataLoaded.leSlot) (fun _ => FixedTextLoaded.Value_boolLoaded)
    (by decide) (by decide) (by decide) (fun _ h => leResid_of_armPostGeomV h)

theorem ScaffoldRows.field_hIGt : BinIntCell .gt GtResid (fun _ _ => True) :=
  binIntCell_of_postGeom (slotDef := GtSlotPinned) (valLoaded := Value_boolLoaded)
    (viLo := 0x800027f8) (viHi := 0x8000280c) (tblOff := 4)
    (fun _ => FixedRodataLoaded.gtSlot) (fun _ => FixedTextLoaded.Value_boolLoaded)
    (by decide) (by decide) (by decide) (fun _ h => gtResid_of_armPostGeomV h)

theorem ScaffoldRows.field_hIGe : BinIntCell .ge GeResid (fun _ _ => True) :=
  binIntCell_of_postGeom (slotDef := GeSlotPinned) (valLoaded := Value_boolLoaded)
    (viLo := 0x800027f8) (viHi := 0x8000280c) (tblOff := 4)
    (fun _ => FixedRodataLoaded.geSlot) (fun _ => FixedTextLoaded.Value_boolLoaded)
    (by decide) (by decide) (by decide) (fun _ h => geResid_of_armPostGeomV h)

theorem ScaffoldRows.field_hIMul : BinIntCell .mul MulResid (fun _ _ => True) :=
  binIntCell_of_postGeom (slotDef := MulSlotPinned) (valLoaded := Value_intLoaded)
    (viLo := 0x8000280c) (viHi := 0x8000281c) (tblOff := 12)
    (fun _ => FixedRodataLoaded.mulSlot) (fun _ => FixedTextLoaded.Value_intLoaded)
    (by decide) (by decide) (by decide) (fun image h => mulResid_of_armPostGeomV h
      image.text.__muldi3Loaded (image.stackPrefixDisjoint h.spSLhi (by decide) (by decide)))

theorem ScaffoldRows.field_hIDiv :
    BinIntCell .div DivResid (fun a b => ¬(a = -2^63 ∧ b = -1)) :=
  binIntCell_of_postGeom (slotDef := DivSlotPinned) (valLoaded := Value_intLoaded)
    (viLo := 0x8000280c) (viHi := 0x8000281c) (tblOff := 20)
    (fun _ => FixedRodataLoaded.divSlot) (fun _ => FixedTextLoaded.Value_intLoaded)
    (by decide) (by decide) (by decide) (fun image h => divResid_of_armPostGeomV h
      image.text.__divdi3Loaded image.text.__umoddi3Loaded image.text.__hidden___udivdi3Loaded
      (image.stackPrefixDisjoint h.spSLhi (by decide) (by decide)))

theorem ScaffoldRows.field_hIMod : BinIntCell .mod ModResid (fun _ _ => True) :=
  binIntCell_of_postGeom
    (slotDef := SlotPinned 0x80019f94#64 0x00#8 0x98#8 0xfe#8 0xff#8)
    (valLoaded := Value_intLoaded) (viLo := 0x8000280c) (viHi := 0x8000281c) (tblOff := 20)
    (fun _ => FixedRodataLoaded.modSlot) (fun _ => FixedTextLoaded.Value_intLoaded)
    (by decide) (by decide) (by decide) (fun image h => modResid_of_armPostGeomV h
      image.text.__moddi3Loaded image.text.__hidden___udivdi3Loaded
      (image.stackPrefixDisjoint h.spSLhi (by decide) (by decide)))

#print axioms binIntCell_of_postGeom
#print axioms StaticImageSupport.stackPrefixDisjoint
#print axioms ScaffoldRows.field_hIAdd
#print axioms ScaffoldRows.field_hISub
#print axioms ScaffoldRows.field_hIMul
#print axioms ScaffoldRows.field_hIDiv
#print axioms ScaffoldRows.field_hIMod
#print axioms ScaffoldRows.field_hILt
#print axioms ScaffoldRows.field_hILe
#print axioms ScaffoldRows.field_hIGt
#print axioms ScaffoldRows.field_hIGe
end Vsa.Sim
