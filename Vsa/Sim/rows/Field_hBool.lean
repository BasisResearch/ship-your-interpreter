import Vsa.Sim.rows.AssemblySkeleton

/-!
# RUN-1 field `hBool` — reduced to the CALLEE GEOMETRY ONLY (wave 47e)

Bool twin of `Field_hNull.lean`: the widener half of `BoolLeafResid` is
discharged by `leafWidenP_of_entry` (wave 47e `EntryStackSurv` +
`LeafExitPin`); the residual gap is EXACTLY the `EvalBoolEntry`-minus-
`EvalEntry` callee geometry (`evalentry-missing-nbs-callee-geom`; the
verdict's `BoolGeom`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout)
open Vsa.Sim.TermSimAssembly
open Vsa.Sim.Code

namespace Vsa.Sim.Rows

local notation "SpecSt" => Vsa.While.St

/-- The `EvalBoolEntry`-minus-`EvalEntry` callee geometry (value_bool window
`[0x800027f8, 0x8000280c)`, slot 2). -/
def BoolLeafGeom : Prop :=
  ∀ (st : SpecSt) (b : Bool) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env (.bool b) sp r sret aEnv aExpr m0 c →
    (sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat) ∧
    ((0x8000280c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027f8) ∧
    Value_boolLoaded c.σ.mem ∧
    Vsa.Sim.BoolSlotPinned c.σ.mem ∧
    ((0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 8)

/-- **`hBool` reduced**: geometry ⇒ the field (widener half FREE since 47e). -/
theorem field_hBool_of_geom (hG : BoolLeafGeom) :
    ∀ (st : SpecSt) (b : Bool), BoolLeafResid st b := by
  intro st b g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG st b g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact ⟨h1, h2, h3, h4, h5, Vsa.Sim.leafWidenP_of_entry hc⟩

/-- **The geometry, DISCHARGED** (wave 47f, the `GeomFrom` supplier layer):
projected off the amended `EvalEntry` — `nbs_pins` + the widened disjointness
literals (`omega` narrows the whole-text/whole-table windows to the bool ones). -/
theorem boolLeafGeom_discharged : BoolLeafGeom := by
  intro st b g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  refine ⟨?_, ?_, hc.nbs_pins.bool_code, hc.nbs_pins.bool_slot, ?_⟩
  · rcases hc.sret_vicode_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hc.vicode_stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hc.table_stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- **`hBool` DISCHARGED** (wave 47f): the bool-leaf residual holds outright. -/
theorem field_hBool : ∀ (st : SpecSt) (b : Bool), BoolLeafResid st b :=
  field_hBool_of_geom boolLeafGeom_discharged

/-- The skeleton-hole form (`assembly_skeleton.tsv` row `hBool`). -/
theorem skelHBool_discharged (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHBool L :=
  fun st b => field_hBool st b

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.field_hBool_of_geom
#print axioms Vsa.Sim.Rows.field_hBool
#print axioms Vsa.Sim.Rows.skelHBool_discharged
