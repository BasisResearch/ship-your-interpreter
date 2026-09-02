import Vsa.Sim.rows.AssemblySkeleton

/-!
# RUN-1 field `hNull` — reduced to the CALLEE GEOMETRY ONLY (wave 47e)

The wave-47e amendment (`EntryStackSurv` + `LeafExitPin`, see `Field_hInt.lean`)
discharges the WIDENER half of `NullLeafResid` (`leafWidenP_of_entry`).  What
remains is EXACTLY the `EvalNullEntry`-minus-`EvalEntry` callee geometry — the
independent gap `evalentry-missing-nbs-callee-geom` (`experiments/
observations.md`; machine-checked as `NullGeom` in
`experiments/fleet/obstructions/B1_reseat_footprint_verdict.lean`): `EvalEntry`
carries only the INT-pilot callee facts (`value_int_code`/`int_slot`/…), so the
`value_null` code pins, slot-3 jump-table pin, and the null-arm disjointness
windows are supplied by NOTHING.  `field_hNull_of_geom` is the machine-checked
reduction: the field closes the moment the geometry lands (an `EvalEntry`
widening / M6 `Layout` bundle — its own amendment wave).

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

/-- The `EvalNullEntry`-minus-`EvalEntry` callee geometry (the verdict's
`NullGeom`, on main): value_null window `[0x800027ec, 0x800027f8)`
disjointness, code + slot-3 pins.  NOT derivable from `EvalEntry` (int-pilot
fields only) — the open gap `evalentry-missing-nbs-callee-geom`. -/
def NullLeafGeom : Prop :=
  ∀ (st : SpecSt) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env .null sp r sret aEnv aExpr m0 c →
    (sret.toNat + 24 ≤ 0x800027ec ∨ 0x800027f8 ≤ sret.toNat) ∧
    ((0x800027f8 : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x800027ec) ∧
    Value_nullLoaded c.σ.mem ∧
    Vsa.Sim.NullSlotPinned c.σ.mem ∧
    ((0x80019f58 : Nat) + 16 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 12)

/-- **`hNull` reduced**: geometry ⇒ the field (the widener half is FREE since
wave 47e). -/
theorem field_hNull_of_geom (hG : NullLeafGeom) : ∀ st : SpecSt, NullLeafResid st := by
  intro st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hG st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact ⟨h1, h2, h3, h4, h5, Vsa.Sim.leafWidenP_of_entry hc⟩

/-- **The geometry, DISCHARGED** (wave 47f, the `GeomFrom` supplier layer):
projected off the amended `EvalEntry` — `nbs_pins` supplies the code/slot pins,
the widened `sret_vicode_disjoint`/`vicode_stack_disjoint`/
`table_stack_disjoint` literals supply the window facts (`omega` narrows the
whole-text/whole-table windows to the null ones). -/
theorem nullLeafGeom_discharged : NullLeafGeom := by
  intro st g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  refine ⟨?_, ?_, hc.nbs_pins.null_code, hc.nbs_pins.null_slot, ?_⟩
  · rcases hc.sret_vicode_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hc.vicode_stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hc.table_stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

/-- **`hNull` DISCHARGED** (wave 47f): the null-leaf residual holds outright. -/
theorem field_hNull : ∀ st : SpecSt, NullLeafResid st :=
  field_hNull_of_geom nullLeafGeom_discharged

/-- The skeleton-hole form (`assembly_skeleton.tsv` row `hNull`). -/
theorem skelHNull_discharged (L : Layout) : Vsa.Sim.TermAssembly.Skel.SkelHNull L :=
  fun st => field_hNull st

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.field_hNull_of_geom
#print axioms Vsa.Sim.Rows.field_hNull
#print axioms Vsa.Sim.Rows.skelHNull_discharged
