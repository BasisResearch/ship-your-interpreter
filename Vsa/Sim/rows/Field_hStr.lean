import Vsa.Sim.rows.AssemblySkeleton

/-!
# RUN-1 field `hStr` — reduced to the CALLEE GEOMETRY ONLY (wave 47e)

Str twin of `Field_hNull.lean`: the widener half of `StrLeafResid` is
discharged by `leafWidenP_of_entry` (wave 47e `EntryStackSurv` +
`LeafExitPin`); the residual gap is EXACTLY the `EvalStrEntry`-minus-
`EvalEntry` callee geometry + payload-string region facts
(`evalentry-missing-nbs-callee-geom`; the verdict's `StrGeom` — note the
payload facts are EXPRESSION-DEPENDENT, so they belong to an AST-region
bundle, not per-callee code pins).

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

/-- The `EvalStrEntry`-minus-`EvalEntry` callee geometry + payload-string
region facts (value_str window `[0x8000281c, 0x8000282c)`, slot 1). -/
def StrLeafGeom : Prop :=
  ∀ (st : SpecSt) (s : String) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env (.str s) sp r sret aEnv aExpr m0 c →
    (∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
      p + s.length < SL.lo ∨ sp.toNat ≤ p) ∧
    (∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
      p ≠ 0 ∧ (sret.toNat + 16 ≤ p ∨ p + s.length < sret.toNat)) ∧
    (sret.toNat + 24 ≤ 0x8000281c ∨ 0x8000282c ≤ sret.toNat) ∧
    ((0x8000282c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000281c) ∧
    Value_strLoaded c.σ.mem ∧
    Vsa.Sim.StrSlotPinned c.σ.mem ∧
    ((0x80019f58 : Nat) + 8 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58 + 4)

/-- **`hStr` reduced**: geometry ⇒ the field (widener half FREE since 47e). -/
theorem field_hStr_of_geom (hG : StrLeafGeom) :
    ∀ (st : SpecSt) (s : String), StrLeafResid st s := by
  intro st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ :=
    hG st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  exact ⟨h1, h2, h3, h4, h5, h6, h7, Vsa.Sim.leafWidenP_of_entry hc⟩

/-- **The REMAINING str residual after wave 47f: ONLY the payload-string region
facts.**  The code/slot half of `StrLeafGeom` is now supplied by the amended
`EvalEntry` (`nbs_pins` + widened disjointness literals, see
`field_hStr_of_payload`); what is left is EXPRESSION-DEPENDENT — where the
`.str s` literal's runtime bytes live relative to the stack/sret windows.
`ExprRepr`'s `.str` constructor carries only `read64` + `CString` (no region
facts), so these belong to the AST-region bundle (its own amendment: a
region-pinned `ExprRepr` or an AST-arena invariant), NOT to per-callee code
pins.  Observation: `strleafgeom-payload-ast-region` (`experiments/
observations.md`). -/
def StrPayloadGeom : Prop :=
  ∀ (st : SpecSt) (s : String) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env (.str s) sp r sret aEnv aExpr m0 c →
    (∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
      p + s.length < SL.lo ∨ sp.toNat ≤ p) ∧
    (∀ p : Nat, read64 c.σ.mem (aExpr.toNat + 8) = some p →
      p ≠ 0 ∧ (sret.toNat + 16 ≤ p ∨ p + s.length < sret.toNat))

/-- **`hStr` reduced FURTHER (wave 47f)**: the code/slot geometry half of
`StrLeafGeom` is discharged from the amended `EvalEntry`; the field now needs
ONLY the payload region facts. -/
theorem field_hStr_of_payload (hG : StrPayloadGeom) :
    ∀ (st : SpecSt) (s : String), StrLeafResid st s := by
  intro st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨h1, h2⟩ := hG st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  refine ⟨h1, h2, ?_, ?_, hc.nbs_pins.str_code, hc.nbs_pins.str_slot, ?_,
    Vsa.Sim.leafWidenP_of_entry hc⟩
  · rcases hc.sret_vicode_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hc.vicode_stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · rcases hc.table_stack_disjoint with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.field_hStr_of_geom
#print axioms Vsa.Sim.Rows.field_hStr_of_payload
