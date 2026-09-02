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

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.field_hStr_of_geom
