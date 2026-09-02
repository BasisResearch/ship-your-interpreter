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

/-! ## Wave 47g — the `StrPayloadGeom` supplier VERDICT (Law 4)

The task was to thread the payload region facts "from where they exist".
Machine-checked survey result: THEY EXIST NOWHERE ON MAIN.

* `ExprRepr.str` (`Vsa/MemRepr.lean`) carries only `read32`(kind) +
  `read64`(payload ptr) + `CString` — no region facts, and `p = 0` is not
  even excluded (`CString m 0 s` is satisfiable).
* `StoreRepr` (`Vsa/RuntimeRepr.lean`) pins `A.contains` for FRAMES and
  CLOSURES only — the AST is parsed before `interp_run` and is not a store
  object; no `A.contains` fact mentions AST nodes or their string payloads.
* `ProgramRepr`/`StmtArrayRepr` are pure pointer-chase relations;
  `Layout.atInterpRun` (`Vsa/Refinement.lean`) is fully abstract.

So `StrPayloadGeom` is NOT derivable from a bare `EvalEntry`: nothing
constrains where the literal's cstring bytes sit relative to `SL`/`sp`/`sret`.
Per Law 4, the gap is pinned below as ONE named premise on the ExprRepr/
AST-region side — `EvalEntryStrAstRegion`, the `.str`-root projection of the
observation's proposed `ast_region` `EvalEntry` amendment — and the discharge
of `field_hStr` FROM that premise is machine-checked
(`field_hStr_of_astRegion`), so the future amendment wave only has to supply
the premise (entry field + hereditary `ExprNodesIn` transport), not redo any
geometry. -/

/-- **The `.str` node's payload lives in an AST region `[lo, hi)`** with a
nonzero pointer: the ExprRepr-side region fact `ExprRepr.str` lacks.  This is
the `.str` case of the (future) hereditary `ExprNodesIn` AST-arena invariant —
observation `strleafgeom-payload-ast-region` proposal.  Named-field structure
(gate shape); `lo`/`hi` are parameters (a `Prop` structure cannot carry data
fields). -/
structure StrPayloadIn (m : Mem) (lo hi a : Nat) (s : String) : Prop where
  payload : ∀ p : Nat, read64 m (a + 8) = some p →
    p ≠ 0 ∧ lo ≤ p ∧ p + s.length < hi

/-- **THE named premise** (Law 4; supplies `StrPayloadGeom`, hence `hStr`).
Every `EvalEntry` at a `.str` node comes with an AST region containing the
payload cstring, disjoint from the WHOLE stack region `[SL.lo, SL.hi)` and
from the sret buffer.  This is exactly the `.str` projection of the proposed
`ast_region` `EvalEntry` field: the whole-stack form (not `[SL.lo, sp)`) is
the transport-closed one — a child entry's `sp - 1088` scribble and its
in-stack `subsret` are both absorbed by it, so the amendment threads ONE fact,
not per-entry literals.  Supplied at the top by the parse-arena layout (M6);
nothing on main pins it — see the verdict block above. -/
def EvalEntryStrAstRegion : Prop :=
  ∀ (st : SpecSt) (s : String) (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (d : Nat) (env : Addr) (sp r sret aEnv aExpr : BitVec 64) (m0 : Mem) (c : Config),
    Vsa.Sim.EvalEntry g N A SL φf φc st d env (.str s) sp r sret aEnv aExpr m0 c →
    ∃ lo hi,
      StrPayloadIn c.σ.mem lo hi aExpr.toNat s ∧
      (hi ≤ SL.lo ∨ SL.hi ≤ lo) ∧
      (hi ≤ sret.toNat ∨ sret.toNat + 24 ≤ lo)

/-- The AST-region premise supplies the payload geometry: region-vs-stack
gives the `SL.lo`/`sp` disjunction (`sp ≤ SL.hi` from the entry's `stackOK`),
region-vs-sret gives the sret disjunction, `StrPayloadIn` gives `p ≠ 0`. -/
theorem strPayloadGeom_of_astRegion (hA : EvalEntryStrAstRegion) :
    StrPayloadGeom := by
  intro st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨lo, hi, hin, hstk, hsret⟩ :=
    hA st s g N A SL φf φc d env sp r sret aEnv aExpr m0 c hc
  obtain ⟨-, hsphi, -⟩ := hc.stackOK
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · obtain ⟨-, hplo, hphi⟩ := hin.payload p hp
    rcases hstk with h | h
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  · obtain ⟨hnz, hplo, hphi⟩ := hin.payload p hp
    refine ⟨hnz, ?_⟩
    rcases hsret with h | h
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)

/-- **`hStr` discharged FROM the named AST-region premise** — the whole
residual is now `EvalEntryStrAstRegion` alone; the future `ast_region`
amendment plugs in here with zero geometry rework. -/
theorem field_hStr_of_astRegion (hA : EvalEntryStrAstRegion) :
    ∀ (st : SpecSt) (s : String), StrLeafResid st s :=
  field_hStr_of_payload (strPayloadGeom_of_astRegion hA)

end Vsa.Sim.Rows

#print axioms Vsa.Sim.Rows.field_hStr_of_geom
#print axioms Vsa.Sim.Rows.field_hStr_of_payload
#print axioms Vsa.Sim.Rows.strPayloadGeom_of_astRegion
#print axioms Vsa.Sim.Rows.field_hStr_of_astRegion
