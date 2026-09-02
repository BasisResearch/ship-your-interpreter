import Vsa.Sim.rows.AssemblySkeleton

/-!
# B5-execarms — machine-checked OBSTRUCTIONS (Law 4)

Fleet batch B5 was to discharge the exec-arm skeleton holes
`SkelHSExpr … SkelHSWhileBreak`.  They are UNPROVABLE AS STATED — in fact
provably FALSE for the 11 dispatch-family fields: every underlying residual
bundle (`ExecCaseGeom`, `ExecExprGeom`, `ExecRetGeom`, `ExecRetNullGeom`,
`ExecVarNullGeom`, `ExecVarInitGeom`, `IfNoneGeom`, `WhileFalseGeom`,
`IfTrueGeom`, `IfFalseGeom`) asserts `StmtSlotPinned k armPC m0`
UNCONDITIONALLY under the residual's ∀-quantified `m0 : Mem`.  At `m0 = ∅`
the slot-pin's four byte lookups are `none`, refuting the ∃ — so each
`SkelHS*` hole (and hence `TermResidualsCore L` itself, which carries these
fields verbatim) is uninhabited.

The fix is a statement amendment (coordinator-owned, per the worker
contract): condition the slot pin + table/stack disjointness on the pinned
image — byte-pin premises in the `gen_layout.py` `groundSlot_k` supplier
shape, or a named `RodataPinned m0` hypothesis on the residual's `m0`.

The 3 loop-family fields (`hSBlock`/`hSForStart`/`hSWhileBreak`) have no
slot pin but demand the loop knot itself (`hstep`/`hWhileIH`/`hForIH` = the
full seq/for/while simulation as unconditional ∀-ghost oracles) — not
falsifiable by a cheap witness, and not suppliable by any landed lemma
(the supplier is the capstone under assembly); they are SKIPPED with the
named obstruction in `experiments/observations.md`
(`loop-geom-self-referential-oracles`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows
open Vsa.Sim.TermSimAssembly
local notation "SpecSt" => Vsa.While.St

set_option linter.unusedVariables false

namespace Vsa.Sim.TermAssembly.Skel

/-- **The core falsity**: no statement jump-table slot is pinned in the EMPTY
memory — the four byte lookups of `StmtSlotPinned.b0` all return `none`. -/
theorem stmtSlotPinned_empty_false (k : Nat) (armPC : BitVec 64) :
    ¬ Vsa.Sim.StmtSlotPinned k armPC (∅ : Mem) := by
  rintro ⟨⟨b0, b1, b2, b3, h0, -⟩⟩
  simp at h0

/-! Cheap witnesses for the residuals' ∀-instantiation. -/

/-- The empty spec state. -/
def st0 : SpecSt := ⟨⟨#[], #[]⟩, ""⟩
/-- The everywhere-`none` ghost register frame. -/
def g0 : (R : Register) → Option (RegisterType R) := fun _ => none
/-- A degenerate native-address table. -/
def N0 : NativeAddrs := ⟨0, 0, 0⟩
/-- A degenerate arena. -/
def A0 : Arena := ⟨0, 0⟩
/-- A degenerate stack layout. -/
def SL0 : StackLayout := ⟨0, 0⟩
/-- The zero correspondence map. -/
def φ0 : Addr → Nat := fun _ => 0

/-- **`hSBrk` is FALSE**: `BrkResid` at `m0 = ∅` demands
`StmtSlotPinned 7 execArmBrk ∅`. -/
theorem skelHSBrk_false (L : Layout) : ¬ SkelHSBrk L := fun h =>
  stmtSlotPinned_empty_false 7 Vsa.Sim.execArmBrk
    (h st0 g0 N0 A0 SL0 φ0 φ0 0 0 0 ∅).1

/-- **`hSCont` is FALSE** (slot 8, `execArmCont`, `m0 = ∅`). -/
theorem skelHSCont_false (L : Layout) : ¬ SkelHSCont L := fun h =>
  stmtSlotPinned_empty_false 8 Vsa.Sim.execArmCont
    (h st0 g0 N0 A0 SL0 φ0 φ0 0 0 0 ∅).1

/-- **`hSExpr` is FALSE** (slot 0, `execArmExpr`, `m0 = ∅`). -/
theorem skelHSExpr_false (L : Layout) : ¬ SkelHSExpr L := fun h =>
  stmtSlotPinned_empty_false 0 Vsa.Sim.execArmExpr
    (h st0 st0 0 0 (.int 0) .null g0 N0 A0 SL0 φ0 φ0 0 0 0 0 0 0 ∅).1

/-- **`hSRet` is FALSE** (slot 6, `execArmRet`, `m0 = ∅`). -/
theorem skelHSRet_false (L : Layout) : ¬ SkelHSRet L := fun h =>
  stmtSlotPinned_empty_false 6 Vsa.Sim.execArmRet
    (h st0 st0 0 0 (.int 0) .null g0 N0 A0 SL0 φ0 φ0 0 0 0 0 0 0 ∅).1

/-- **`hSRetNull` is FALSE** (slot 6, `execArmRet`, `m0 = ∅`). -/
theorem skelHSRetNull_false (L : Layout) : ¬ SkelHSRetNull L := fun h =>
  stmtSlotPinned_empty_false 6 Vsa.Sim.execArmRet
    (h st0 0 0 g0 N0 A0 SL0 φ0 φ0 0 0 0 0 0 0 ∅).1

/-- **`hSVarNull` is FALSE** (slot 1, `execArmVarDecl`, `m0 = ∅`). -/
theorem skelHSVarNull_false (L : Layout) : ¬ SkelHSVarNull L := fun h =>
  stmtSlotPinned_empty_false 1 Vsa.Sim.execArmVarDecl
    (h st0 0 0 "" g0 N0 A0 SL0 φ0 φ0 0 0 0 0 0 0 ∅).1

/-- **`hSVarInit` is FALSE** (slot 1, `execArmVarDecl`, `m0 = ∅`). -/
theorem skelHSVarInit_false (L : Layout) : ¬ SkelHSVarInit L := fun h =>
  stmtSlotPinned_empty_false 1 Vsa.Sim.execArmVarDecl
    (h st0 st0 0 0 "" (.int 0) .null g0 N0 A0 SL0 φ0 φ0 0 0 0 0 0 0 ∅).1

/-- **`hSIfNone` is FALSE** (slot 3, `execArmIf`, `m0 = ∅`). -/
theorem skelHSIfNone_false (L : Layout) : ¬ SkelHSIfNone L := fun h =>
  stmtSlotPinned_empty_false 3 Vsa.Sim.execArmIf
    (h st0 st0 0 0 (.int 0) .brk .null g0 N0 A0 SL0 φ0 φ0 0 0 0 0 0 0 ∅).hslot

/-- **`hSWhileFalse` is FALSE** (slot 4, `execArmWhile`, `m0 = ∅`). -/
theorem skelHSWhileFalse_false (L : Layout) : ¬ SkelHSWhileFalse L := fun h =>
  stmtSlotPinned_empty_false 4 Vsa.Sim.execArmWhile
    (h st0 st0 0 0 (.int 0) .brk .null g0 N0 A0 SL0 φ0 φ0 0 0 0 0 0 0 ∅).hslot

/-- **`hSIfTrue` is FALSE** (slot 3, `execArmIf`, `m0 = ∅`). -/
theorem skelHSIfTrue_false (L : Layout) : ¬ SkelHSIfTrue L := fun h =>
  stmtSlotPinned_empty_false 3 Vsa.Sim.execArmIf
    (h st0 st0 st0 0 0 (.int 0) .brk none .null .normal
      g0 N0 A0 SL0 φ0 φ0 0 0 0 0 0 0 ∅).hslot

/-- **`hSIfFalse` is FALSE** (slot 3, `execArmIf`, `m0 = ∅`). -/
theorem skelHSIfFalse_false (L : Layout) : ¬ SkelHSIfFalse L := fun h =>
  stmtSlotPinned_empty_false 3 Vsa.Sim.execArmIf
    (h st0 st0 st0 0 0 (.int 0) .brk .brk .null .normal
      g0 N0 A0 SL0 φ0 φ0 0 0 0 0 0 0 ∅).hslot

/-- **COROLLARY** — the assembly target itself is uninhabited: any
`TermResidualsCore L` carries `hSBrk` verbatim, refuted above.  This is the
strongest form of the obstruction: no supplier campaign can fill the record
until the residual statements are amended. -/
theorem termResidualsCore_false (L : Layout) : ¬ TermResidualsCore L := fun h =>
  skelHSBrk_false L h.hSBrk

#print axioms stmtSlotPinned_empty_false
#print axioms skelHSBrk_false
#print axioms skelHSCont_false
#print axioms skelHSExpr_false
#print axioms skelHSRet_false
#print axioms skelHSRetNull_false
#print axioms skelHSVarNull_false
#print axioms skelHSVarInit_false
#print axioms skelHSIfNone_false
#print axioms skelHSWhileFalse_false
#print axioms skelHSIfTrue_false
#print axioms skelHSIfFalse_false
#print axioms termResidualsCore_false

end Vsa.Sim.TermAssembly.Skel
