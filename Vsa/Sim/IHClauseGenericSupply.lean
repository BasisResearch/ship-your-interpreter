import Vsa.Sim.IHClauseGeneric
import Vsa.Sim.IntegerCellSuppliers
import Vsa.Sim.rows.EvalNegRowFootprint
import Vsa.Sim.rows.EvalNotRowFootprint
import Vsa.Sim.rows.EvalOrTrueRowFootprint
import Vsa.Sim.rows.EvalAndFalseRowFootprint
import Vsa.Sim.rows.EvalAndTrueRowFootprint
import Vsa.Sim.rows.EvalOrFalseRowFootprint
import Vsa.Sim.rows.EvalAddRowFootprint
import Vsa.Sim.rows.EvalSubRowFootprint
import Vsa.Sim.rows.EvalMulRowFootprint
import Vsa.Sim.rows.EvalDivRowFootprint
import Vsa.Sim.rows.EvalModRowFootprint
import Vsa.Sim.rows.EvalLeRowFootprint
import Vsa.Sim.rows.EvalGtRowFootprint
import Vsa.Sim.rows.EvalGeRowFootprint
import Vsa.Sim.rows.EvalEqNeRowFootprint

/-!
# `IHClauseGenericSupply` — the row-contract premises of the generic steps (IH tower, Level 2)

`IHClauseGeneric.lean` states each non-leaf step of the `Footprint` clause over a
NAMED row contract (`NegRowF`, `NotRowF`, `LogicalShortRowF`, `LogicalFallRowF`,
`IntCellF`, …).  Level 1B landed the footprint sibling of every one-child arm and
of the nine integer cells, each as an unconditional supplier
(`rows/Eval<Arm>RowFootprint.lean`).  This file discharges the contracts from those
suppliers and lands the generic steps CLOSED at the generator's field types:

| step | supplier chain |
|---|---|
| `footprint.hNeg` | `evalNegIHF` ⇒ `negRowF_closed` |
| `footprint.hNot` | `evalNotIHF` ⇒ `notRowF_closed` |
| `footprint.hOrTrue` | `evalOrTrueIHF` ⇒ `logicalShortRowF_orTrue` |
| `footprint.hAndFalse` | `evalAndFalseIHF` ⇒ `logicalShortRowF_andFalse` |
| `footprint.hAndTrue` | `evalAndTrueIHF` ⇒ `logicalFallRowF_andTrue` |
| `footprint.hOrFalse` | `evalOrFalseIHF` ⇒ `logicalFallRowF_orFalse` |

and the nine integer cells `intCellF_<op> : IntCellF .<op> …` from
`bin<Op>CellF_of` (Level 1B) at the head footprint `binaryHeadFootprintSupply` and
the landed residual suppliers `ScaffoldRows.field_hI<Op>`
(`IntegerCellSuppliers.lean`).  Eight are unconditional; `intCellF_div` takes the
`INT64_MIN / -1` subcase as the named premise `DivOverflowCellF`, exactly as
`eval_binary_row` takes `hDivOv : BinDivOverflowCell`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## 1. The one-child and logical row contracts -/

/-- `NegRowF` from the landed footprint row `evalNegIHF`. -/
theorem negRowF_closed : NegRowF :=
  fun st d env e st' n hE hIH => evalNegIHF st st' d env e n hE hIH

/-- `NotRowF` from the landed footprint row `evalNotIHF`. -/
theorem notRowF_closed : NotRowF :=
  fun st d env e st' v hE hIH => evalNotIHF st st' d env e v hE hIH

/-- The or-true short-circuit contract from `evalOrTrueIHF`. -/
theorem logicalShortRowF_orTrue : LogicalShortRowF .or true true :=
  fun st d env l r st' lv hE hb hIH => evalOrTrueIHF st st' d env l r lv hE hb hIH

/-- The and-false short-circuit contract from `evalAndFalseIHF`. -/
theorem logicalShortRowF_andFalse : LogicalShortRowF .and false false :=
  fun st d env l r st' lv hE hb hIH => evalAndFalseIHF st st' d env l r lv hE hb hIH

/-- The and-true fall-through contract from `evalAndTrueIHF`. -/
theorem logicalFallRowF_andTrue : LogicalFallRowF .and true :=
  fun st d env l r st' st'' lv rv hEl hb hEr ihL ihR =>
    evalAndTrueIHF st st' st'' d env l r lv rv hEl hb hEr ihL ihR

/-- The or-false fall-through contract from `evalOrFalseIHF`. -/
theorem logicalFallRowF_orFalse : LogicalFallRowF .or false :=
  fun st d env l r st' st'' lv rv hEl hb hEr ihL ihR =>
    evalOrFalseIHF st st' st'' d env l r lv rv hEl hb hEr ihL ihR

/-! ## 2. The nine integer cells

Each cell is the Level-1B `bin<Op>CellF_of` at the closed head footprint supply
and the landed integer residual supplier; the parent derivation the `F` cell asks
for is rebuilt from the two child derivations and `binOpSem`. -/

theorem intCellF_add : IntCellF .add (fun a b => .int (wrap64 (a + b))) (fun _ _ => True) := by
  intro st d env el er st' st'' a b hEl hEr ihL ihR _
  exact binAddCellF_of (binaryHeadFootprintSupply noArenaFoot noArenaFoot)
    ScaffoldRows.field_hIAdd st d env el er st' st'' a b hEl hEr ihL ihR
    (EvalE.binary st d env .add el er st' st'' (.int a) (.int b) _ hEl hEr (by simp [binOpSem]))

theorem intCellF_sub : IntCellF .sub (fun a b => .int (wrap64 (a - b))) (fun _ _ => True) := by
  intro st d env el er st' st'' a b hEl hEr ihL ihR _
  exact binSubCellF_of (binaryHeadFootprintSupply noArenaFoot noArenaFoot)
    ScaffoldRows.field_hISub st d env el er st' st'' a b hEl hEr ihL ihR
    (EvalE.binary st d env .sub el er st' st'' (.int a) (.int b) _ hEl hEr (by simp [binOpSem]))

theorem intCellF_mul : IntCellF .mul (fun a b => .int (wrap64 (a * b))) (fun _ _ => True) := by
  intro st d env el er st' st'' a b hEl hEr ihL ihR _
  exact binMulCellF_of (binaryHeadFootprintSupply noArenaFoot noArenaFoot)
    ScaffoldRows.field_hIMul st d env el er st' st'' a b hEl hEr ihL ihR
    (EvalE.binary st d env .mul el er st' st'' (.int a) (.int b) _ hEl hEr (by simp [binOpSem]))

/-- The `.div` cell.  `binOpSem` guards only `b ≠ 0`, so the `INT64_MIN / -1`
subcase (which the hardware seam `__divdi3` covers by a different path) is the
named premise `DivOverflowCellF` — the footprint sibling of `eval_binary_row`'s
`hDivOv : BinDivOverflowCell`.  Supplier: the wrap-semantics division row. -/
theorem intCellF_div (hOv : DivOverflowCellF) :
    IntCellF .div (fun a b => .int (wrap64 (a.tdiv b))) (fun _ b => b ≠ 0) := by
  intro st d env el er st' st'' a b hEl hEr ihL ihR hb0
  by_cases hov : (a = -2^63 ∧ b = -1)
  · obtain ⟨ha, hb⟩ := hov
    subst ha; subst hb
    exact hOv st d env el er st' st'' (-2^63) (-1) hEl hEr ihL ihR rfl rfl
  · exact binDivCellF_of (binaryHeadFootprintSupply noArenaFoot noArenaFoot)
      ScaffoldRows.field_hIDiv st d env el er st' st'' a b hb0 hov hEl hEr ihL ihR
      (EvalE.binary st d env .div el er st' st'' (.int a) (.int b) _ hEl hEr
        (by simp [binOpSem, hb0]))

theorem intCellF_mod : IntCellF .mod (fun a b => .int (wrap64 (a.tmod b))) (fun _ b => b ≠ 0) := by
  intro st d env el er st' st'' a b hEl hEr ihL ihR hb0
  exact binModCellF_of (binaryHeadFootprintSupply noArenaFoot noArenaFoot)
    ScaffoldRows.field_hIMod st d env el er st' st'' a b hb0 hEl hEr ihL ihR
    (EvalE.binary st d env .mod el er st' st'' (.int a) (.int b) _ hEl hEr
      (by simp [binOpSem, hb0]))

theorem intCellF_lt_closed : IntCellF .lt (fun a b => .bool (a < b)) (fun _ _ => True) :=
  intCellF_lt ScaffoldRows.field_hILt

theorem intCellF_le : IntCellF .le (fun a b => .bool (a ≤ b)) (fun _ _ => True) := by
  intro st d env el er st' st'' a b hEl hEr ihL ihR _
  exact binLeCellF_of (binaryHeadFootprintSupply noArenaFoot noArenaFoot)
    ScaffoldRows.field_hILe st d env el er st' st'' a b hEl hEr ihL ihR
    (EvalE.binary st d env .le el er st' st'' (.int a) (.int b) _ hEl hEr (by simp [binOpSem]))

theorem intCellF_gt : IntCellF .gt (fun a b => .bool (a > b)) (fun _ _ => True) := by
  intro st d env el er st' st'' a b hEl hEr ihL ihR _
  exact binGtCellF_of (binaryHeadFootprintSupply noArenaFoot noArenaFoot)
    ScaffoldRows.field_hIGt st d env el er st' st'' a b hEl hEr ihL ihR
    (EvalE.binary st d env .gt el er st' st'' (.int a) (.int b) _ hEl hEr (by simp [binOpSem]))

theorem intCellF_ge : IntCellF .ge (fun a b => .bool (a ≥ b)) (fun _ _ => True) := by
  intro st d env el er st' st'' a b hEl hEr ihL ihR _
  exact binGeCellF_of (binaryHeadFootprintSupply noArenaFoot noArenaFoot)
    ScaffoldRows.field_hIGe st d env el er st' st'' a b hEl hEr ihL ihR
    (EvalE.binary st d env .ge el er st' st'' (.int a) (.int b) _ hEl hEr (by simp [binOpSem]))

/-! ## 3. The binary dispatcher's cell record

`hBinary` is the dispatcher over `BinaryFootprintCells`.  Nine fields are the
integer cells above; the remaining six are exactly the cells `eval_binary_row`
itself takes as residuals: the equality pair at the LANDED `BinEqCell` suppliers
(through `eqCellF_of`/`neCellF_of`, `rows/EvalEqNeRowFootprint.lean`), the four
string comparisons (`BinStrCmpCellF`, `binStrCmpCellF_of`), and the division
overflow (`DivOverflowCellF`, the footprint twin of `eval_binary_row`'s `hDivOv`). -/

/-- The non-allocating binary cells, with the nine integer cells discharged. -/
theorem binaryFootprintCells_of
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    (hStrLt : BinStrCmpCellF .lt (fun sl sr => sl < sr))
    (hStrLe : BinStrCmpCellF .le (fun sl sr => sl < sr || sl == sr))
    (hStrGt : BinStrCmpCellF .gt (fun sl sr => sr < sl))
    (hStrGe : BinStrCmpCellF .ge (fun sl sr => sr < sl || sl == sr)) :
    BinaryFootprintCells where
  add := intCellF_add
  sub := intCellF_sub
  mul := intCellF_mul
  div := intCellF_div hDivOv
  mod := intCellF_mod
  lt := intCellF_lt_closed
  le := intCellF_le
  gt := intCellF_gt
  ge := intCellF_ge
  eq := eqCellF_of hEq
  ne := neCellF_of hNe
  strLt := hStrLt
  strLe := hStrLe
  strGt := hStrGt
  strGe := hStrGe

/-! ## 3. The generic steps at the generator's field types, CLOSED -/

namespace IHClauseGeneric.footprint

/-- `hNeg`: CLOSED (the landed negation footprint row). -/
theorem hNeg :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int)
      (a : EvalE st d env e st' (Value.int n)),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' (Value.int n) a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.unary UnOp.neg e) st'
        (Value.int (wrap64 (-n))) (EvalE.neg st d env e st' n a) →
      EvalIHF noArenaFoot st d env e st' (Value.int n) →
      EvalIHF noArenaFoot st d env (Expr.unary UnOp.neg e) st' (Value.int (wrap64 (-n))) :=
  hNeg_of negRowF_closed

/-- `hNot`: CLOSED (the landed logical-not footprint row). -/
theorem hNot :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)
      (a : EvalE st d env e st' v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' v a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.unary UnOp.not e) st'
        (Value.bool !v.truthy) (EvalE.not st d env e st' v a) →
      EvalIHF noArenaFoot st d env e st' v →
      EvalIHF noArenaFoot st d env (Expr.unary UnOp.not e) st' (Value.bool !v.truthy) :=
  hNot_of notRowF_closed

/-- `hOrTrue`: CLOSED. -/
theorem hOrTrue :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.or l r) st'
        (Value.bool true) (EvalE.orTrue st d env l r st' lv a a_1) →
      EvalIHF noArenaFoot st d env l st' lv →
      EvalIHF noArenaFoot st d env (Expr.logical LogOp.or l r) st' (Value.bool true) :=
  hOrTrue_of logicalShortRowF_orTrue

/-- `hAndFalse`: CLOSED. -/
theorem hAndFalse :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.and l r) st'
        (Value.bool false) (EvalE.andFalse st d env l r st' lv a a_1) →
      EvalIHF noArenaFoot st d env l st' lv →
      EvalIHF noArenaFoot st d env (Expr.logical LogOp.and l r) st' (Value.bool false) :=
  hAndFalse_of logicalShortRowF_andFalse

/-- `hOrFalse`: CLOSED. -/
theorem hOrFalse :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false) (a_2 : EvalE st' d env r st'' rv),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_2 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.or l r) st''
        (Value.bool rv.truthy) (EvalE.orFalse st d env l r st' st'' lv rv a a_1 a_2) →
      EvalIHF noArenaFoot st d env l st' lv →
      EvalIHF noArenaFoot st' d env r st'' rv →
      EvalIHF noArenaFoot st d env (Expr.logical LogOp.or l r) st'' (Value.bool rv.truthy) :=
  hOrFalse_of logicalFallRowF_orFalse

/-- `hAndTrue`: CLOSED. -/
theorem hAndTrue :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true) (a_2 : EvalE st' d env r st'' rv),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_2 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.and l r) st''
        (Value.bool rv.truthy) (EvalE.andTrue st d env l r st' st'' lv rv a a_1 a_2) →
      EvalIHF noArenaFoot st d env l st' lv →
      EvalIHF noArenaFoot st' d env r st'' rv →
      EvalIHF noArenaFoot st d env (Expr.logical LogOp.and l r) st'' (Value.bool rv.truthy) :=
  hAndTrue_of logicalFallRowF_andTrue


/-- **`hBinary` from the base row's own cells.**  Exactly `eval_binary_row`'s
hypotheses at the footprint contract: the nine integer cells are discharged
(section 2), the equality pair, the four string comparisons, the division
overflow and — only for `op = .add` — the two string-concatenation cells remain,
as they do in the base row.  The concatenation cells ALLOCATE, so at
`noArenaFoot` they are unsatisfiable; the guarded step below excludes them. -/
theorem hBinary_of_base
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    (hStrLt : BinStrCmpCellF .lt (fun sl sr => sl < sr))
    (hStrLe : BinStrCmpCellF .le (fun sl sr => sl < sr || sl == sr))
    (hStrGt : BinStrCmpCellF .gt (fun sl sr => sr < sl))
    (hStrGe : BinStrCmpCellF .ge (fun sl sr => sr < sl || sl == sr))
    (hStrAddL : StrAddLCellF) (hStrAddR : StrAddRCellF) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : SpecSt)
      (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv)
      (a_2 : binOpSem st''.store op lv rv = some v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_1 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.binary op l r) st'' v
        (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2) →
      EvalIHF noArenaFoot st d env l st' lv →
      EvalIHF noArenaFoot st' d env r st'' rv →
      EvalIHF noArenaFoot st d env (Expr.binary op l r) st'' v :=
  fun st d env op l r st' st'' lv rv v a a_1 a_2 o1 o2 o3 ihL ihR =>
    hBinary_of_cells
      (binaryFootprintCells_of hDivOv hEq hNe hStrLt hStrLe hStrGt hStrGe)
      st d env op l r st' st'' lv rv v a a_1 a_2 (fun _ => ⟨hStrAddL, hStrAddR⟩)
      o1 o2 o3 ihL ihR

end IHClauseGeneric.footprint


namespace IHClauseGeneric.footprintNA

/-- **`hBinary` of the guarded clause from the base row's own cells.**  The guard
excludes `op = .add`, so the two allocating concatenation cells are gone; what
remains is exactly the residual set `eval_binary_row` itself carries beyond the
nine integer cells. -/
theorem hBinary_of_base
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    (hStrLt : BinStrCmpCellF .lt (fun sl sr => sl < sr))
    (hStrLe : BinStrCmpCellF .le (fun sl sr => sl < sr || sl == sr))
    (hStrGt : BinStrCmpCellF .gt (fun sl sr => sr < sl))
    (hStrGe : BinStrCmpCellF .ge (fun sl sr => sr < sl || sl == sr)) :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : SpecSt)
      (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv)
      (a_2 : binOpSem st''.store op lv rv = some v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_1 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.binary op l r) st'' v
        (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2) →
      (IHClauseGeneric.noAllocExpr l = true → EvalIHF noArenaFoot st d env l st' lv) →
      (IHClauseGeneric.noAllocExpr r = true → EvalIHF noArenaFoot st' d env r st'' rv) →
      (IHClauseGeneric.noAllocExpr (Expr.binary op l r) = true →
        EvalIHF noArenaFoot st d env (Expr.binary op l r) st'' v) :=
  hBinary (binaryFootprintCells_of hDivOv hEq hNe hStrLt hStrLe hStrGt hStrGe)

end IHClauseGeneric.footprintNA

#print axioms negRowF_closed
#print axioms notRowF_closed
#print axioms logicalShortRowF_orTrue
#print axioms logicalShortRowF_andFalse
#print axioms logicalFallRowF_andTrue
#print axioms logicalFallRowF_orFalse
#print axioms intCellF_add
#print axioms intCellF_sub
#print axioms intCellF_mul
#print axioms intCellF_div
#print axioms intCellF_mod
#print axioms intCellF_lt_closed
#print axioms intCellF_le
#print axioms intCellF_gt
#print axioms intCellF_ge
#print axioms IHClauseGeneric.footprint.hNeg
#print axioms IHClauseGeneric.footprint.hNot
#print axioms IHClauseGeneric.footprint.hOrTrue
#print axioms IHClauseGeneric.footprint.hAndFalse
#print axioms IHClauseGeneric.footprint.hOrFalse
#print axioms IHClauseGeneric.footprint.hAndTrue
#print axioms binaryFootprintCells_of
#print axioms IHClauseGeneric.footprint.hBinary_of_base
#print axioms IHClauseGeneric.footprintNA.hBinary_of_base

end Vsa.Sim
