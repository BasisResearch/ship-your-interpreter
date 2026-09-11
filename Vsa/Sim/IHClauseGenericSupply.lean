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
import Vsa.Sim.StrCmpCellClauses

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

It also lands the PRODUCT clause `FootprintCov` (`EvalIHFP noArenaFoot` =
footprint ∧ the returned value's payload covered outside the stack window,
`Vsa/Sim/StrCmpCellClauses.lean`).  The four string-comparison cells need the
LEFT child's payload coverage — `valueSurvives_of_covered` consumes exactly it —
so they are stated at `BinStrCmpCellFP` (left child at the product clause) and
supplied by `binStrCmpCellFP_cov`; `binStrCmpCellF_cov` lowers them to the plain
`BinStrCmpCellF` through the CLOSED product clause `FootprintPayloadClause`.
`binaryFootprintCells_of` therefore no longer takes the four cells, and neither
does `footprint{,NA}.hBinary_of_base`.  The ten closed steps of the product
clause itself are `IHClauseGeneric.footprintCov.<case>`: the four leaves and the
six one-child arms, whose results are payload-free (`.int`/`.bool`/`.null`)
except the string literal, whose coverage is `evalStrPayloadIHF`.

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

/-! ## 2b. The product clause `EvalIHFP` and the four string-comparison cells

`valueSurvives_of_covered` (`StrCmpCellClauses.lean`) transports the left string
operand across the right child from the left child's PAYLOAD COVERAGE, which the
plain footprint contract does not carry.  So a string-comparison cell is stated
with its LEFT child at the product clause (`BinStrCmpCellFP`), where it is closed
but for the shared operand residual; the plain `BinStrCmpCellF` follows from the
CLOSED product clause at the left child's own derivation. -/

/-- Lift a footprint child contract to the product clause when the returned value
has no indirect payload (`ValuePayloadCovered` is `True` off `.str`/`.native`). -/
theorem EvalIHFP.of_footprint_payloadFree {F : FootFam} {st st' : SpecSt} {d env : Nat}
    {e : Expr} {v : Value}
    (hv : ∀ (P : Nat → Prop) m a, ValuePayloadCovered P m a v)
    (h : EvalIHF F st d env e st' v) : EvalIHFP F st d env e st' v :=
  EvalIHWithM.mono (fun _ _ _ _ _ _ _ _ _ hf => ⟨hf, hv _ _ _⟩) h

/-- **The string-comparison cell at the product clause.**  The left child carries
its payload coverage, the right child only its footprint, and the node's result
is a `Bool`, so the parent stays at the plain footprint contract. -/
def BinStrCmpCellFP (op : BinOp) (bres : String → String → Bool) : Prop :=
  ∀ (st : SpecSt) (d : Nat) (env : Addr) (el er : Expr)
    (st' st'' : SpecSt) (sl sr : String),
    EvalE st d env el st' (.str sl) →
    EvalE st' d env er st'' (.str sr) →
    EvalIHFP noArenaFoot st d env el st' (.str sl) →
    EvalIHF noArenaFoot st' d env er st'' (.str sr) →
    EvalIHF noArenaFoot st d env (.binary op el er) st'' (.bool (bres sl sr))

/-- **The product-clause cell supplier, CLOSED but for the operand residual.**
`binRow_strcmpF_cov` over the survival-free head `binaryHeadFootprintSupplyCov`:
the left temporary's survival across the right child is derived at the actual
memories from the left child's coverage, so `StrLeftSurvivesSupply` is gone.
`hOps` is the shared operand residual of `StrCmpCell.lean`
(`strCmpOperandsSupply_of_owned` derives it from `StrCmpOwnedOperands`). -/
theorem binStrCmpCellFP_cov (D : StrCmpOp) (C : D.Cert) (hOps : StrCmpOperandsSupply) :
    BinStrCmpCellFP D.op D.bres := by
  intro st d env el er st' st'' sl sr hEl hEr ihL ihR
  refine EvalIHF.of_exitF (fun g N A SL φf φc sp r sret aEnv aExpr m0 => ?_)
  exact binRow_strcmpF_cov D C (binaryHeadFootprintSupplyCov noArenaFoot)
    g N A SL φf φc st st' st'' d env el er sl sr sp r sret aEnv aExpr m0 hEl ihL ihR
    (EvalE.binary st d env D.op el er st' st'' (.str sl) (.str sr) _ hEl hEr (C.sem _ _ _))
    (fun c hc gpre v8 v9 v18 v19 hf c2 hTS =>
      strCmpResid_of_entry D C hc hf hTS
        (hOps g gpre N A SL φf φc st st' st'' d env D.op el er sl sr
          sp r sret aEnv aExpr v8 v9 v18 v19 m0 c c2 hc hf hTS))

/-- **The plain footprint cell from the closed product clause.**  The left child's
coverage is taken at its OWN derivation, so the cell's own `EvalIHF` left
hypothesis is discarded and the landed `BinStrCmpCellF` shape is produced. -/
theorem binStrCmpCellF_cov (D : StrCmpOp) (C : D.Cert) (hOps : StrCmpOperandsSupply)
    (hCL : FootprintPayloadClause) : BinStrCmpCellF D.op D.bres :=
  fun st d env el er st' st'' sl sr hEl hEr _ihL ihR =>
    binStrCmpCellFP_cov D C hOps st d env el er st' st'' sl sr hEl hEr
      (hCL st d env el st' (.str sl) hEl) ihR

/-! ## 3. The binary dispatcher's cell record

`hBinary` is the dispatcher over `BinaryFootprintCells`.  Nine fields are the
integer cells above; the remaining six are exactly the cells `eval_binary_row`
itself takes as residuals: the equality pair at the LANDED `BinEqCell` suppliers
(through `eqCellF_of`/`neCellF_of`, `rows/EvalEqNeRowFootprint.lean`), the division
overflow (`DivOverflowCellF`, the footprint twin of `eval_binary_row`'s `hDivOv`).
The four string comparisons are supplied here (`binStrCmpCellF_cov`) from the
shared operand residual and the closed product clause. -/

/-- The non-allocating binary cells, with the nine integer cells and the four
string comparisons discharged. -/
theorem binaryFootprintCells_of
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    (hOps : StrCmpOperandsSupply) (hCL : FootprintPayloadClause) :
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
  strLt := binStrCmpCellF_cov strCmpLt strCmpLt_cert hOps hCL
  strLe := binStrCmpCellF_cov strCmpLe strCmpLe_cert hOps hCL
  strGt := binStrCmpCellF_cov strCmpGt strCmpGt_cert hOps hCL
  strGe := binStrCmpCellF_cov strCmpGe strCmpGe_cert hOps hCL

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
(section 2) and so are the four string comparisons (section 2b, from the shared
operand residual and the closed product clause); the equality pair, the division
overflow and — only for `op = .add` — the two string-concatenation cells remain,
as they do in the base row.  The concatenation cells ALLOCATE, so at
`noArenaFoot` they are unsatisfiable; the guarded step below excludes them. -/
theorem hBinary_of_base
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    (hOps : StrCmpOperandsSupply) (hCL : FootprintPayloadClause)
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
      (binaryFootprintCells_of hDivOv hEq hNe hOps hCL)
      st d env op l r st' st'' lv rv v a a_1 a_2 (fun _ => ⟨hStrAddL, hStrAddR⟩)
      o1 o2 o3 ihL ihR

end IHClauseGeneric.footprint


namespace IHClauseGeneric.footprintNA

/-- **`hBinary` of the guarded clause from the base row's own cells.**  The guard
excludes `op = .add`, so the two allocating concatenation cells are gone; what
remains beyond the nine integer cells and the four string comparisons is the
equality pair and the division overflow. -/
theorem hBinary_of_base
    (hDivOv : DivOverflowCellF)
    (hEq : BinEqCell .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21))
    (hNe : BinEqCell .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21))
    (hOps : StrCmpOperandsSupply) (hCL : FootprintPayloadClause) :
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
  hBinary (binaryFootprintCells_of hDivOv hEq hNe hOps hCL)

end IHClauseGeneric.footprintNA

namespace IHClauseGeneric.footprintCov

/-! ## 4. The product clause `FootprintCov` — the ten closed steps

The clause is `EvalIHFP noArenaFoot` (`Vsa/Sim/StrCmpCellClauses.lean`): the
`Footprint` fact AND the returned value's payload covered outside the stack
window.  Off `.str`/`.native` the coverage half is `True`
(`ValuePayloadCovered`), so every step whose node returns an `.int`, a `.bool`
or `.null` is its `Footprint` step plus `EvalIHFP.of_footprint_payloadFree`; the
string literal's coverage is `evalStrPayloadIHF`.  Field types are those of
`Vsa/Sim/rows/IHClause_FootprintCov.lean`. -/

/-- `hInt`: CLOSED (payload-free result). -/
theorem hInt :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (n : Int),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.int n) st (Value.int n) (EvalE.int st d env n) →
      EvalIHFP noArenaFoot st d env (Expr.int n) st (Value.int n) :=
  fun st d env n hOld =>
    EvalIHFP.of_footprint_payloadFree (fun _ _ _ => trivial) (footprint.hInt st d env n hOld)

/-- `hStr`: CLOSED — the coverage half is the string leaf's own payload pin. -/
theorem hStr :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : String),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.str s) st (Value.str s) (EvalE.str st d env s) →
      EvalIHFP noArenaFoot st d env (Expr.str s) st (Value.str s) :=
  fun st d env s _ => evalStrPayloadIHF st d env s

/-- `hBool`: CLOSED (payload-free result). -/
theorem hBool :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (b : Bool),
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.bool b) st (Value.bool b)
        (EvalE.bool st d env b) →
      EvalIHFP noArenaFoot st d env (Expr.bool b) st (Value.bool b) :=
  fun st d env b hOld =>
    EvalIHFP.of_footprint_payloadFree (fun _ _ _ => trivial) (footprint.hBool st d env b hOld)

/-- `hNull`: CLOSED (payload-free result). -/
theorem hNull :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      Vsa.Sim.TermSimAssembly.mEvalE st d env Expr.null st Value.null (EvalE.null st d env) →
      EvalIHFP noArenaFoot st d env Expr.null st Value.null :=
  fun st d env hOld =>
    EvalIHFP.of_footprint_payloadFree (fun _ _ _ => trivial) (footprint.hNull st d env hOld)

/-- `hNeg`: CLOSED (payload-free result; the child's coverage is dropped). -/
theorem hNeg :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int)
      (a : EvalE st d env e st' (Value.int n)),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' (Value.int n) a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.unary UnOp.neg e) st'
        (Value.int (wrap64 (-n))) (EvalE.neg st d env e st' n a) →
      EvalIHFP noArenaFoot st d env e st' (Value.int n) →
      EvalIHFP noArenaFoot st d env (Expr.unary UnOp.neg e) st' (Value.int (wrap64 (-n))) :=
  fun st d env e st' n a o1 hOld ih =>
    EvalIHFP.of_footprint_payloadFree (fun _ _ _ => trivial)
      (footprint.hNeg st d env e st' n a o1 hOld (EvalIHFP.footprint (F := noArenaFoot) ih))

/-- `hNot`: CLOSED (payload-free result). -/
theorem hNot :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value)
      (a : EvalE st d env e st' v),
      Vsa.Sim.TermSimAssembly.mEvalE st d env e st' v a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.unary UnOp.not e) st'
        (Value.bool !v.truthy) (EvalE.not st d env e st' v a) →
      EvalIHFP noArenaFoot st d env e st' v →
      EvalIHFP noArenaFoot st d env (Expr.unary UnOp.not e) st' (Value.bool !v.truthy) :=
  fun st d env e st' v a o1 hOld ih =>
    EvalIHFP.of_footprint_payloadFree (fun _ _ _ => trivial)
      (footprint.hNot st d env e st' v a o1 hOld (EvalIHFP.footprint (F := noArenaFoot) ih))

/-- `hOrTrue`: CLOSED (payload-free result). -/
theorem hOrTrue :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.or l r) st'
        (Value.bool true) (EvalE.orTrue st d env l r st' lv a a_1) →
      EvalIHFP noArenaFoot st d env l st' lv →
      EvalIHFP noArenaFoot st d env (Expr.logical LogOp.or l r) st' (Value.bool true) :=
  fun st d env l r st' lv a a_1 o1 hOld ih =>
    EvalIHFP.of_footprint_payloadFree (fun _ _ _ => trivial)
      (footprint.hOrTrue st d env l r st' lv a a_1 o1 hOld
        (EvalIHFP.footprint (F := noArenaFoot) ih))

/-- `hAndFalse`: CLOSED (payload-free result). -/
theorem hAndFalse :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.and l r) st'
        (Value.bool false) (EvalE.andFalse st d env l r st' lv a a_1) →
      EvalIHFP noArenaFoot st d env l st' lv →
      EvalIHFP noArenaFoot st d env (Expr.logical LogOp.and l r) st' (Value.bool false) :=
  fun st d env l r st' lv a a_1 o1 hOld ih =>
    EvalIHFP.of_footprint_payloadFree (fun _ _ _ => trivial)
      (footprint.hAndFalse st d env l r st' lv a a_1 o1 hOld
        (EvalIHFP.footprint (F := noArenaFoot) ih))

/-- `hOrFalse`: CLOSED (payload-free result). -/
theorem hOrFalse :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false) (a_2 : EvalE st' d env r st'' rv),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_2 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.or l r) st''
        (Value.bool rv.truthy) (EvalE.orFalse st d env l r st' st'' lv rv a a_1 a_2) →
      EvalIHFP noArenaFoot st d env l st' lv →
      EvalIHFP noArenaFoot st' d env r st'' rv →
      EvalIHFP noArenaFoot st d env (Expr.logical LogOp.or l r) st'' (Value.bool rv.truthy) :=
  fun st d env l r st' st'' lv rv a a_1 a_2 o1 o2 hOld ihL ihR =>
    EvalIHFP.of_footprint_payloadFree (fun _ _ _ => trivial)
      (footprint.hOrFalse st d env l r st' st'' lv rv a a_1 a_2 o1 o2 hOld
        (EvalIHFP.footprint (F := noArenaFoot) ihL) (EvalIHFP.footprint (F := noArenaFoot) ihR))

/-- `hAndTrue`: CLOSED (payload-free result). -/
theorem hAndTrue :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value)
      (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true) (a_2 : EvalE st' d env r st'' rv),
      Vsa.Sim.TermSimAssembly.mEvalE st d env l st' lv a →
      Vsa.Sim.TermSimAssembly.mEvalE st' d env r st'' rv a_2 →
      Vsa.Sim.TermSimAssembly.mEvalE st d env (Expr.logical LogOp.and l r) st''
        (Value.bool rv.truthy) (EvalE.andTrue st d env l r st' st'' lv rv a a_1 a_2) →
      EvalIHFP noArenaFoot st d env l st' lv →
      EvalIHFP noArenaFoot st' d env r st'' rv →
      EvalIHFP noArenaFoot st d env (Expr.logical LogOp.and l r) st'' (Value.bool rv.truthy) :=
  fun st d env l r st' st'' lv rv a a_1 a_2 o1 o2 hOld ihL ihR =>
    EvalIHFP.of_footprint_payloadFree (fun _ _ _ => trivial)
      (footprint.hAndTrue st d env l r st' st'' lv rv a a_1 a_2 o1 o2 hOld
        (EvalIHFP.footprint (F := noArenaFoot) ihL) (EvalIHFP.footprint (F := noArenaFoot) ihR))

end IHClauseGeneric.footprintCov

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
#print axioms binStrCmpCellFP_cov
#print axioms binStrCmpCellF_cov
#print axioms IHClauseGeneric.footprintCov.hInt
#print axioms IHClauseGeneric.footprintCov.hStr
#print axioms IHClauseGeneric.footprintCov.hBool
#print axioms IHClauseGeneric.footprintCov.hNull
#print axioms IHClauseGeneric.footprintCov.hNeg
#print axioms IHClauseGeneric.footprintCov.hNot
#print axioms IHClauseGeneric.footprintCov.hOrTrue
#print axioms IHClauseGeneric.footprintCov.hAndFalse
#print axioms IHClauseGeneric.footprintCov.hOrFalse
#print axioms IHClauseGeneric.footprintCov.hAndTrue

end Vsa.Sim
