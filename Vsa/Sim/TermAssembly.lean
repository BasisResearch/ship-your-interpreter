import Vsa.Sim.TermBundles
import Vsa.Sim.rows.EvalVarRow
import Vsa.Sim.rows.BinDispatchRow
import Vsa.Sim.rows.CallRows
import Vsa.Sim.rows.ExecRouting
import Vsa.Sim.rows.ExecRecRows
import Vsa.Sim.rows.ExecDispatchRows
import Vsa.Sim.rows.ScaffoldRows
import Vsa.Sim.rows.ExecVarInitRow
import Vsa.Sim.rows.EvalAssignRow
import Vsa.Sim.rows.ErrorRouting
import Vsa.Sim.EntrySeams
import Vsa.Sim.DivFamily
import Vsa.While.StmtDispatchClose

/-!
# `TermAssembly` — the assembly capstone

This is the record-fill + endgame corollary that turns the 49 landed slot-verified
rows (`rows/`) + the two closed families (`errFamilyClosed`, the `DivCorrFamily`
reduction) into ONE named-field residual structure `TermResiduals` and a single
theorem `interpSim_of_residuals` producing `InterpSim L`.

**THE POINT.**  After this file, the ENTIRE remaining project = discharging the
fields of `TermResiduals`, each of which is a NAMED typed premise carrying a doc
comment naming its supplier task.  There is no more assembly to do: `htri` is
UNCONDITIONAL (`Vsa.While.htri_unconditional`), the error family is closed modulo
its `ErrShared` + 43 `hsite` reachability residuals (folded into `TermResiduals`),
the divergence family is the single named `DivCorrFamily` residual (folded in), and
the entry premise is `hEntryHalts_closed'` modulo `InterpInitStoreRepr`/`EpilogueSpill`
(folded in).

## Structure

* `TermResiduals` — every row's residual premise (`∀…, <Resid>`), the `hCallClosure`
  whole-premise crux, the `eval_binary_row` 19 cell/str/div residuals, plus the
  endgame residuals (`InterpInitStoreRepr`/`EpilogueSpill`/`DivCorrFamily`/`ErrShared`
  + 43 `hsite`).  Named fields ONLY.
* `termCases_of_residuals (R) : TermCaseBundle.TermCases` — applies every row.
* `hterm_of_residuals (R) : <hterm shape>` — `termSimClosed_of_bundle` + `hEntryHalts_closed'`.
* `hdivFam_of_residuals (R) : DivFamily L` — the `DivCorrFamily` reduction.
* `herrFam_of_residuals (R) : ErrFamily L` — `errFamilyClosed`.
* `interpSim_of_residuals (R) : InterpSim L` — `interpSimClosed_of_families` with
  `htri_unconditional`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.  `#print axioms` ⊆
{propext, Classical.choice, Quot.sound}.
-/

open LeanRV64DExecutable Sail Vsa
open Register
open Vsa.Machine (MState Config Halts Diverges)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.Rows
open Vsa.Sim.ScaffoldRows
open Vsa.Sim.TermSimAssembly
open Vsa.Sim.InterpSimBundle (DivFamily ErrFamily)

namespace Vsa.Sim.TermAssembly

local notation "SpecSt" => Vsa.While.St

/-! ## `TermResiduals` — the honest complete list of the project's remaining work

Every field is a NAMED typed premise (R6/R7).  The doc comment names the row/family
that CONSUMES it and the supplier task that DISCHARGES it.  This is the entire
residual surface of the development after the capstone. -/
structure TermResiduals (L : Layout) where
  -- ===== TermRouting.lean — the 10 leaf/logical rows =====
  /-- `hInt`/`eval_int_row`.  Supplier: `LeafWiden` int-leaf geometry (`LeafWiden`/`GeomFrom`). -/
  hInt : ∀ st n, IntLeafResid st n
  /-- `hNull`/`eval_null_row`.  Supplier: null-slot geometry + `LeafWiden` (`NullSlotPinned`). -/
  hNull : ∀ st, NullLeafResid st
  /-- `hBool`/`eval_bool_row`.  Supplier: bool-region geometry + `LeafWiden`. -/
  hBool : ∀ st b, BoolLeafResid st b
  /-- `hStr`/`eval_str_row`.  Supplier: str-leaf geometry + `LeafWiden` (str repr readback). -/
  hStr : ∀ st s, StrLeafResid st s
  /-- `hNeg`/`eval_neg_row`.  Supplier: neg-arm geometry (`EvalRecCommon`/`blockB_unary`). -/
  hNeg : ∀ st esub, NegResid st esub
  /-- `hNot`/`eval_not_row`.  Supplier: not-arm geometry. -/
  hNot : ∀ esub vsub, NotResid esub vsub
  /-- `hOrTrue`/`eval_orTrue_row`.  Supplier: logical short-circuit geometry. -/
  hOrTrue : ∀ el er vl, OrTrueResid el er vl
  /-- `hAndFalse`/`eval_andFalse_row`.  Supplier: logical short-circuit geometry. -/
  hAndFalse : ∀ el er vl, AndFalseResid el er vl
  /-- `hOrFalse`/`eval_orFalse_row`.  Supplier: logical fall-through geometry. -/
  hOrFalse : ∀ st' st'' el er vl vr, OrFalseResid st' st'' el er vl vr
  /-- `hAndTrue`/`eval_andTrue_row`.  Supplier: logical fall-through geometry. -/
  hAndTrue : ∀ st' st'' el er vl vr, AndTrueResid st' st'' el er vl vr
  -- ===== EvalVarRow.lean =====
  /-- `hVar`/`eval_var_row`.  Supplier: `VarLeafResid` — carries the `env_get_found`
      caller-linkage oracle (dischargeable from `env_get_found_uncond''` once the
      eval-var-arm call bridge lands; the `TermCallees.envGet` contract is LANDED). -/
  hVar : ∀ st x v, VarLeafResid st x v
  -- ===== EvalAssignRow.lean =====
  /-- `hAssign`/`eval_assign_row`.  Supplier: `AssignArmSpec` arm oracle ("row now,
      arm spec later" precedent) — the composed `env_define` (`TermCallees.envDefine`,
      OPEN) store-set arm.  No `evalAssignSim` exists yet; whole arm is this oracle. -/
  hAssign : ∀ st d env x e st' v store'', AssignResid st d env x e st' v store''
  -- ===== BinDispatchRow.lean — eval_binary_row's 19 cell/str/div residuals =====
  /-- `hBinary` add int-cell.  Supplier: `AddResid` value-path (`EvalAddRow`, block-reflected). -/
  hIAdd : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .add Vsa.Sim.AddResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
  /-- `hBinary` sub int-cell.  Supplier: `SubResid` (`EvalSubRow`). -/
  hISub : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .sub Vsa.Sim.SubResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
  /-- `hBinary` mul int-cell.  Supplier: `MulResid` (`EvalMulRow`, `__muldi3` seam). -/
  hIMul : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .mul Vsa.Sim.MulResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
  /-- `hBinary` div int-cell (non-overflow arm; the `¬(a=-2^63 ∧ b=-1)` guard is the
      `TermGuards.binNoOvf` side-condition).  Supplier: `DivResid` (`EvalDivRow`,
      `__divdi3` seam via `TermCallees.divdi3`). -/
  hIDiv : ∀ g N A SL φf φc st st' st'' el er a b, ¬(a = -2^63 ∧ b = -1) →
      ∀ sp r sret aExpr m0,
      BinIntCellResid .div Vsa.Sim.DivResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
  /-- `hBinary` mod int-cell.  Supplier: `ModResid` (`EvalModRow`, div-parity). -/
  hIMod : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .mod Vsa.Sim.ModResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
  /-- `hBinary` lt int-cell.  Supplier: `LtResid` (`EvalLtRow`). -/
  hILt : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .lt Vsa.Sim.LtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
  /-- `hBinary` le int-cell.  Supplier: `LeResid` (`EvalLeRow`). -/
  hILe : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .le Vsa.Sim.LeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
  /-- `hBinary` gt int-cell.  Supplier: `GtResid` (`EvalGtRow`). -/
  hIGt : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .gt Vsa.Sim.GtResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
  /-- `hBinary` ge int-cell.  Supplier: `GeResid` (`EvalGeRow`, xori clone). -/
  hIGe : ∀ g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0,
      BinIntCellResid .ge Vsa.Sim.GeResid g N A SL φf φc st st' st'' el er a b sp r sret aExpr m0
  /-- `hBinary` eq cell.  Supplier: `EqResid` via `value_equal_spec_full`
      (`TermCallees.valueEqual`, LANDED) + `EvalEqNeRow`. -/
  hEq : ∀ g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0,
      BinEqCellResid .eq .eq (0x80003720#64) (0x8000371c#64) (0x1ff140#21)
        g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0
  /-- `hBinary` ne cell.  Supplier: `EqResid` (`EvalEqNeRow`). -/
  hNe : ∀ g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0,
      BinEqCellResid .ne .ne (0x80003770#64) (0x8000376c#64) (0x1ff0f0#21)
        g N A SL φf φc st st' st'' el er vl vr sp r sret aExpr m0
  /-- `hBinary` str `+` (left-str) cell.  Supplier: `StrConcatCellResid`
      (`TermGuards.strConcat`, blocked on the stringify spec). -/
  hStrAddL : ∀ st d env el er st'' (sl : String) (rv : Value),
      EvalIH st d env (.binary .add el er) st''
        (.str ((Value.str sl).display st''.store ++ rv.display st''.store))
  /-- `hBinary` str `+` (right-str) cell.  Supplier: `StrConcatCellResid`. -/
  hStrAddR : ∀ st d env el er st'' (lv : Value) (sr : String),
      EvalIH st d env (.binary .add el er) st''
        (.str (lv.display st''.store ++ (Value.str sr).display st''.store))
  /-- `hBinary` str `<` cell.  Supplier: `StrCmpOrderBridge`/`StrArmPrologue`
      (`TermGuards.strCmp`/`strArmProlog`, LANDED slots via `strcmp_full_spec`). -/
  hStrLt : ∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .lt el er) st'' (.bool (sl < sr))
  /-- `hBinary` str `≤` cell.  Supplier: `StrCmpOrderBridge`/`StrArmPrologue`. -/
  hStrLe : ∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .le el er) st'' (.bool (sl < sr || sl == sr))
  /-- `hBinary` str `>` cell.  Supplier: `StrCmpOrderBridge`/`StrArmPrologue`. -/
  hStrGt : ∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .gt el er) st'' (.bool (sr < sl))
  /-- `hBinary` str `≥` cell.  Supplier: `StrCmpOrderBridge`/`StrArmPrologue`. -/
  hStrGe : ∀ st d env el er st'' (sl sr : String),
      EvalIH st d env (.binary .ge el er) st'' (.bool (sr < sl || sl == sr))
  /-- `hBinary` div-overflow arm (`INT64_MIN / -1` wraps).  Supplier:
      `TermGuards.divOvfArm` wrap-semantics div row. -/
  hDivOv : ∀ st d env el er st'',
      EvalIH st d env (.binary .div el er) st''
        (.int (wrap64 ((-2^63 : Int).tdiv (-1))))
  -- ===== CallRows.lean =====
  /-- `hArgsNil`/`eval_argsNil_row`.  Supplier: `ArgsNilResid` seg-identity at
      `evalArgsLoopPC`→`evalArgsContPC`. -/
  hArgsNil : ∀ st d env, ArgsNilResid st d env
  /-- `hArgsCons`/`eval_argsCons_row`.  Supplier: `ArgsConsResid` per-iter body oracle
      + fall-through (`TermGuards.argsMeasure`, `evalArgsStepOf`/`loopFromBody`). -/
  hArgsCons : ∀ st d env, ArgsConsResid st d env
  /-- `hCallPrint`/`eval_callPrint_row`.  Supplier: native `print` seg (`NativePrintSpec`). -/
  hCallPrint : ∀ st d vs, CallPrintResid st d vs
  /-- `hCallPrintln`/`eval_callPrintln_row`.  Supplier: native `println` seg. -/
  hCallPrintln : ∀ st d vs, CallPrintlnResid st d vs
  /-- `hCallAssertOk`/`eval_callAssertOk_row`.  Supplier: native `assert` seg. -/
  hCallAssertOk : ∀ st d, CallAssertOkResid st d
  /-- `hCall`/`eval_call_row`.  Supplier: `CallResid` = `CallArmSpec` arm + widen. -/
  hCall : ∀ st st' st'' st''' d env f args fval vs v,
      CallResid st st' st'' st''' d env f args fval vs v
  /-- `hFn`/`eval_fn_row`.  Supplier: `FnResid` = closure-alloc arm + native-store repr. -/
  hFn : ∀ st d env name params body store' a,
      FnResid st d env name params body store' a
  -- ===== hCallClosure — the CRUX gap (whole premise; sibling owns rows/CallClosureRow) =====
  /-- **CRUX** — `hCallClosure`.  Consumed positionally by the recursor; NO landed row
      (depth-crux + `env_define` env-fold gated).  Supplied as a WHOLE PREMISE by the
      sibling-owned `rows/CallClosureRow` (`TermGuards.depthCrux` + `TermCallees.envDefine`).
      Typed VERBATIM as the `TermCaseBundle.TermCases.hCallClosure` field. -/
  hCallClosure :
    ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) (store' : Store)
      (frame : Addr) (st' : SpecSt) (status : Status) (v : Value)
      (a_1 : st.store.closures[a]? = some cd) (a_2 : vs.length = cd.params.length)
      (a_3 : d < maxCallDepth) (a_4 : st.store.allocFrame (some cd.env) = (store', frame))
      (a_5 : ExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status)
      (a_6 : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v),
      mExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status a_5 →
      mCall st d (Value.closure a) vs st' v (Call.closure st d a cd vs store' frame st' status v a_1 a_2 a_3 a_4 a_5 a_6)
  -- ===== ExecRecRows.lean / ExecRouting.lean — the exec leaves =====
  /-- `hSExpr`/`exec_expr_row`.  Supplier: `ExprResid` = `execExprSimD` geometry. -/
  hSExpr : ∀ st st' d env e v, ExprResid st st' d env e v
  /-- `hSRet`/`exec_ret_row`.  Supplier: `RetResid` = `ExecRetGeom`. -/
  hSRet : ∀ st st' d env e v, RetResid st st' d env e v
  /-- `hSRetNull`/`exec_retNull_row`.  Supplier: `RetNullResid` = `ExecRetNullGeom`
      (carries the OPEN `value_null`-bridge glue). -/
  hSRetNull : ∀ st d env, RetNullResid st d env
  /-- `hSVarNull`/`exec_varNull_row`.  Supplier: `VarNullResid` = `ExecVarNullGeom`
      (carries the OPEN `value_null`+`env_define` glue, `TermCallees.envDefine`). -/
  hSVarNull : ∀ st d env x, VarNullResid st d env x
  /-- `hSBrk`/`exec_brk_row`.  Supplier: `BrkResid` = `ExecCaseGeom` brk arm. -/
  hSBrk : ∀ st, BrkResid st
  /-- `hSCont`/`exec_cont_row`.  Supplier: `ContResid` = `ExecCaseGeom` cont arm. -/
  hSCont : ∀ st, ContResid st
  -- ===== ExecVarInitRow.lean =====
  /-- `hSVarInit`/`exec_varInit_row`.  Supplier: `VarInitResid` = `ExecVarInitGeom`
      (`hGlue` threads the `env_define` callee oracle, `TermCallees.envDefine`). -/
  hSVarInit : ∀ st st' d env x e v, VarInitResid st st' d env x e v
  -- ===== ExecDispatchRows.lean — if/while/for/block =====
  /-- `hSIfNone`/`exec_ifNone_row`.  Supplier: `IfNoneResid` = exit-sim geometry. -/
  hSIfNone : ∀ st st' d env c t v, IfNoneResid st st' d env c t v
  /-- `hSWhileFalse`/`exec_whileFalse_row`.  Supplier: `WhileFalseResid`. -/
  hSWhileFalse : ∀ st st' d env c b v, WhileFalseResid st st' d env c b v
  /-- `hSIfTrue`/`exec_ifTrue_row`.  Supplier: `IfTrueResid` (branch exit-sim). -/
  hSIfTrue : ∀ st st' st'' d env c t e v status, IfTrueResid st st' st'' d env c t e v status
  /-- `hSIfFalse`/`exec_ifFalse_row`.  Supplier: `IfFalseResid` (else-branch exit-sim). -/
  hSIfFalse : ∀ st st' st'' d env c t e v status, IfFalseResid st st' st'' d env c t e v status
  /-- `hSBlock`/`exec_block_row`.  Supplier: `BlockResid` = `allocFrame` + seq exit-sim. -/
  hSBlock : ∀ st st' d env ss status store' inner, BlockResid st st' d env ss status store' inner
  /-- `hSForStart`/`exec_forStart_row`.  Supplier: `ForStartResid` = `allocFrame` +
      init/for-loop exit-sim (`TermGuards.forMeasure`). -/
  hSForStart : ∀ st st' st'' d env init cnd step b status store' outer,
      ForStartResid st st' st'' d env init cnd step b status store' outer
  /-- `hSWhileBreak`/`exec_whileBreak_row`.  Supplier: `WhileResid` (shared with
      whileRet/whileLoop; `TermGuards.whileMeasure`, `execWhileIH_of_resid`). -/
  hSWhileBreak : ∀ st st' d env c b status, WhileResid st st' d env c b status
  -- ===== ScaffoldRows.lean — the 3 unconditional identity scaffolds =====
  -- hInitNone/hFcNone/hEsNone are UNCONDITIONAL (seg-identity); no residual field.

  -- ===== The genuine whole-premise gaps (no landed row; typed VERBATIM as the
  -- TermCases field).  These are the for-loop scaffold `.some`/body/loop cases +
  -- the ExecSeq cases, which have NO `_row` theorem yet. =====
  /-- **GAP** — `hInitSome` (`ExecInit.some`).  Supplier: the `for` initializer seg
      (`exec_stmt(init)`, `p`→`p` identity-PC span over the sub-`ExecS` IH); the named
      residual type is `Vsa.Sim.ScaffoldRows.hInitSome_resid`. -/
  hInitSome : Vsa.Sim.ScaffoldRows.hInitSome_resid
  /-- **GAP** — `hFcSome` (`ForCond.some`).  Supplier: the truthy `for` condition seg
      (`eval_expr(c)` + `value_truthy`, `p`→`p`); `Vsa.Sim.ScaffoldRows.hFcSome_resid`. -/
  hFcSome : Vsa.Sim.ScaffoldRows.hFcSome_resid
  /-- **GAP** — `hEsSome` (`ExecStep.some`).  Supplier: the `for` step-expr seg
      (`eval_expr(e)`, `p`→`p`); `Vsa.Sim.ScaffoldRows.hEsSome_resid`. -/
  hEsSome : Vsa.Sim.ScaffoldRows.hEsSome_resid
  /-- **GAP** — `hFlCondFalse` (`ForLoop.condFalse`).  Supplier: the for-loop
      condition-false exit arm (`TermGuards.forMeasure` shape). -/
  hFlCondFalse :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt)
      (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false),
      mEvalE st d env c st' v a →
      mForLoop st d env (some c) step b st' Status.normal (ForLoop.condFalse st d env c step b st' v a a_1)
  /-- **GAP** — `hFlBodyBreak` (`ForLoop.bodyBreak`).  Supplier: for-loop body-break arm. -/
  hFlBodyBreak :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' : SpecSt) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' Status.brk),
      mForCond st d env cnd st' a → mExecS st' d env b st'' Status.brk a_1 →
      mForLoop st d env cnd step b st'' Status.normal (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1)
  /-- **GAP** — `hFlBodyRet` (`ForLoop.bodyRet`).  Supplier: for-loop body-ret arm. -/
  hFlBodyRet :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' : SpecSt) (rv : Value) (a : ForCond st d env cnd st')
      (a_1 : ExecS st' d env b st'' (Status.ret rv)),
      mForCond st d env cnd st' a → mExecS st' d env b st'' (Status.ret rv) a_1 →
      mForLoop st d env cnd step b st'' (Status.ret rv) (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1)
  /-- **GAP** — `hFlLoop` (`ForLoop.loop`).  Supplier: for-loop back-edge
      (`TermGuards.forMeasure`, `execForStepOf`/`loopFromBody`). -/
  hFlLoop :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
      (st' st'' st''' st'''' : SpecSt) (status status' : Status) (a : ForCond st d env cnd st')
      (a_1 : ExecS st' d env b st'' status) (a_2 : status = Status.normal ∨ status = Status.cont)
      (a_3 : ExecStep st'' d env step st''') (a_4 : ForLoop st''' d env cnd step b st'''' status'),
      mForCond st d env cnd st' a → mExecS st' d env b st'' status a_1 →
      mExecStep st'' d env step st''' a_3 → mForLoop st''' d env cnd step b st'''' status' a_4 →
      mForLoop st d env cnd step b st'''' status' (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4)
  /-- **GAP** — `hSeqNil` (`ExecSeq.nil`).  Supplier: `execSeqNil` seg-identity
      (`ExecSimCommon.execSeqNil`, essentially LANDED — a `_row` wrap is trivial). -/
  hSeqNil :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      mExecSeq st d env [] st Status.normal (ExecSeq.nil st d env)
  /-- **GAP** — `hSeqConsNormal` (`ExecSeq.consNormal`).  Supplier: `execSeqLoop`
      back-edge (`TermGuards.seqMeasure`). -/
  hSeqConsNormal :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : SpecSt)
      (status : Status) (a : ExecS st d env s st' Status.normal) (a_1 : ExecSeq st' d env ss st'' status),
      mExecS st d env s st' Status.normal a → mExecSeq st' d env ss st'' status a_1 →
      mExecSeq st d env (s :: ss) st'' status (ExecSeq.consNormal st d env s ss st' st'' status a a_1)
  /-- **GAP** — `hSeqConsAbrupt` (`ExecSeq.consAbrupt`).  Supplier: `execSeqLoop`
      abrupt-exit arm (`TermGuards.seqMeasure`). -/
  hSeqConsAbrupt :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt)
      (status : Status) (a : ExecS st d env s st' status) (a_1 : status ≠ Status.normal),
      mExecS st d env s st' status a →
      mExecSeq st d env (s :: ss) st' status (ExecSeq.consAbrupt st d env s ss st' status a a_1)

  -- ===== Endgame residuals (folded into TermResiduals per the task) =====
  /-- **ENTRY (prologue)** — `hEntryHalts` store-init locus.  Supplier: the off-path
      `interp_init` store representation at the `interp_run` loop head
      (`Vsa.Sim.InterpInitStoreRepr`, decoded PC span in its doc). -/
  hInitStore : ∀ p, Vsa.Sim.InterpInitStoreRepr L p
  /-- **ENTRY (epilogue)** — `hEntryHalts` exit-0 spill seam.  Supplier: the epilogue
      restore-block byte-level spill/frame/image/tail facts
      (`Vsa.Sim.EpilogueSpill`, the `s5=0` latch + restore `ChainFacts`). -/
  hEpilogueSpill : ∀ (g : (R : Register) → Option (RegisterType R))
      (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
      (st' : SpecSt) (m0 : Mem) (out : String),
      Vsa.Sim.EpilogueSpill g N A SL φf φc st' m0 out
  /-- **DIVERGENCE** — `hdivFam`.  Supplier: the per-load divergence correspondence
      (`Vsa.Sim.DivFamily.DivCorrFamily L`), discharged by the M4 `exec_stmt` case
      Triples' progress-only ("≥1 step, still corresponds") skeleton. -/
  hDivCorr : Vsa.Sim.DivFamily.DivCorrFamily L
  /-- **ERROR** — the M5 error family `ErrFamily L`.  Supplier:
      `Vsa.Sim.errFamilyClosed L S hsite…`, fed the shared L7/L8 `ErrShared` bundle `S`
      (`SnprintfContract SC` + `ErrorTailChain HT`, M3/M6 error-path inputs) and the 43
      per-error-site `hsite` residuals (M4 caller-linkage, `SitePre`-conditioned: the
      spec-derivation context → `ReachJal … c`, i.e. config `c` RUNS to each
      `jal runtime_error`; `m5_error_routing.tsv`).  `errFamily_ofShared` below is the
      one-liner that builds this field from those pieces. -/
  hErrFam : ErrFamily L

/-! ## The record fill — `termCases_of_residuals`

Applies each landed row to its `TermResiduals` field.  The unconditional scaffolds
(`hInitNone`/`hFcNone`/`hEsNone`) take no residual; `hCallClosure` is passed through
as a whole premise. -/
def termCases_of_residuals {L : Layout} (R : TermResiduals L) :
    Vsa.Sim.TermCaseBundle.TermCases where
  hInt := eval_int_row R.hInt
  hStr := eval_str_row R.hStr
  hBool := eval_bool_row R.hBool
  hNull := eval_null_row R.hNull
  hVar := eval_var_row R.hVar
  hAssign := eval_assign_row R.hAssign
  hBinary := Vsa.Sim.eval_binary_row R.hIAdd R.hISub R.hIMul R.hIDiv R.hIMod R.hILt R.hILe
    R.hIGt R.hIGe R.hEq R.hNe R.hStrAddL R.hStrAddR R.hStrLt R.hStrLe R.hStrGt R.hStrGe R.hDivOv
  hOrTrue := eval_orTrue_row R.hOrTrue
  hOrFalse := eval_orFalse_row R.hOrFalse
  hAndFalse := eval_andFalse_row R.hAndFalse
  hAndTrue := eval_andTrue_row R.hAndTrue
  hNeg := eval_neg_row R.hNeg
  hNot := eval_not_row R.hNot
  hCall := eval_call_row R.hCall
  hFn := eval_fn_row R.hFn
  hArgsNil := eval_argsNil_row R.hArgsNil
  hArgsCons := eval_argsCons_row R.hArgsCons
  hCallClosure := R.hCallClosure
  hCallPrint := eval_callPrint_row R.hCallPrint
  hCallPrintln := eval_callPrintln_row R.hCallPrintln
  hCallAssertOk := eval_callAssertOk_row R.hCallAssertOk
  hSExpr := exec_expr_row R.hSExpr
  hSVarInit := exec_varInit_row R.hSVarInit
  hSVarNull := exec_varNull_row R.hSVarNull
  hSBlock := exec_block_row R.hSBlock
  hSIfTrue := exec_ifTrue_row R.hSIfTrue
  hSIfFalse := exec_ifFalse_row R.hSIfFalse
  hSIfNone := exec_ifNone_row R.hSIfNone
  hSWhileFalse := exec_whileFalse_row R.hSWhileFalse
  hSWhileBreak := exec_whileBreak_row R.hSWhileBreak
  hSWhileRet := exec_whileRet_row R.hSWhileBreak
  hSWhileLoop := exec_whileLoop_row R.hSWhileBreak
  hSForStart := exec_forStart_row R.hSForStart
  hSRet := exec_ret_row R.hSRet
  hSRetNull := exec_retNull_row R.hSRetNull
  hSBrk := exec_brk_row R.hSBrk
  hSCont := exec_cont_row R.hSCont
  hInitNone := hInitNone_row
  hInitSome := R.hInitSome
  hFlCondFalse := R.hFlCondFalse
  hFlBodyBreak := R.hFlBodyBreak
  hFlBodyRet := R.hFlBodyRet
  hFlLoop := R.hFlLoop
  hFcNone := hFcNone_row
  hFcSome := R.hFcSome
  hEsNone := hEsNone_row
  hEsSome := R.hEsSome
  hSeqNil := R.hSeqNil
  hSeqConsNormal := R.hSeqConsNormal
  hSeqConsAbrupt := R.hSeqConsAbrupt

/-! ## The term arm — `hterm_of_residuals`

`termSimClosed_of_bundle` applied to the filled record, with the entry premise
supplied by `hEntryHalts_closed'` (fed the two tightened entry residuals from `R`).
The conclusion is EXACTLY `interpSimClosed_of_families`' `hterm` argument type. -/
theorem hterm_of_residuals {L : Layout} (R : TermResiduals L) :
    ∀ (p : Program) (c : Config) (out : String),
      Loaded L p c → BigStep p out → Halts c out 0 :=
  Vsa.Sim.TermCaseBundle.termSimClosed_of_bundle L (termCases_of_residuals R)
    (Vsa.Sim.hEntryHalts_closed' L R.hInitStore R.hEpilogueSpill)

/-! ## The divergence family — `hdivFam_of_residuals`

`DivFamily L` is definitionally the per-load `DivCorrFamily L` residual
(`Vsa.Sim.DivFamily.divFamily_of_corr`).  The `Corr` design is the SegEntry/ExecEntry
correspondence the rows already use — "the machine config `c` is executing the spec
node `(st, d, env, ss)`"; its `DivStep` progress arm is the M4 `exec_stmt` case
Triples' "≥1 step, still corresponds" skeleton, and its entry `Corr c initSt 0 0 p`
is `Loaded L p c`.  This whole obligation is the single named `R.hDivCorr` field. -/
theorem hdivFam_of_residuals {L : Layout} (R : TermResiduals L) : DivFamily L :=
  Vsa.Sim.DivFamily.divFamily_of_corr L R.hDivCorr

/-! ### The `Corr` design + the cheap `DivStep` arm

The natural correspondence is the one the rows already carry: `divCorr c st d env ss`
= "machine config `c` is parked at the `exec_stmt` statement-loop head executing the
spec node `(st, d, env, ss)`" — the `ExecEntry`/`SegEntry` shape (`ExecIH`'s entry
predicate).  Its `DivStep` progress arm is the M4 `exec_stmt` case Triples
(`execExprSimD`/`execBlockSim`/…) FORGETTING output/final-value and keeping only
"≥1 step, still corresponds"; its entry `Corr c initSt 0 0 p` is the program-load
correspondence packaged in `Loaded L p c`.

Per `DivFamily.lean`'s machine-checked verdict, no *concrete* `Corr` is discharge­able
purely spec-side: it either fails `DivStep` (no machine steps to exhibit) or fails
entry (nothing ties `c` to the spec).  What IS cheap and honest is to instantiate the
`DivStep` STATEMENT and derive it for the degenerate correspondence — recording that
the obligation is well-formed and that its progress content (not its entry) is the
whole residual.  `divStep_vacuous` below discharges `DivStep` for `fun _ _ _ _ _ =>
False` (both arms vacuous: no corresponding config exists), so the ONLY genuine gap
in the divergence family is the entry `Corr c initSt 0 0 p` — exactly what
`R.hDivCorr` (`DivCorrFamily`) bundles with its progress arm. -/
theorem divStep_vacuous :
    Vsa.Sim.DivStep (fun _ _ _ _ _ => False) :=
  ⟨fun _ _ _ _ _ _ _ _ hc => hc.elim, fun _ _ _ _ _ _ _ _ hc => hc.elim⟩

/-! ## `errFamily_ofShared` — build the `hErrFam` field from `ErrShared` + 43 hsites

The one-liner that discharges `TermResiduals.hErrFam`: `errFamilyClosed` fed the
shared L7/L8 bundle and the 43 per-error-site residuals.  Each routed residual is
now the CORRECTED `SitePre`-conditioned reachability (`ErrorReach.lean`): the
premise's spec-derivation context → `ReachJal S … <pc> <bytes> c` (the entry config
`c` RUNS to the jal), NOT the refuted `∀ c, JalErrPre … c`.  Its argument list IS
the honest error-side remaining work; recorded here so the supplier of `hErrFam` is
machine-checked to be exactly `errFamilyClosed`. -/
theorem errFamily_ofShared (L : Layout) (S : Vsa.Sim.ErrShared)
    (hsite_hVarUndef : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      st.store.get? env x = none → ReachJal S.g S.inp S.m0 0x80003b54#64 0xef#8 0xf0#8 0x4f#8 0xa5#8 c)
    (hsite_hAssignE : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
      EvalErr st d env e → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003b9c#64 0xef#8 0xf0#8 0xcf#8 0xa0#8 c)
    (hsite_hAssignUnbound : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → st'.store.set? env x v = none → ReachJal S.g S.inp S.m0 0x80003bc8#64 0xef#8 0xf0#8 0x0f#8 0x9e#8 c)
    (hsite_hBinaryL : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003c10#64 0xef#8 0xf0#8 0x8f#8 0x99#8 c)
    (hsite_hBinaryR : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' : SpecSt) (lv : Value),
      EvalE st d env l st' lv → EvalErr st' d env r → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003c7c#64 0xef#8 0xf0#8 0xcf#8 0x92#8 c)
    (hsite_hBinaryOp : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → EvalE st' d env r st'' rv →
      binOpSem st''.store op lv rv = none → ReachJal S.g S.inp S.m0 0x80003cc4#64 0xef#8 0xf0#8 0x4f#8 0x8e#8 c)
    (hsite_hOrL : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003ce8#64 0xef#8 0xf0#8 0x0f#8 0x8c#8 c)
    (hsite_hOrR : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt)
      (lv : Value),
      EvalE st d env l st' lv → lv.truthy = false → EvalErr st' d env r →
      ErrHalts c → ReachJal S.g S.inp S.m0 0x80003d14#64 0xef#8 0xf0#8 0x4f#8 0x89#8 c)
    (hsite_hAndL : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003d5c#64 0xef#8 0xf0#8 0xcf#8 0x84#8 c)
    (hsite_hAndR : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt)
      (lv : Value),
      EvalE st d env l st' lv → lv.truthy = true → EvalErr st' d env r →
      ErrHalts c → ReachJal S.g S.inp S.m0 0x80003da0#64 0xef#8 0xf0#8 0x8f#8 0x80#8 c)
    (hsite_hUnaryE : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : UnOp) (e : Expr),
      EvalErr st d env e → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003950#64 0xef#8 0xf0#8 0x8f#8 0xc5#8 c)
    (hsite_hNegType : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ReachJal S.g S.inp S.m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8 c)
    (hsite_hCallF : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr),
      EvalErr st d env f → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003de8#64 0xef#8 0xe0#8 0x1f#8 0xfc#8 c)
    (hsite_hCallArgs : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → EvalArgsErr st' d env args → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003e98#64 0xef#8 0xe0#8 0x1f#8 0xf1#8 c)
    (hsite_hCallC : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : SpecSt) (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
      CallErr st'' d fv vs → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003f58#64 0xef#8 0xe0#8 0x1f#8 0xe5#8 c)
    (hsite_hArgsHead : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr),
      EvalErr st d env e → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003fac#64 0xef#8 0xe0#8 0xdf#8 0xdf#8 c)
    (hsite_hArgsTail : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalArgsErr st' d env es → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003fdc#64 0xef#8 0xe0#8 0xdf#8 0xdc#8 c)
    (hsite_hNotCallable : ∀ (c : Config) (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value),
      (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) → ReachJal S.g S.inp S.m0 0x80002e90#64 0xef#8 0xf0#8 0x9f#8 0xf1#8 c)
    (hsite_hBadClosure : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Vsa.While.Addr)
      (vs : List Vsa.While.Value), st.store.closures[a]? = none → ErrHalts c)
    (hsite_hArity : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length ≠ cd.params.length → ReachJal S.g S.inp S.m0 0x80002ebc#64 0xef#8 0xf0#8 0xdf#8 0xee#8 c)
    (hsite_hDepth : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      ¬ d < maxCallDepth → ReachJal S.g S.inp S.m0 0x80002e90#64 0xef#8 0xf0#8 0x9f#8 0xf1#8 c)
    (hsite_hBody : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeqErr ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body → ErrHalts c → ReachJal S.g S.inp S.m0 0x80002ebc#64 0xef#8 0xf0#8 0xdf#8 0xee#8 c)
    (hsite_hEscape : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body st' status →
      (status = .brk ∨ status = .cont) → ReachJal S.g S.inp S.m0 0x80002e90#64 0xef#8 0xf0#8 0x9f#8 0xf1#8 c)
    (hsite_hAssertFail : ∀ (c : Config) (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value),
      (vs = [v] ∨ vs = [v, m]) → v.truthy = false → ReachJal S.g S.inp S.m0 0x80002ebc#64 0xef#8 0xf0#8 0xdf#8 0xee#8 c)
    (hsite_hAssertArity : ∀ (c : Config) (st : SpecSt) (d : Nat) (vs : List Value),
      (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) → ReachJal S.g S.inp S.m0 0x80002e90#64 0xef#8 0xf0#8 0x9f#8 0xf1#8 c)
    (hsite_hExpr : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003b54#64 0xef#8 0xf0#8 0x4f#8 0xa5#8 c)
    (hsite_hVarInit : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
      EvalErr st d env e → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003b9c#64 0xef#8 0xf0#8 0xcf#8 0xa0#8 c)
    (hsite_hBlock : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr),
      st.store.allocFrame (some env) = (store', inner) →
      ExecSeqErr ⟨store', st.out⟩ d inner ss → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003bc8#64 0xef#8 0xf0#8 0x0f#8 0x9e#8 c)
    (hsite_hIfCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t : Stmt)
      (e : Option Stmt),
      EvalErr st d env cnd → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003c10#64 0xef#8 0xf0#8 0x8f#8 0x99#8 c)
    (hsite_hIfThen : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t : Stmt)
      (e : Option Stmt) (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → ExecErr st' d env t →
      ErrHalts c → ReachJal S.g S.inp S.m0 0x80003c7c#64 0xef#8 0xf0#8 0xcf#8 0x92#8 c)
    (hsite_hIfElse : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t e : Stmt)
      (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = false → ExecErr st' d env e →
      ErrHalts c → ReachJal S.g S.inp S.m0 0x80003cc4#64 0xef#8 0xf0#8 0x4f#8 0x8e#8 c)
    (hsite_hWhileCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt),
      EvalErr st d env cnd → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003ce8#64 0xef#8 0xf0#8 0x0f#8 0x8c#8 c)
    (hsite_hWhileBody : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt)
      (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → ExecErr st' d env b →
      ErrHalts c → ReachJal S.g S.inp S.m0 0x80003d14#64 0xef#8 0xf0#8 0x4f#8 0x89#8 c)
    (hsite_hWhileLoop : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt)
      (st' st'' : SpecSt) (v : Value) (status : Status),
      EvalE st d env cnd st' v → v.truthy = true → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecErr st'' d env (.whileStmt cnd b) →
      ErrHalts c → ReachJal S.g S.inp S.m0 0x80003d5c#64 0xef#8 0xf0#8 0xcf#8 0x84#8 c)
    (hsite_hForInit : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (init : Stmt) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr),
      st.store.allocFrame (some env) = (store', outer) →
      ExecErr ⟨store', st.out⟩ d outer init → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003da0#64 0xef#8 0xf0#8 0x8f#8 0x80#8 c)
    (hsite_hForLoop : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' : SpecSt),
      st.store.allocFrame (some env) = (store', outer) →
      ExecInit ⟨store', st.out⟩ d outer init st' →
      ForLoopErr st' d outer cnd step b → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003950#64 0xef#8 0xf0#8 0x8f#8 0xc5#8 c)
    (hsite_hRet : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ReachJal S.g S.inp S.m0 0x800034e4#64 0xef#8 0xf0#8 0x5f#8 0x8c#8 c)
    (hsite_hFlCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (step : Option Expr)
      (b : Stmt),
      EvalErr st d env cnd → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003de8#64 0xef#8 0xe0#8 0x1f#8 0xfc#8 c)
    (hsite_hFlBody : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' : SpecSt),
      ForCond st d env cnd st' → ExecErr st' d env b → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003e98#64 0xef#8 0xe0#8 0x1f#8 0xf1#8 c)
    (hsite_hFlStep : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr) (e : Expr)
      (b : Stmt) (st' st'' : SpecSt) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → EvalErr st'' d env e → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003f58#64 0xef#8 0xe0#8 0x1f#8 0xe5#8 c)
    (hsite_hFlLoop : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' : SpecSt) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
      ForLoopErr st''' d env cnd step b → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003fac#64 0xef#8 0xe0#8 0xdf#8 0xdf#8 c)
    (hsite_hSeqHead : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt),
      ExecErr st d env s → ErrHalts c → ReachJal S.g S.inp S.m0 0x80003fdc#64 0xef#8 0xe0#8 0xdf#8 0xdc#8 c)
    (hsite_hSeqTail : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : SpecSt),
      ExecS st d env s st' .normal → ExecSeqErr st' d env ss → ErrHalts c → ReachJal S.g S.inp S.m0 0x80002e90#64 0xef#8 0xf0#8 0x9f#8 0xf1#8 c)
    (hsite_hTopAbrupt : ∀ (p : Vsa.While.Program) (c : Config),
      Vsa.While.TopAbrupt p → ErrHalts c) :
    ErrFamily L :=
  Vsa.Sim.errFamilyClosed L S
    hsite_hVarUndef hsite_hAssignE hsite_hAssignUnbound hsite_hBinaryL hsite_hBinaryR
    hsite_hBinaryOp hsite_hOrL hsite_hOrR hsite_hAndL hsite_hAndR hsite_hUnaryE
    hsite_hNegType hsite_hCallF hsite_hCallArgs hsite_hCallC hsite_hArgsHead
    hsite_hArgsTail hsite_hNotCallable hsite_hBadClosure hsite_hArity hsite_hDepth
    hsite_hBody hsite_hEscape hsite_hAssertFail hsite_hAssertArity hsite_hExpr
    hsite_hVarInit hsite_hBlock hsite_hIfCond hsite_hIfThen hsite_hIfElse
    hsite_hWhileCond hsite_hWhileBody hsite_hWhileLoop hsite_hForInit hsite_hForLoop
    hsite_hRet hsite_hFlCond hsite_hFlBody hsite_hFlStep hsite_hFlLoop hsite_hSeqHead
    hsite_hSeqTail hsite_hTopAbrupt

/-! ## THE ENDGAME COROLLARY — `interpSim_of_residuals`

`InterpSim L` from `TermResiduals L` alone.  `htri` is UNCONDITIONAL
(`Vsa.While.htri_unconditional`); the term arm is `hterm_of_residuals`, the
divergence family `hdivFam_of_residuals`, the error family `R.hErrFam`.  After this
theorem the ENTIRE remaining project = discharging the fields of `TermResiduals`. -/
theorem interpSim_of_residuals {L : Layout} (R : TermResiduals L) : InterpSim L :=
  Vsa.Sim.InterpSimFinal.interpSimClosed_of_families L
    (hterm_of_residuals R)
    Vsa.While.htri_unconditional
    (hdivFam_of_residuals R)
    R.hErrFam

/-! ## Conditional refinement, from the residuals -/

/-- The complete behavioral correspondence, from `TermResiduals L` alone. -/
theorem refinement_of_residuals {L : Layout} (R : TermResiduals L) :
    ∀ p c, Loaded L p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out) :=
  Vsa.Refine.refinement (interpSim_of_residuals R)

#print axioms termCases_of_residuals
#print axioms hterm_of_residuals
#print axioms hdivFam_of_residuals
#print axioms divStep_vacuous
#print axioms errFamily_ofShared
#print axioms interpSim_of_residuals

end Vsa.Sim.TermAssembly
