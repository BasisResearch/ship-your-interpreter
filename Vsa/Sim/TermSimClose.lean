import Vsa.Sim.TermSimAssembly
import Vsa.Refinement

/-!
# Layer 7 — the CLOSE skeleton (term side): `termSimClosed`

`TermSimAssembly.term_sim_of_cases` is the nine-motive `@EvalE.rec` assembly:
given the ~50 per-constructor case Triples (the M4 residual bundle), it concludes
`mEvalE … t = EvalIH …` for an arbitrary `EvalE` derivation. This file closes the
**statement (`ExecSeq`) root** — the shape `InterpSim.term_sim` actually needs —
and bridges the resulting per-node `ExecSeq` simulation Triple to the top-level
`BigStep p out → Halts c out 0` obligation.

## Two pieces

* **`execSeq_sim_of_cases`** — the exact same 50 minor premises, but driving
  `@ExecSeq.rec` to conclude `mExecSeq … t` (the ninth motive) for an arbitrary
  `ExecSeq` derivation. Because `EvalE`/`ExecS`/`ExecSeq` are one mutual block,
  the nine motives and 50 premises are literally the same as
  `term_sim_of_cases`; only the final index/derivation and the exposed motive
  differ. This is the `ExecSeq`-rooted twin of `term_sim_of_cases`.

* **`termSimClosed`** — from (a) the 50 minor premises [the aggregated **M4
  residual bundle** — each discharged, conditionally on its own named residuals,
  by the correspondingly-named landed case lemma: `evalIntSim`…`evalFnSim`,
  `execExprSim`…`execContSim`, `execSeqNil`/`execSeqLoop`, `evalArgsNil`/
  `evalArgsCons`, `callAssertOk`/`callPrint`/`callPrintln`, and the open
  `hCallClosure`/loop-scaffold premises] and (b) ONE named **entry bridge**
  `hEntryHalts` [the M6 program-entry residual: the per-node `mExecSeq`
  simulation Triple for the whole program `p`, at the `interp_run` entry
  configuration determined by `Loaded L p c`, transported to a clean
  `Halts c out 0`], concludes exactly `InterpSim.term_sim`.

The entry bridge `hEntryHalts` is precisely the residual-unification /
program-entry-plumbing gap flagged in `TermSimAssembly`'s module doc ("`term_sim`
follows by instantiating … at the whole-program entry … once the
residual-unification interface (M6) closes"). Here it is pinned as a single
explicit hypothesis rather than left implicit.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.TermSimClose

open Vsa.While
open Vsa.Machine (Config Halts)
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The `ExecSeq`-rooted assembly — `execSeq_sim_of_cases`

Identical hypotheses to `term_sim_of_cases`; `@ExecSeq.rec` exposes the ninth
motive `mExecSeq` at an arbitrary `ExecSeq` node. -/

theorem execSeq_sim_of_cases
    (hInt :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (n : Int), mEvalE st d env (Expr.int n) st (Value.int n) (EvalE.int st d env n))
    (hStr :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : String), mEvalE st d env (Expr.str s) st (Value.str s) (EvalE.str st d env s))
    (hBool :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (b : Bool), mEvalE st d env (Expr.bool b) st (Value.bool b) (EvalE.bool st d env b))
    (hNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mEvalE st d env Expr.null st Value.null (EvalE.null st d env))
    (hVar :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value) (a : st.store.get? env x = some v), mEvalE st d env (Expr.var x) st v (EvalE.var st d env x v a))
    (hAssign :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value) (store'' : Store) (a : EvalE st d env e st' v) (a_1 : st'.store.set? env x v = some store''), mEvalE st d env e st' v a → mEvalE st d env (Expr.assign x e) { store := store'', out := st'.out } v (EvalE.assign st d env x e st' v store'' a a_1))
    (hBinary :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : SpecSt) (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv) (a_2 : binOpSem st''.store op lv rv = some v), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_1 → mEvalE st d env (Expr.binary op l r) st'' v (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2))
    (hOrTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true), mEvalE st d env l st' lv a → mEvalE st d env (Expr.logical LogOp.or l r) st' (Value.bool true) (EvalE.orTrue st d env l r st' lv a a_1))
    (hOrFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false) (a_2 : EvalE st' d env r st'' rv), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_2 → mEvalE st d env (Expr.logical LogOp.or l r) st'' (Value.bool rv.truthy) (EvalE.orFalse st d env l r st' st'' lv rv a a_1 a_2))
    (hAndFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false), mEvalE st d env l st' lv a → mEvalE st d env (Expr.logical LogOp.and l r) st' (Value.bool false) (EvalE.andFalse st d env l r st' lv a a_1))
    (hAndTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true) (a_2 : EvalE st' d env r st'' rv), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_2 → mEvalE st d env (Expr.logical LogOp.and l r) st'' (Value.bool rv.truthy) (EvalE.andTrue st d env l r st' st'' lv rv a a_1 a_2))
    (hNeg :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int) (a : EvalE st d env e st' (Value.int n)), mEvalE st d env e st' (Value.int n) a → mEvalE st d env (Expr.unary UnOp.neg e) st' (Value.int (wrap64 (-n))) (EvalE.neg st d env e st' n a))
    (hNot :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mEvalE st d env (Expr.unary UnOp.not e) st' (Value.bool !v.truthy) (EvalE.not st d env e st' v a))
    (hCall :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr) (st' st'' st''' : SpecSt) (fv : Value) (vs : List Value) (v : Value) (a : EvalE st d env f st' fv) (a_1 : EvalArgs st' d env args st'' vs) (a_2 : Call st'' d fv vs st''' v), mEvalE st d env f st' fv a → mEvalArgs st' d env args st'' vs a_1 → mCall st'' d fv vs st''' v a_2 → mEvalE st d env (f.call args) st''' v (EvalE.call st d env f args st' st'' st''' fv vs v a a_1 a_2))
    (hFn :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (name : Option String) (params : List String) (body : List Stmt) (store' : Store) (a : Addr) (a_1 : st.store.allocClosure { env := env, name := name, params := params, body := body } = (store', a)), mEvalE st d env (Expr.fn name params body) { store := store', out := st.out } (Value.closure a) (EvalE.fn st d env name params body store' a a_1))
    (hArgsNil :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mEvalArgs st d env [] st [] (EvalArgs.nil st d env))
    (hArgsCons :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr) (st' st'' : SpecSt) (v : Value) (vs : List Value) (a : EvalE st d env e st' v) (a_1 : EvalArgs st' d env es st'' vs), mEvalE st d env e st' v a → mEvalArgs st' d env es st'' vs a_1 → mEvalArgs st d env (e :: es) st'' (v :: vs) (EvalArgs.cons st d env e es st' st'' v vs a a_1))
    (hCallClosure :
      ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status) (v : Value) (a_1 : st.store.closures[a]? = some cd) (a_2 : vs.length = cd.params.length) (a_3 : d < maxCallDepth) (a_4 : st.store.allocFrame (some cd.env) = (store', frame)) (a_5 : ExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status) (a_6 : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v), mExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status a_5 → mCall st d (Value.closure a) vs st' v (Call.closure st d a cd vs store' frame st' status v a_1 a_2 a_3 a_4 a_5 a_6))
    (hCallPrint :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value), mCall st d (Value.native NativeFn.print) vs { store := st.store, out := st.out +++ printArgs st.store vs } Value.null (Call.print st d vs))
    (hCallPrintln :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value), mCall st d (Value.native NativeFn.println) vs { store := st.store, out := st.out +++ printArgs st.store vs +++ "\n" } Value.null (Call.println st d vs))
    (hCallAssertOk :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value) (a : vs = [v] ∨ vs = [v, m]) (a_1 : v.truthy = true), mCall st d (Value.native NativeFn.assert) vs st Value.null (Call.assertOk st d vs v m a a_1))
    (hSExpr :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.expr e) st' Status.normal (ExecS.expr st d env e st' v a))
    (hSVarInit :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.varDecl x (some e)) { store := st'.store.define env x v, out := st'.out } Status.normal (ExecS.varInit st d env x e st' v a))
    (hSVarNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String), mExecS st d env (Stmt.varDecl x none) { store := st.store.define env x Value.null, out := st.out } Status.normal (ExecS.varNull st d env x))
    (hSBlock :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store) (inner : Addr) (st' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', inner)) (a_1 : ExecSeq { store := store', out := st.out } d inner ss st' status), mExecSeq { store := store', out := st.out } d inner ss st' status a_1 → mExecS st d env (Stmt.block ss) st' status (ExecS.block st d env ss store' inner st' status a a_1))
    (hSIfTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (e : Option Stmt) (st' st'' : SpecSt) (v : Value) (status : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env t st'' status), mEvalE st d env c st' v a → mExecS st' d env t st'' status a_2 → mExecS st d env (Stmt.ifStmt c t e) st'' status (ExecS.ifTrue st d env c t e st' st'' v status a a_1 a_2))
    (hSIfFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt) (st' st'' : SpecSt) (v : Value) (status : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = false) (a_2 : ExecS st' d env e st'' status), mEvalE st d env c st' v a → mExecS st' d env e st'' status a_2 → mExecS st d env (Stmt.ifStmt c t (some e)) st'' status (ExecS.ifFalse st d env c t e st' st'' v status a a_1 a_2))
    (hSIfNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mExecS st d env (Stmt.ifStmt c t none) st' Status.normal (ExecS.ifNone st d env c t st' v a a_1))
    (hSWhileFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mExecS st d env (Stmt.whileStmt c b) st' Status.normal (ExecS.whileFalse st d env c b st' v a a_1))
    (hSWhileBreak :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' Status.brk), mEvalE st d env c st' v a → mExecS st' d env b st'' Status.brk a_2 → mExecS st d env (Stmt.whileStmt c b) st'' Status.normal (ExecS.whileBreak st d env c b st' st'' v a a_1 a_2))
    (hSWhileRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v rv : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' (Status.ret rv)), mEvalE st d env c st' v a → mExecS st' d env b st'' (Status.ret rv) a_2 → mExecS st d env (Stmt.whileStmt c b) st'' (Status.ret rv) (ExecS.whileRet st d env c b st' st'' v rv a a_1 a_2))
    (hSWhileLoop :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' st''' : SpecSt) (v : Value) (status status' : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' status) (a_3 : status = Status.normal ∨ status = Status.cont) (a_4 : ExecS st'' d env (Stmt.whileStmt c b) st''' status'), mEvalE st d env c st' v a → mExecS st' d env b st'' status a_2 → mExecS st'' d env (Stmt.whileStmt c b) st''' status' a_4 → mExecS st d env (Stmt.whileStmt c b) st''' status' (ExecS.whileLoop st d env c b st' st'' st''' v status status' a a_1 a_2 a_3 a_4))
    (hSForStart :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr) (st' st'' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', outer)) (a_1 : ExecInit { store := store', out := st.out } d outer init st') (a_2 : ForLoop st' d outer cnd step b st'' status), mExecInit { store := store', out := st.out } d outer init st' a_1 → mForLoop st' d outer cnd step b st'' status a_2 → mExecS st d env (Stmt.forStmt init cnd step b) st'' status (ExecS.forStart st d env init cnd step b store' outer st' st'' status a a_1 a_2))
    (hSRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.ret (some e)) st' (Status.ret v) (ExecS.ret st d env e st' v a))
    (hSRetNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env (Stmt.ret none) st (Status.ret Value.null) (ExecS.retNull st d env))
    (hSBrk :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env Stmt.brk st Status.brk (ExecS.brk st d env))
    (hSCont :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env Stmt.cont st Status.cont (ExecS.cont st d env))
    (hInitNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecInit st d env none st (ExecInit.none st d env))
    (hInitSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (st' : SpecSt) (a : ExecS st d env s st' Status.normal), mExecS st d env s st' Status.normal a → mExecInit st d env (some s) st' (ExecInit.some st d env s st' a))
    (hFlCondFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mForLoop st d env (some c) step b st' Status.normal (ForLoop.condFalse st d env c step b st' v a a_1))
    (hFlBodyBreak :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : SpecSt) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' Status.brk), mForCond st d env cnd st' a → mExecS st' d env b st'' Status.brk a_1 → mForLoop st d env cnd step b st'' Status.normal (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1))
    (hFlBodyRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : SpecSt) (rv : Value) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' (Status.ret rv)), mForCond st d env cnd st' a → mExecS st' d env b st'' (Status.ret rv) a_1 → mForLoop st d env cnd step b st'' (Status.ret rv) (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1))
    (hFlLoop :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : SpecSt) (status status' : Status) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' status) (a_2 : status = Status.normal ∨ status = Status.cont) (a_3 : ExecStep st'' d env step st''') (a_4 : ForLoop st''' d env cnd step b st'''' status'), mForCond st d env cnd st' a → mExecS st' d env b st'' status a_1 → mExecStep st'' d env step st''' a_3 → mForLoop st''' d env cnd step b st'''' status' a_4 → mForLoop st d env cnd step b st'''' status' (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4))
    (hFcNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mForCond st d env none st (ForCond.none st d env))
    (hFcSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true), mEvalE st d env c st' v a → mForCond st d env (some c) st' (ForCond.some st d env c st' v a a_1))
    (hEsNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecStep st d env none st (ExecStep.none st d env))
    (hEsSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecStep st d env (some e) st' (ExecStep.some st d env e st' v a))
    (hSeqNil :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecSeq st d env [] st Status.normal (ExecSeq.nil st d env))
    (hSeqConsNormal :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : SpecSt) (status : Status) (a : ExecS st d env s st' Status.normal) (a_1 : ExecSeq st' d env ss st'' status), mExecS st d env s st' Status.normal a → mExecSeq st' d env ss st'' status a_1 → mExecSeq st d env (s :: ss) st'' status (ExecSeq.consNormal st d env s ss st' st'' status a a_1))
    (hSeqConsAbrupt :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt) (status : Status) (a : ExecS st d env s st' status) (a_1 : status ≠ Status.normal), mExecS st d env s st' status a → mExecSeq st d env (s :: ss) st' status (ExecSeq.consAbrupt st d env s ss st' status a a_1))
    {st : SpecSt} {d : Nat} {env : Addr} {ss : List Stmt} {st' : SpecSt}
    {status : Status}
    (t : ExecSeq st d env ss st' status) : mExecSeq st d env ss st' status t :=
  @ExecSeq.rec mEvalE mEvalArgs mCall mExecS mExecInit mForLoop mForCond mExecStep
    mExecSeq
    hInt hStr hBool hNull hVar hAssign hBinary hOrTrue hOrFalse hAndFalse hAndTrue hNeg
    hNot hCall hFn hArgsNil hArgsCons hCallClosure hCallPrint hCallPrintln hCallAssertOk
    hSExpr hSVarInit hSVarNull hSBlock hSIfTrue hSIfFalse hSIfNone hSWhileFalse
    hSWhileBreak hSWhileRet hSWhileLoop hSForStart hSRet hSRetNull hSBrk hSCont hInitNone
    hInitSome hFlCondFalse hFlBodyBreak hFlBodyRet hFlLoop hFcNone hFcSome hEsNone hEsSome
    hSeqNil hSeqConsNormal hSeqConsAbrupt
    st d env ss st' status t

/-! ## §2. `termSimClosed` — bridging the `ExecSeq` root to `Halts`

From the 50-premise M4 residual bundle (via `execSeq_sim_of_cases`) and ONE
named program-entry bridge, we obtain exactly `InterpSim.term_sim`.

The bridge `hEntryHalts` is the M6 program-entry residual: it consumes the
whole-program per-node `ExecSeq` simulation datum
`mExecSeq initSt 0 0 p st' .normal t` (the `SegEntry → SegExit` Triple for the
program body, produced from the bundle) together with `Loaded L p c` and
`st'.out = out`, and lands the clean `Halts c out 0`. It is the sole residue of
program-entry plumbing (`interp_run` prologue → statement loop → clean exit +
the layout/`Loaded` ↔ `SegEntry` unification). -/

theorem termSimClosed (L : Layout)
    (hInt :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (n : Int), mEvalE st d env (Expr.int n) st (Value.int n) (EvalE.int st d env n))
    (hStr :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : String), mEvalE st d env (Expr.str s) st (Value.str s) (EvalE.str st d env s))
    (hBool :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (b : Bool), mEvalE st d env (Expr.bool b) st (Value.bool b) (EvalE.bool st d env b))
    (hNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mEvalE st d env Expr.null st Value.null (EvalE.null st d env))
    (hVar :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (v : Value) (a : st.store.get? env x = some v), mEvalE st d env (Expr.var x) st v (EvalE.var st d env x v a))
    (hAssign :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value) (store'' : Store) (a : EvalE st d env e st' v) (a_1 : st'.store.set? env x v = some store''), mEvalE st d env e st' v a → mEvalE st d env (Expr.assign x e) { store := store'', out := st'.out } v (EvalE.assign st d env x e st' v store'' a a_1))
    (hBinary :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) (st' st'' : SpecSt) (lv rv v : Value) (a : EvalE st d env l st' lv) (a_1 : EvalE st' d env r st'' rv) (a_2 : binOpSem st''.store op lv rv = some v), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_1 → mEvalE st d env (Expr.binary op l r) st'' v (EvalE.binary st d env op l r st' st'' lv rv v a a_1 a_2))
    (hOrTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true), mEvalE st d env l st' lv a → mEvalE st d env (Expr.logical LogOp.or l r) st' (Value.bool true) (EvalE.orTrue st d env l r st' lv a a_1))
    (hOrFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false) (a_2 : EvalE st' d env r st'' rv), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_2 → mEvalE st d env (Expr.logical LogOp.or l r) st'' (Value.bool rv.truthy) (EvalE.orFalse st d env l r st' st'' lv rv a a_1 a_2))
    (hAndFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt) (lv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = false), mEvalE st d env l st' lv a → mEvalE st d env (Expr.logical LogOp.and l r) st' (Value.bool false) (EvalE.andFalse st d env l r st' lv a a_1))
    (hAndTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : SpecSt) (lv rv : Value) (a : EvalE st d env l st' lv) (a_1 : lv.truthy = true) (a_2 : EvalE st' d env r st'' rv), mEvalE st d env l st' lv a → mEvalE st' d env r st'' rv a_2 → mEvalE st d env (Expr.logical LogOp.and l r) st'' (Value.bool rv.truthy) (EvalE.andTrue st d env l r st' st'' lv rv a a_1 a_2))
    (hNeg :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (n : Int) (a : EvalE st d env e st' (Value.int n)), mEvalE st d env e st' (Value.int n) a → mEvalE st d env (Expr.unary UnOp.neg e) st' (Value.int (wrap64 (-n))) (EvalE.neg st d env e st' n a))
    (hNot :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mEvalE st d env (Expr.unary UnOp.not e) st' (Value.bool !v.truthy) (EvalE.not st d env e st' v a))
    (hCall :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr) (st' st'' st''' : SpecSt) (fv : Value) (vs : List Value) (v : Value) (a : EvalE st d env f st' fv) (a_1 : EvalArgs st' d env args st'' vs) (a_2 : Call st'' d fv vs st''' v), mEvalE st d env f st' fv a → mEvalArgs st' d env args st'' vs a_1 → mCall st'' d fv vs st''' v a_2 → mEvalE st d env (f.call args) st''' v (EvalE.call st d env f args st' st'' st''' fv vs v a a_1 a_2))
    (hFn :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (name : Option String) (params : List String) (body : List Stmt) (store' : Store) (a : Addr) (a_1 : st.store.allocClosure { env := env, name := name, params := params, body := body } = (store', a)), mEvalE st d env (Expr.fn name params body) { store := store', out := st.out } (Value.closure a) (EvalE.fn st d env name params body store' a a_1))
    (hArgsNil :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mEvalArgs st d env [] st [] (EvalArgs.nil st d env))
    (hArgsCons :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr) (st' st'' : SpecSt) (v : Value) (vs : List Value) (a : EvalE st d env e st' v) (a_1 : EvalArgs st' d env es st'' vs), mEvalE st d env e st' v a → mEvalArgs st' d env es st'' vs a_1 → mEvalArgs st d env (e :: es) st'' (v :: vs) (EvalArgs.cons st d env e es st' st'' v vs a a_1))
    (hCallClosure :
      ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status) (v : Value) (a_1 : st.store.closures[a]? = some cd) (a_2 : vs.length = cd.params.length) (a_3 : d < maxCallDepth) (a_4 : st.store.allocFrame (some cd.env) = (store', frame)) (a_5 : ExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status) (a_6 : status = Status.normal ∧ v = Value.null ∨ status = Status.ret v), mExecSeq { store := List.foldl (fun s x => match x with | (x, v) => s.define frame x v) store' (cd.params.zip vs), out := st.out } (d + 1) frame cd.body st' status a_5 → mCall st d (Value.closure a) vs st' v (Call.closure st d a cd vs store' frame st' status v a_1 a_2 a_3 a_4 a_5 a_6))
    (hCallPrint :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value), mCall st d (Value.native NativeFn.print) vs { store := st.store, out := st.out +++ printArgs st.store vs } Value.null (Call.print st d vs))
    (hCallPrintln :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value), mCall st d (Value.native NativeFn.println) vs { store := st.store, out := st.out +++ printArgs st.store vs +++ "\n" } Value.null (Call.println st d vs))
    (hCallAssertOk :
      ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value) (a : vs = [v] ∨ vs = [v, m]) (a_1 : v.truthy = true), mCall st d (Value.native NativeFn.assert) vs st Value.null (Call.assertOk st d vs v m a a_1))
    (hSExpr :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.expr e) st' Status.normal (ExecS.expr st d env e st' v a))
    (hSVarInit :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.varDecl x (some e)) { store := st'.store.define env x v, out := st'.out } Status.normal (ExecS.varInit st d env x e st' v a))
    (hSVarNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String), mExecS st d env (Stmt.varDecl x none) { store := st.store.define env x Value.null, out := st.out } Status.normal (ExecS.varNull st d env x))
    (hSBlock :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store) (inner : Addr) (st' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', inner)) (a_1 : ExecSeq { store := store', out := st.out } d inner ss st' status), mExecSeq { store := store', out := st.out } d inner ss st' status a_1 → mExecS st d env (Stmt.block ss) st' status (ExecS.block st d env ss store' inner st' status a a_1))
    (hSIfTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (e : Option Stmt) (st' st'' : SpecSt) (v : Value) (status : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env t st'' status), mEvalE st d env c st' v a → mExecS st' d env t st'' status a_2 → mExecS st d env (Stmt.ifStmt c t e) st'' status (ExecS.ifTrue st d env c t e st' st'' v status a a_1 a_2))
    (hSIfFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt) (st' st'' : SpecSt) (v : Value) (status : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = false) (a_2 : ExecS st' d env e st'' status), mEvalE st d env c st' v a → mExecS st' d env e st'' status a_2 → mExecS st d env (Stmt.ifStmt c t (some e)) st'' status (ExecS.ifFalse st d env c t e st' st'' v status a a_1 a_2))
    (hSIfNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mExecS st d env (Stmt.ifStmt c t none) st' Status.normal (ExecS.ifNone st d env c t st' v a a_1))
    (hSWhileFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mExecS st d env (Stmt.whileStmt c b) st' Status.normal (ExecS.whileFalse st d env c b st' v a a_1))
    (hSWhileBreak :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' Status.brk), mEvalE st d env c st' v a → mExecS st' d env b st'' Status.brk a_2 → mExecS st d env (Stmt.whileStmt c b) st'' Status.normal (ExecS.whileBreak st d env c b st' st'' v a a_1 a_2))
    (hSWhileRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v rv : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' (Status.ret rv)), mEvalE st d env c st' v a → mExecS st' d env b st'' (Status.ret rv) a_2 → mExecS st d env (Stmt.whileStmt c b) st'' (Status.ret rv) (ExecS.whileRet st d env c b st' st'' v rv a a_1 a_2))
    (hSWhileLoop :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' st''' : SpecSt) (v : Value) (status status' : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' status) (a_3 : status = Status.normal ∨ status = Status.cont) (a_4 : ExecS st'' d env (Stmt.whileStmt c b) st''' status'), mEvalE st d env c st' v a → mExecS st' d env b st'' status a_2 → mExecS st'' d env (Stmt.whileStmt c b) st''' status' a_4 → mExecS st d env (Stmt.whileStmt c b) st''' status' (ExecS.whileLoop st d env c b st' st'' st''' v status status' a a_1 a_2 a_3 a_4))
    (hSForStart :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr) (st' st'' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', outer)) (a_1 : ExecInit { store := store', out := st.out } d outer init st') (a_2 : ForLoop st' d outer cnd step b st'' status), mExecInit { store := store', out := st.out } d outer init st' a_1 → mForLoop st' d outer cnd step b st'' status a_2 → mExecS st d env (Stmt.forStmt init cnd step b) st'' status (ExecS.forStart st d env init cnd step b store' outer st' st'' status a a_1 a_2))
    (hSRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecS st d env (Stmt.ret (some e)) st' (Status.ret v) (ExecS.ret st d env e st' v a))
    (hSRetNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env (Stmt.ret none) st (Status.ret Value.null) (ExecS.retNull st d env))
    (hSBrk :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env Stmt.brk st Status.brk (ExecS.brk st d env))
    (hSCont :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecS st d env Stmt.cont st Status.cont (ExecS.cont st d env))
    (hInitNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecInit st d env none st (ExecInit.none st d env))
    (hInitSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (st' : SpecSt) (a : ExecS st d env s st' Status.normal), mExecS st d env s st' Status.normal a → mExecInit st d env (some s) st' (ExecInit.some st d env s st' a))
    (hFlCondFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mForLoop st d env (some c) step b st' Status.normal (ForLoop.condFalse st d env c step b st' v a a_1))
    (hFlBodyBreak :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : SpecSt) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' Status.brk), mForCond st d env cnd st' a → mExecS st' d env b st'' Status.brk a_1 → mForLoop st d env cnd step b st'' Status.normal (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1))
    (hFlBodyRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : SpecSt) (rv : Value) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' (Status.ret rv)), mForCond st d env cnd st' a → mExecS st' d env b st'' (Status.ret rv) a_1 → mForLoop st d env cnd step b st'' (Status.ret rv) (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1))
    (hFlLoop :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : SpecSt) (status status' : Status) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' status) (a_2 : status = Status.normal ∨ status = Status.cont) (a_3 : ExecStep st'' d env step st''') (a_4 : ForLoop st''' d env cnd step b st'''' status'), mForCond st d env cnd st' a → mExecS st' d env b st'' status a_1 → mExecStep st'' d env step st''' a_3 → mForLoop st''' d env cnd step b st'''' status' a_4 → mForLoop st d env cnd step b st'''' status' (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4))
    (hFcNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mForCond st d env none st (ForCond.none st d env))
    (hFcSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true), mEvalE st d env c st' v a → mForCond st d env (some c) st' (ForCond.some st d env c st' v a a_1))
    (hEsNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecStep st d env none st (ExecStep.none st d env))
    (hEsSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecStep st d env (some e) st' (ExecStep.some st d env e st' v a))
    (hSeqNil :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecSeq st d env [] st Status.normal (ExecSeq.nil st d env))
    (hSeqConsNormal :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : SpecSt) (status : Status) (a : ExecS st d env s st' Status.normal) (a_1 : ExecSeq st' d env ss st'' status), mExecS st d env s st' Status.normal a → mExecSeq st' d env ss st'' status a_1 → mExecSeq st d env (s :: ss) st'' status (ExecSeq.consNormal st d env s ss st' st'' status a a_1))
    (hSeqConsAbrupt :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt) (status : Status) (a : ExecS st d env s st' status) (a_1 : status ≠ Status.normal), mExecS st d env s st' status a → mExecSeq st d env (s :: ss) st' status (ExecSeq.consAbrupt st d env s ss st' status a a_1))
    (hEntryHalts :
      ∀ (p : Program) (c : Config) (out : String) (st' : SpecSt)
        (t : ExecSeq initSt 0 0 p st' Status.normal),
        Loaded L p c → st'.out = out →
        mExecSeq initSt 0 0 p st' Status.normal t →
        Halts c out 0) :
    ∀ (p : Program) (c : Config) (out : String),
      Loaded L p c → BigStep p out → Halts c out 0 := by
  intro p c out hL hbs
  obtain ⟨st', hexec, hout⟩ := hbs
  exact hEntryHalts p c out st' hexec hL hout
    (execSeq_sim_of_cases
      hInt hStr hBool hNull hVar hAssign hBinary hOrTrue hOrFalse hAndFalse hAndTrue hNeg
      hNot hCall hFn hArgsNil hArgsCons hCallClosure hCallPrint hCallPrintln hCallAssertOk
      hSExpr hSVarInit hSVarNull hSBlock hSIfTrue hSIfFalse hSIfNone hSWhileFalse
      hSWhileBreak hSWhileRet hSWhileLoop hSForStart hSRet hSRetNull hSBrk hSCont hInitNone
      hInitSome hFlCondFalse hFlBodyBreak hFlBodyRet hFlLoop hFcNone hFcSome hEsNone hEsSome
      hSeqNil hSeqConsNormal hSeqConsAbrupt hexec)

end Vsa.Sim.TermSimClose
