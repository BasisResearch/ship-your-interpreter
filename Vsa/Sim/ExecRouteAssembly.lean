import Vsa.Sim.TermCaseBundle

/-!
# Context-indexed statement recursion

`ExecIH`, `ExecDispatchIH`, and `ExecWhileArmIH` start at different physical
machine states.  This file builds the product motive by structural recursion on
the semantic derivation.  It does not derive a post-prologue or live-frame IH
from the fresh-entry IH.

The remaining premises are constructor-local machine rows.  Every constructor
supplies its exact post-prologue row.  Only the four `while` constructors also
have a live-frame row at `0x80004034`.
-/

namespace Vsa.Sim

open LeanRV64DExecutable Sail
open Register
open Vsa.While
open Vsa.Sim.TermSimAssembly

local notation "SpecSt" => Vsa.While.St

/-- Constructor-local rows for the two non-fresh statement entries. -/
structure ExecRouteCases : Prop where
  hSExpr :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value) (a : EvalE st d env e st' v),
      mEvalE st d env e st' v a →
      ExecDispatchIH st d env (.expr e) st' .normal
  hSVarInit :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v),
      mEvalE st d env e st' v a →
      ExecDispatchIH st d env (.varDecl x (some e))
        ⟨st'.store.define env x v, st'.out⟩ .normal
  hSVarNull :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      ExecDispatchIH st d env (.varDecl x none)
        ⟨st.store.define env x .null, st.out⟩ .normal
  hSBlock :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
      (store' : Store) (inner : Addr) (st' : SpecSt) (status : Status)
      (a : st.store.allocFrame (some env) = (store', inner))
      (a_1 : ExecSeq ⟨store', st.out⟩ d inner ss st' status),
      mExecSeq ⟨store', st.out⟩ d inner ss st' status a_1 →
      ExecDispatchIH st d env (.block ss) st' status
  hSIfTrue :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) (st' st'' : SpecSt) (v : Value) (status : Status)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = true)
      (a_2 : ExecS st' d env t st'' status),
      mEvalE st d env c st' v a →
      mExecSRoute st' d env t st'' status a_2 →
      ExecDispatchIH st d env (.ifStmt c t e) st'' status
  hSIfFalse :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
      (st' st'' : SpecSt) (v : Value) (status : Status)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = false)
      (a_2 : ExecS st' d env e st'' status),
      mEvalE st d env c st' v a →
      mExecSRoute st' d env e st'' status a_2 →
      ExecDispatchIH st d env (.ifStmt c t (some e)) st'' status
  hSIfNone :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v)
      (a_1 : v.truthy = false),
      mEvalE st d env c st' v a →
      ExecDispatchIH st d env (.ifStmt c t none) st' .normal
  hSWhileFalse :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v)
      (a_1 : v.truthy = false),
      mEvalE st d env c st' v a →
      ExecDispatchIH st d env (.whileStmt c b) st' .normal ∧
      ExecWhileArmIH st d env c b st' .normal
  hSWhileBreak :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : SpecSt) (v : Value) (a : EvalE st d env c st' v)
      (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' .brk),
      mEvalE st d env c st' v a →
      mExecSRoute st' d env b st'' .brk a_2 →
      ExecDispatchIH st d env (.whileStmt c b) st'' .normal ∧
      ExecWhileArmIH st d env c b st'' .normal
  hSWhileRet :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : SpecSt) (v rv : Value) (a : EvalE st d env c st' v)
      (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' (.ret rv)),
      mEvalE st d env c st' v a →
      mExecSRoute st' d env b st'' (.ret rv) a_2 →
      ExecDispatchIH st d env (.whileStmt c b) st'' (.ret rv) ∧
      ExecWhileArmIH st d env c b st'' (.ret rv)
  hSWhileLoop :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' st''' : SpecSt) (v : Value) (status status' : Status)
      (a : EvalE st d env c st' v) (a_1 : v.truthy = true)
      (a_2 : ExecS st' d env b st'' status)
      (a_3 : status = .normal ∨ status = .cont)
      (a_4 : ExecS st'' d env (.whileStmt c b) st''' status'),
      mEvalE st d env c st' v a →
      mExecSRoute st' d env b st'' status a_2 →
      mExecSRoute st'' d env (.whileStmt c b) st''' status' a_4 →
      ExecDispatchIH st d env (.whileStmt c b) st''' status' ∧
      ExecWhileArmIH st d env c b st''' status'
  hSForStart :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr)
      (st' st'' : SpecSt) (status : Status)
      (a : st.store.allocFrame (some env) = (store', outer))
      (a_1 : ExecInit ⟨store', st.out⟩ d outer init st')
      (a_2 : ForLoop st' d outer cnd step b st'' status),
      mExecInit ⟨store', st.out⟩ d outer init st' a_1 →
      mForLoop st' d outer cnd step b st'' status a_2 →
      ExecDispatchIH st d env (.forStmt init cnd step b) st'' status
  hSRet :
    ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value) (a : EvalE st d env e st' v),
      mEvalE st d env e st' v a →
      ExecDispatchIH st d env (.ret (some e)) st' (.ret v)
  hSRetNull :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      ExecDispatchIH st d env (.ret none) st (.ret .null)
  hSBrk :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      ExecDispatchIH st d env .brk st .brk
  hSCont :
    ∀ (st : SpecSt) (d : Nat) (env : Addr),
      ExecDispatchIH st d env .cont st .cont

/-- Assemble the exact route product by mutual recursion on `ExecS`. -/
theorem execSRoute_of_cases
    (B : TermCaseBundle.TermCases) (R : ExecRouteCases)
    {st : SpecSt} {d : Nat} {env : Addr} {s : Stmt}
    {st' : SpecSt} {status : Status} (h : ExecS st d env s st' status) :
    mExecSRoute st d env s st' status h := by
  apply @ExecS.rec mEvalE mEvalArgs mCall mExecSRoute mExecInit mForLoop
    mForCond mExecStep mExecSeq
  · exact B.hInt
  · exact B.hStr
  · exact B.hBool
  · exact B.hNull
  · exact B.hVar
  · exact B.hAssign
  · exact B.hBinary
  · exact B.hOrTrue
  · exact B.hOrFalse
  · exact B.hAndFalse
  · exact B.hAndTrue
  · exact B.hNeg
  · exact B.hNot
  · exact B.hCall
  · exact B.hFn
  · exact B.hArgsNil
  · exact B.hArgsCons
  · exact B.hCallClosure
  · exact B.hCallPrint
  · exact B.hCallPrintln
  · exact B.hCallAssertOk
  · intro st d env e st' v a hE
    exact { fresh := B.hSExpr st d env e st' v a hE
            dispatch := R.hSExpr st d env e st' v a hE
            whileArm := by intro c b heq; cases heq }
  · intro st d env x e st' v a hE
    exact { fresh := B.hSVarInit st d env x e st' v a hE
            dispatch := R.hSVarInit st d env x e st' v a hE
            whileArm := by intro c b heq; cases heq }
  · intro st d env x
    exact { fresh := B.hSVarNull st d env x
            dispatch := R.hSVarNull st d env x
            whileArm := by intro c b heq; cases heq }
  · intro st d env ss store' inner st' status a a_1 hSeq
    exact { fresh := B.hSBlock st d env ss store' inner st' status a a_1 hSeq
            dispatch := R.hSBlock st d env ss store' inner st' status a a_1 hSeq
            whileArm := by intro c b heq; cases heq }
  · intro st d env c t e st' st'' v status a a_1 a_2 hC hT
    exact { fresh := B.hSIfTrue st d env c t e st' st'' v status a a_1 a_2 hC hT.fresh
            dispatch := R.hSIfTrue st d env c t e st' st'' v status a a_1 a_2 hC hT
            whileArm := by intro c' b heq; cases heq }
  · intro st d env c t e st' st'' v status a a_1 a_2 hC hE
    exact { fresh := B.hSIfFalse st d env c t e st' st'' v status a a_1 a_2 hC hE.fresh
            dispatch := R.hSIfFalse st d env c t e st' st'' v status a a_1 a_2 hC hE
            whileArm := by intro c' b heq; cases heq }
  · intro st d env c t st' v a a_1 hC
    exact { fresh := B.hSIfNone st d env c t st' v a a_1 hC
            dispatch := R.hSIfNone st d env c t st' v a a_1 hC
            whileArm := by intro c' b heq; cases heq }
  · intro st d env c b st' v a a_1 hC
    have hR := R.hSWhileFalse st d env c b st' v a a_1 hC
    exact { fresh := B.hSWhileFalse st d env c b st' v a a_1 hC
            dispatch := hR.1
            whileArm := by intro c' b' heq; cases heq; exact hR.2 }
  · intro st d env c b st' st'' v a a_1 a_2 hC hB
    have hR := R.hSWhileBreak st d env c b st' st'' v a a_1 a_2 hC hB
    exact { fresh := B.hSWhileBreak st d env c b st' st'' v a a_1 a_2 hC hB.fresh
            dispatch := hR.1
            whileArm := by intro c' b' heq; cases heq; exact hR.2 }
  · intro st d env c b st' st'' v rv a a_1 a_2 hC hB
    have hR := R.hSWhileRet st d env c b st' st'' v rv a a_1 a_2 hC hB
    exact { fresh := B.hSWhileRet st d env c b st' st'' v rv a a_1 a_2 hC hB.fresh
            dispatch := hR.1
            whileArm := by intro c' b' heq; cases heq; exact hR.2 }
  · intro st d env c b st' st'' st''' v status status' a a_1 a_2 a_3 a_4 hC hB hRest
    have hR := R.hSWhileLoop st d env c b st' st'' st''' v status status'
      a a_1 a_2 a_3 a_4 hC hB hRest
    exact { fresh := B.hSWhileLoop st d env c b st' st'' st''' v status status'
              a a_1 a_2 a_3 a_4 hC hB.fresh hRest.fresh
            dispatch := hR.1
            whileArm := by intro c' b' heq; cases heq; exact hR.2 }
  · intro st d env init cnd step b store' outer st' st'' status a a_1 a_2 hInit hFor
    exact { fresh := B.hSForStart st d env init cnd step b store' outer st' st'' status
              a a_1 a_2 hInit hFor
            dispatch := R.hSForStart st d env init cnd step b store' outer st' st'' status
              a a_1 a_2 hInit hFor
            whileArm := by intro c b heq; cases heq }
  · intro st d env e st' v a hE
    exact { fresh := B.hSRet st d env e st' v a hE
            dispatch := R.hSRet st d env e st' v a hE
            whileArm := by intro c b heq; cases heq }
  · intro st d env
    exact { fresh := B.hSRetNull st d env
            dispatch := R.hSRetNull st d env
            whileArm := by intro c b heq; cases heq }
  · intro st d env
    exact { fresh := B.hSBrk st d env
            dispatch := R.hSBrk st d env
            whileArm := by intro c b heq; cases heq }
  · intro st d env
    exact { fresh := B.hSCont st d env
            dispatch := R.hSCont st d env
            whileArm := by intro c b heq; cases heq }
  · exact B.hInitNone
  · intro st d env s st' status a hS
    exact B.hInitSome st d env s st' status a hS.fresh
  · exact B.hFlCondFalse
  · intro st d env cnd step b st' st'' a a_1 hC hB
    exact B.hFlBodyBreak st d env cnd step b st' st'' a a_1 hC hB.fresh
  · intro st d env cnd step b st' st'' rv a a_1 hC hB
    exact B.hFlBodyRet st d env cnd step b st' st'' rv a a_1 hC hB.fresh
  · intro st d env cnd step b st' st'' st''' st'''' status status'
      a a_1 a_2 a_3 a_4 hC hB hStep hRest
    exact B.hFlLoop st d env cnd step b st' st'' st''' st'''' status status'
      a a_1 a_2 a_3 a_4 hC hB.fresh hStep hRest
  · exact B.hFcNone
  · exact B.hFcSome
  · exact B.hEsNone
  · exact B.hEsSome
  · exact B.hSeqNil
  · intro st d env s ss st' st'' status a a_1 hS hSeq
    exact B.hSeqConsNormal st d env s ss st' st'' status a a_1 hS.fresh hSeq
  · intro st d env s ss st' status a a_1 hS
    exact B.hSeqConsAbrupt st d env s ss st' status a a_1 hS.fresh

/--
Direct mutual induction with the statement motive strengthened to the three-route
product.  In particular, recursive statement premises are route products; no
fresh-entry theorem is repurposed at either internal entry point.
-/
theorem execSRoute_of_mutual_cases
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
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr) (st' st'' st''' : SpecSt) (fv : Value) (vs : List Value) (v : Value) (a : EvalE st d env f st' fv) (a_1 : args.length ≤ maxArgs) (a_2 : EvalArgs st' d env args st'' vs) (a_3 : Call st'' d fv vs st''' v), mEvalE st d env f st' fv a → mEvalArgs st' d env args st'' vs a_2 → mCall st'' d fv vs st''' v a_3 → mEvalE st d env (f.call args) st''' v (EvalE.call st d env f args st' st'' st''' fv vs v a a_1 a_2 a_3))
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
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecSRoute st d env (Stmt.expr e) st' Status.normal (ExecS.expr st d env e st' v a))
    (hSVarInit :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecSRoute st d env (Stmt.varDecl x (some e)) { store := st'.store.define env x v, out := st'.out } Status.normal (ExecS.varInit st d env x e st' v a))
    (hSVarNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String), mExecSRoute st d env (Stmt.varDecl x none) { store := st.store.define env x Value.null, out := st.out } Status.normal (ExecS.varNull st d env x))
    (hSBlock :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store) (inner : Addr) (st' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', inner)) (a_1 : ExecSeq { store := store', out := st.out } d inner ss st' status), mExecSeq { store := store', out := st.out } d inner ss st' status a_1 → mExecSRoute st d env (Stmt.block ss) st' status (ExecS.block st d env ss store' inner st' status a a_1))
    (hSIfTrue :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (e : Option Stmt) (st' st'' : SpecSt) (v : Value) (status : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env t st'' status), mEvalE st d env c st' v a → mExecSRoute st' d env t st'' status a_2 → mExecSRoute st d env (Stmt.ifStmt c t e) st'' status (ExecS.ifTrue st d env c t e st' st'' v status a a_1 a_2))
    (hSIfFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt) (st' st'' : SpecSt) (v : Value) (status : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = false) (a_2 : ExecS st' d env e st'' status), mEvalE st d env c st' v a → mExecSRoute st' d env e st'' status a_2 → mExecSRoute st d env (Stmt.ifStmt c t (some e)) st'' status (ExecS.ifFalse st d env c t e st' st'' v status a a_1 a_2))
    (hSIfNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mExecSRoute st d env (Stmt.ifStmt c t none) st' Status.normal (ExecS.ifNone st d env c t st' v a a_1))
    (hSWhileFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mExecSRoute st d env (Stmt.whileStmt c b) st' Status.normal (ExecS.whileFalse st d env c b st' v a a_1))
    (hSWhileBreak :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' Status.brk), mEvalE st d env c st' v a → mExecSRoute st' d env b st'' Status.brk a_2 → mExecSRoute st d env (Stmt.whileStmt c b) st'' Status.normal (ExecS.whileBreak st d env c b st' st'' v a a_1 a_2))
    (hSWhileRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' : SpecSt) (v rv : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' (Status.ret rv)), mEvalE st d env c st' v a → mExecSRoute st' d env b st'' (Status.ret rv) a_2 → mExecSRoute st d env (Stmt.whileStmt c b) st'' (Status.ret rv) (ExecS.whileRet st d env c b st' st'' v rv a a_1 a_2))
    (hSWhileLoop :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) (st' st'' st''' : SpecSt) (v : Value) (status status' : Status) (a : EvalE st d env c st' v) (a_1 : v.truthy = true) (a_2 : ExecS st' d env b st'' status) (a_3 : status = Status.normal ∨ status = Status.cont) (a_4 : ExecS st'' d env (Stmt.whileStmt c b) st''' status'), mEvalE st d env c st' v a → mExecSRoute st' d env b st'' status a_2 → mExecSRoute st'' d env (Stmt.whileStmt c b) st''' status' a_4 → mExecSRoute st d env (Stmt.whileStmt c b) st''' status' (ExecS.whileLoop st d env c b st' st'' st''' v status status' a a_1 a_2 a_3 a_4))
    (hSForStart :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt) (cnd step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr) (st' st'' : SpecSt) (status : Status) (a : st.store.allocFrame (some env) = (store', outer)) (a_1 : ExecInit { store := store', out := st.out } d outer init st') (a_2 : ForLoop st' d outer cnd step b st'' status), mExecInit { store := store', out := st.out } d outer init st' a_1 → mForLoop st' d outer cnd step b st'' status a_2 → mExecSRoute st d env (Stmt.forStmt init cnd step b) st'' status (ExecS.forStart st d env init cnd step b store' outer st' st'' status a a_1 a_2))
    (hSRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt) (v : Value) (a : EvalE st d env e st' v), mEvalE st d env e st' v a → mExecSRoute st d env (Stmt.ret (some e)) st' (Status.ret v) (ExecS.ret st d env e st' v a))
    (hSRetNull :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecSRoute st d env (Stmt.ret none) st (Status.ret Value.null) (ExecS.retNull st d env))
    (hSBrk :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecSRoute st d env Stmt.brk st Status.brk (ExecS.brk st d env))
    (hSCont :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecSRoute st d env Stmt.cont st Status.cont (ExecS.cont st d env))
    (hInitNone :
      ∀ (st : SpecSt) (d : Nat) (env : Addr), mExecInit st d env none st (ExecInit.none st d env))
    (hInitSome :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (st' : SpecSt) (status : Status) (a : ExecS st d env s st' status), mExecSRoute st d env s st' status a → mExecInit st d env (some s) st' (ExecInit.some st d env s st' status a))
    (hFlCondFalse :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr) (b : Stmt) (st' : SpecSt) (v : Value) (a : EvalE st d env c st' v) (a_1 : v.truthy = false), mEvalE st d env c st' v a → mForLoop st d env (some c) step b st' Status.normal (ForLoop.condFalse st d env c step b st' v a a_1))
    (hFlBodyBreak :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : SpecSt) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' Status.brk), mForCond st d env cnd st' a → mExecSRoute st' d env b st'' Status.brk a_1 → mForLoop st d env cnd step b st'' Status.normal (ForLoop.bodyBreak st d env cnd step b st' st'' a a_1))
    (hFlBodyRet :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' : SpecSt) (rv : Value) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' (Status.ret rv)), mForCond st d env cnd st' a → mExecSRoute st' d env b st'' (Status.ret rv) a_1 → mForLoop st d env cnd step b st'' (Status.ret rv) (ForLoop.bodyRet st d env cnd step b st' st'' rv a a_1))
    (hFlLoop :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : SpecSt) (status status' : Status) (a : ForCond st d env cnd st') (a_1 : ExecS st' d env b st'' status) (a_2 : status = Status.normal ∨ status = Status.cont) (a_3 : ExecStep st'' d env step st''') (a_4 : ForLoop st''' d env cnd step b st'''' status'), mForCond st d env cnd st' a → mExecSRoute st' d env b st'' status a_1 → mExecStep st'' d env step st''' a_3 → mForLoop st''' d env cnd step b st'''' status' a_4 → mForLoop st d env cnd step b st'''' status' (ForLoop.loop st d env cnd step b st' st'' st''' st'''' status status' a a_1 a_2 a_3 a_4))
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
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' st'' : SpecSt) (status : Status) (a : ExecS st d env s st' Status.normal) (a_1 : ExecSeq st' d env ss st'' status), mExecSRoute st d env s st' Status.normal a → mExecSeq st' d env ss st'' status a_1 → mExecSeq st d env (s :: ss) st'' status (ExecSeq.consNormal st d env s ss st' st'' status a a_1))
    (hSeqConsAbrupt :
      ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt) (status : Status) (a : ExecS st d env s st' status) (a_1 : status ≠ Status.normal), mExecSRoute st d env s st' status a → mExecSeq st d env (s :: ss) st' status (ExecSeq.consAbrupt st d env s ss st' status a a_1))
    {st : SpecSt} {d : Nat} {env : Addr} {s : Stmt} {st' : SpecSt} {status : Status}
    (t : ExecS st d env s st' status) : mExecSRoute st d env s st' status t :=
  @ExecS.rec mEvalE mEvalArgs mCall mExecSRoute mExecInit mForLoop mForCond mExecStep
    mExecSeq
    hInt hStr hBool hNull hVar hAssign hBinary hOrTrue hOrFalse hAndFalse hAndTrue hNeg
    hNot hCall hFn hArgsNil hArgsCons hCallClosure hCallPrint hCallPrintln hCallAssertOk
    hSExpr hSVarInit hSVarNull hSBlock hSIfTrue hSIfFalse hSIfNone hSWhileFalse
    hSWhileBreak hSWhileRet hSWhileLoop hSForStart hSRet hSRetNull hSBrk hSCont hInitNone
    hInitSome hFlCondFalse hFlBodyBreak hFlBodyRet hFlLoop hFcNone hFcSome hEsNone hEsSome
    hSeqNil hSeqConsNormal hSeqConsAbrupt
    st d env s st' status t

/-- Adapter for a pre-existing fresh-entry bundle.  Not used to close the
capstone fixed point. -/
theorem execSRouteFamily_of_cases
    (B : TermCaseBundle.TermCases) (R : ExecRouteCases) : ExecSRouteFamily := by
  intro st d env s st' status h
  exact execSRoute_of_cases B R h

#print axioms execSRoute_of_cases
#print axioms execSRouteFamily_of_cases
#print axioms execSRoute_of_mutual_cases

end Vsa.Sim
