import Vsa.While.Semantics

namespace Vsa.CT

open Vsa.While

def divInfo (op : BinOp) (l r : Value) : Option (Int × Int) :=
  match op, l, r with
  | .div, .int a, .int b => some (a, b)
  | .mod, .int a, .int b => some (a, b)
  | _, _, _ => none

mutual

inductive EL where
  | leaf
  | asg (l : EL)
  | bin (l r : EL) (d : Option (Int × Int))
  | orT (l : EL)
  | orF (l r : EL)
  | andF (l : EL)
  | andT (l r : EL)
  | un (l : EL)
  | call (f : EL) (args : List EL) (c : CL)
  | fn

inductive CL where
  | clo (body : List SL)
  | print (vs : List Value)
  | println (vs : List Value)
  | assert

inductive SL where
  | expr (l : EL)
  | varInit (l : EL)
  | varNull
  | block (ss : List SL)
  | ifT (c : EL) (s : SL)
  | ifF (c : EL) (s : SL)
  | ifN (c : EL)
  | whileF (c : EL)
  | whileBrk (c : EL) (b : SL)
  | whileRet (c : EL) (b : SL)
  | whileLoop (c : EL) (b : SL) (rest : SL)
  | forS (init : Option SL) (lp : FL)
  | ret (l : EL)
  | retNull
  | brk
  | cont

inductive FL where
  | condF (c : EL)
  | bodyBrk (c : Option EL) (b : SL)
  | bodyRet (c : Option EL) (b : SL)
  | loop (c : Option EL) (b : SL) (step : Option EL) (rest : FL)

end

mutual

inductive EvalL : St → Nat → Addr → Expr → St → Value → EL → Prop where
  | int (st : St) (d : Nat) (env : Addr) (n : Int) :
    EvalL st d env (.int n) st (.int n) .leaf
  | str (st : St) (d : Nat) (env : Addr) (s : String) :
    EvalL st d env (.str s) st (.str s) .leaf
  | bool (st : St) (d : Nat) (env : Addr) (b : Bool) :
    EvalL st d env (.bool b) st (.bool b) .leaf
  | null (st : St) (d : Nat) (env : Addr) :
    EvalL st d env .null st .null .leaf
  | var (st : St) (d : Nat) (env : Addr) (x : String) (v : Value) :
    st.store.get? env x = some v →
    EvalL st d env (.var x) st v .leaf
  | assign (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St)
      (v : Value) (store'' : Store) (l : EL) :
    EvalL st d env e st' v l →
    st'.store.set? env x v = some store'' →
    EvalL st d env (.assign x e) ⟨store'', st'.out⟩ v (.asg l)
  | binary (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : St) (lv rv v : Value) (ll lr : EL) :
    EvalL st d env l st' lv ll →
    EvalL st' d env r st'' rv lr →
    binOpSem st''.store op lv rv = some v →
    EvalL st d env (.binary op l r) st'' v (.bin ll lr (divInfo op lv rv))
  | orTrue (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) (ll : EL) :
    EvalL st d env l st' lv ll → lv.truthy = true →
    EvalL st d env (.logical .or l r) st' (.bool true) (.orT ll)
  | orFalse (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St)
      (lv rv : Value) (ll lr : EL) :
    EvalL st d env l st' lv ll → lv.truthy = false →
    EvalL st' d env r st'' rv lr →
    EvalL st d env (.logical .or l r) st'' (.bool rv.truthy) (.orF ll lr)
  | andFalse (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) (ll : EL) :
    EvalL st d env l st' lv ll → lv.truthy = false →
    EvalL st d env (.logical .and l r) st' (.bool false) (.andF ll)
  | andTrue (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St)
      (lv rv : Value) (ll lr : EL) :
    EvalL st d env l st' lv ll → lv.truthy = true →
    EvalL st' d env r st'' rv lr →
    EvalL st d env (.logical .and l r) st'' (.bool rv.truthy) (.andT ll lr)
  | neg (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (n : Int) (l : EL) :
    EvalL st d env e st' (.int n) l →
    EvalL st d env (.unary .neg e) st' (.int (wrap64 (-n))) (.un l)
  | not (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) (l : EL) :
    EvalL st d env e st' v l →
    EvalL st d env (.unary .not e) st' (.bool (!v.truthy)) (.un l)
  | call (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' st''' : St) (fv : Value) (vs : List Value) (v : Value)
      (lf : EL) (la : List EL) (lc : CL) :
    EvalL st d env f st' fv lf →
    args.length ≤ maxArgs →
    EvalArgsL st' d env args st'' vs la →
    CallL st'' d fv vs st''' v lc →
    EvalL st d env (.call f args) st''' v (.call lf la lc)
  | fn (st : St) (d : Nat) (env : Addr) (name : Option String)
      (params : List String) (body : List Stmt) (store' : Store) (a : Addr) :
    st.store.allocClosure ⟨env, name, params, body⟩ = (store', a) →
    EvalL st d env (.fn name params body) ⟨store', st.out⟩ (.closure a) .fn

inductive EvalArgsL : St → Nat → Addr → List Expr → St → List Value → List EL → Prop where
  | nil (st : St) (d : Nat) (env : Addr) : EvalArgsL st d env [] st [] []
  | cons (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' st'' : St) (v : Value) (vs : List Value) (l : EL) (ls : List EL) :
    EvalL st d env e st' v l →
    EvalArgsL st' d env es st'' vs ls →
    EvalArgsL st d env (e :: es) st'' (v :: vs) (l :: ls)

inductive CallL : St → Nat → Value → List Value → St → Value → CL → Prop where
  | closure (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : St) (status : Status)
      (v : Value) (lb : List SL) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeqL ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st.out⟩ (d + 1) frame cd.body st' status lb →
    (status = .normal ∧ v = .null ∨ status = .ret v) →
    CallL st d (.closure a) vs st' v (.clo lb)
  | print (st : St) (d : Nat) (vs : List Value) :
    CallL st d (.native .print) vs
      ⟨st.store, st.out ++ printArgs st.store vs⟩ .null (.print vs)
  | println (st : St) (d : Nat) (vs : List Value) :
    CallL st d (.native .println) vs
      ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null (.println vs)
  | assertOk (st : St) (d : Nat) (vs : List Value) (v m : Value) :
    (vs = [v] ∨ vs = [v, m]) →
    v.truthy = true →
    CallL st d (.native .assert) vs st .null .assert

inductive ExecL : St → Nat → Addr → Stmt → St → Status → SL → Prop where
  | expr (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) (l : EL) :
    EvalL st d env e st' v l →
    ExecL st d env (.expr e) st' .normal (.expr l)
  | varInit (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St)
      (v : Value) (l : EL) :
    EvalL st d env e st' v l →
    ExecL st d env (.varDecl x (some e))
      ⟨st'.store.define env x v, st'.out⟩ .normal (.varInit l)
  | varNull (st : St) (d : Nat) (env : Addr) (x : String) :
    ExecL st d env (.varDecl x none)
      ⟨st.store.define env x .null, st.out⟩ .normal .varNull
  | block (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr) (st' : St) (status : Status) (ls : List SL) :
    st.store.allocFrame (some env) = (store', inner) →
    ExecSeqL ⟨store', st.out⟩ d inner ss st' status ls →
    ExecL st d env (.block ss) st' status (.block ls)
  | ifTrue (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) (st' st'' : St) (v : Value) (status : Status) (lc : EL) (lt : SL) :
    EvalL st d env c st' v lc → v.truthy = true →
    ExecL st' d env t st'' status lt →
    ExecL st d env (.ifStmt c t e) st'' status (.ifT lc lt)
  | ifFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
      (st' st'' : St) (v : Value) (status : Status) (lc : EL) (le : SL) :
    EvalL st d env c st' v lc → v.truthy = false →
    ExecL st' d env e st'' status le →
    ExecL st d env (.ifStmt c t (some e)) st'' status (.ifF lc le)
  | ifNone (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : St)
      (v : Value) (lc : EL) :
    EvalL st d env c st' v lc → v.truthy = false →
    ExecL st d env (.ifStmt c t none) st' .normal (.ifN lc)
  | whileFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' : St) (v : Value) (lc : EL) :
    EvalL st d env c st' v lc → v.truthy = false →
    ExecL st d env (.whileStmt c b) st' .normal (.whileF lc)
  | whileBreak (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v : Value) (lc : EL) (lb : SL) :
    EvalL st d env c st' v lc → v.truthy = true →
    ExecL st' d env b st'' .brk lb →
    ExecL st d env (.whileStmt c b) st'' .normal (.whileBrk lc lb)
  | whileRet (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v rv : Value) (lc : EL) (lb : SL) :
    EvalL st d env c st' v lc → v.truthy = true →
    ExecL st' d env b st'' (.ret rv) lb →
    ExecL st d env (.whileStmt c b) st'' (.ret rv) (.whileRet lc lb)
  | whileLoop (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' st''' : St) (v : Value) (status status' : Status) (lc : EL) (lb lr : SL) :
    EvalL st d env c st' v lc → v.truthy = true →
    ExecL st' d env b st'' status lb →
    (status = .normal ∨ status = .cont) →
    ExecL st'' d env (.whileStmt c b) st''' status' lr →
    ExecL st d env (.whileStmt c b) st''' status' (.whileLoop lc lb lr)
  | forStart (st : St) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' st'' : St) (status : Status) (li : Option SL) (lf : FL) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecInitL ⟨store', st.out⟩ d outer init st' li →
    ForLoopL st' d outer cnd step b st'' status lf →
    ExecL st d env (.forStmt init cnd step b) st'' status (.forS li lf)
  | ret (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) (l : EL) :
    EvalL st d env e st' v l →
    ExecL st d env (.ret (some e)) st' (.ret v) (.ret l)
  | retNull (st : St) (d : Nat) (env : Addr) :
    ExecL st d env (.ret none) st (.ret .null) .retNull
  | brk (st : St) (d : Nat) (env : Addr) : ExecL st d env .brk st .brk .brk
  | cont (st : St) (d : Nat) (env : Addr) : ExecL st d env .cont st .cont .cont

inductive ExecInitL : St → Nat → Addr → Option Stmt → St → Option SL → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ExecInitL st d env none st none
  | some (st : St) (d : Nat) (env : Addr) (s : Stmt) (st' : St) (status : Status) (l : SL) :
    ExecL st d env s st' status l →
    ExecInitL st d env (some s) st' (some l)

inductive ForLoopL : St → Nat → Addr → Option Expr → Option Expr → Stmt → St →
    Status → FL → Prop where
  | condFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr)
      (b : Stmt) (st' : St) (v : Value) (lc : EL) :
    EvalL st d env c st' v lc → v.truthy = false →
    ForLoopL st d env (some c) step b st' .normal (.condF lc)
  | bodyBreak (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' : St) (lc : Option EL) (lb : SL) :
    ForCondL st d env cnd st' lc →
    ExecL st' d env b st'' .brk lb →
    ForLoopL st d env cnd step b st'' .normal (.bodyBrk lc lb)
  | bodyRet (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' : St) (rv : Value) (lc : Option EL) (lb : SL) :
    ForCondL st d env cnd st' lc →
    ExecL st' d env b st'' (.ret rv) lb →
    ForLoopL st d env cnd step b st'' (.ret rv) (.bodyRet lc lb)
  | loop (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : St)
      (status status' : Status) (lc : Option EL) (lb : SL) (ls : Option EL) (lr : FL) :
    ForCondL st d env cnd st' lc →
    ExecL st' d env b st'' status lb →
    (status = .normal ∨ status = .cont) →
    ExecStepL st'' d env step st''' ls →
    ForLoopL st''' d env cnd step b st'''' status' lr →
    ForLoopL st d env cnd step b st'''' status' (.loop lc lb ls lr)

inductive ForCondL : St → Nat → Addr → Option Expr → St → Option EL → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ForCondL st d env none st none
  | some (st : St) (d : Nat) (env : Addr) (c : Expr) (st' : St) (v : Value) (l : EL) :
    EvalL st d env c st' v l → v.truthy = true →
    ForCondL st d env (some c) st' (some l)

inductive ExecStepL : St → Nat → Addr → Option Expr → St → Option EL → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ExecStepL st d env none st none
  | some (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) (l : EL) :
    EvalL st d env e st' v l →
    ExecStepL st d env (some e) st' (some l)

inductive ExecSeqL : St → Nat → Addr → List Stmt → St → Status → List SL → Prop where
  | nil (st : St) (d : Nat) (env : Addr) : ExecSeqL st d env [] st .normal []
  | consNormal (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' st'' : St) (status : Status) (l : SL) (ls : List SL) :
    ExecL st d env s st' .normal l →
    ExecSeqL st' d env ss st'' status ls →
    ExecSeqL st d env (s :: ss) st'' status (l :: ls)
  | consAbrupt (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : St) (status : Status) (l : SL) :
    ExecL st d env s st' status l →
    status ≠ .normal →
    ExecSeqL st d env (s :: ss) st' status [l]

end

def BigStepL (p : Program) (out : String) (ℓ : List SL) : Prop :=
  ∃ st', ExecSeqL initSt 0 0 p st' .normal ℓ ∧ st'.out = out

end Vsa.CT
