import Vsa.While.Semantics
import Vsa.Machine

namespace Vsa.While

mutual

inductive EvalErr : St → Nat → Addr → Expr → Prop where

  | varUndef (st : St) (d : Nat) (env : Addr) (x : String) :
    st.store.get? env x = none →
    EvalErr st d env (.var x)

  | assignE (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) :
    EvalErr st d env e →
    EvalErr st d env (.assign x e)

  | assignUnbound (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : St) (v : Value) :
    EvalE st d env e st' v →
    st'.store.set? env x v = none →
    EvalErr st d env (.assign x e)

  | binaryL (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) :
    EvalErr st d env l →
    EvalErr st d env (.binary op l r)
  | binaryR (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' : St) (lv : Value) :
    EvalE st d env l st' lv →
    EvalErr st' d env r →
    EvalErr st d env (.binary op l r)

  | binaryOp (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : St) (lv rv : Value) :
    EvalE st d env l st' lv →
    EvalE st' d env r st'' rv →
    binOpSem st''.store op lv rv = none →
    EvalErr st d env (.binary op l r)

  | orL (st : St) (d : Nat) (env : Addr) (l r : Expr) :
    EvalErr st d env l →
    EvalErr st d env (.logical .or l r)
  | orR (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St) (lv : Value) :
    EvalE st d env l st' lv → lv.truthy = false →
    EvalErr st' d env r →
    EvalErr st d env (.logical .or l r)
  | andL (st : St) (d : Nat) (env : Addr) (l r : Expr) :
    EvalErr st d env l →
    EvalErr st d env (.logical .and l r)
  | andR (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St) (lv : Value) :
    EvalE st d env l st' lv → lv.truthy = true →
    EvalErr st' d env r →
    EvalErr st d env (.logical .and l r)

  | unaryE (st : St) (d : Nat) (env : Addr) (op : UnOp) (e : Expr) :
    EvalErr st d env e →
    EvalErr st d env (.unary op e)

  | negType (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) :
    EvalE st d env e st' v →
    (∀ n : Int, v ≠ .int n) →
    EvalErr st d env (.unary .neg e)

  | callF (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr) :
    EvalErr st d env f →
    EvalErr st d env (.call f args)

  | callTooMany (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : St) (fv : Value) :
    EvalE st d env f st' fv →
    maxArgs < args.length →
    EvalErr st d env (.call f args)
  | callArgs (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : St) (fv : Value) :
    EvalE st d env f st' fv →
    args.length ≤ maxArgs →
    EvalArgsErr st' d env args →
    EvalErr st d env (.call f args)

  | callC (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : St) (fv : Value) (vs : List Value) :
    EvalE st d env f st' fv →
    args.length ≤ maxArgs →
    EvalArgs st' d env args st'' vs →
    CallErr st'' d fv vs →
    EvalErr st d env (.call f args)

inductive EvalArgsErr : St → Nat → Addr → List Expr → Prop where
  | head (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr) :
    EvalErr st d env e →
    EvalArgsErr st d env (e :: es)
  | tail (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : St) (v : Value) :
    EvalE st d env e st' v →
    EvalArgsErr st' d env es →
    EvalArgsErr st d env (e :: es)

inductive CallErr : St → Nat → Value → List Value → Prop where

  | notCallable (st : St) (d : Nat) (fv : Value) (vs : List Value) :
    (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) →
    CallErr st d fv vs

  | badClosure (st : St) (d : Nat) (a : Addr) (vs : List Value) :
    st.store.closures[a]? = none →
    CallErr st d (.closure a) vs

  | arity (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) :
    st.store.closures[a]? = some cd →
    vs.length ≠ cd.params.length →
    CallErr st d (.closure a) vs

  | depth (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    ¬ d < maxCallDepth →
    CallErr st d (.closure a) vs

  | body (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeqErr ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st.out⟩ (d + 1) frame cd.body →
    CallErr st d (.closure a) vs

  | escape (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : St) (status : Status) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st.out⟩ (d + 1) frame cd.body st' status →
    (status = .brk ∨ status = .cont) →
    CallErr st d (.closure a) vs

  | assertFail (st : St) (d : Nat) (vs : List Value) (v m : Value) :
    (vs = [v] ∨ vs = [v, m]) →
    v.truthy = false →
    CallErr st d (.native .assert) vs
  | assertArity (st : St) (d : Nat) (vs : List Value) :
    (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) →
    CallErr st d (.native .assert) vs

inductive ExecErr : St → Nat → Addr → Stmt → Prop where
  | expr (st : St) (d : Nat) (env : Addr) (e : Expr) :
    EvalErr st d env e →
    ExecErr st d env (.expr e)
  | varInit (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) :
    EvalErr st d env e →
    ExecErr st d env (.varDecl x (some e))
  | block (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr) :
    st.store.allocFrame (some env) = (store', inner) →
    ExecSeqErr ⟨store', st.out⟩ d inner ss →
    ExecErr st d env (.block ss)

  | ifCond (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) :
    EvalErr st d env c →
    ExecErr st d env (.ifStmt c t e)
  | ifThen (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = true →
    ExecErr st' d env t →
    ExecErr st d env (.ifStmt c t e)
  | ifElse (st : St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
      (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = false →
    ExecErr st' d env e →
    ExecErr st d env (.ifStmt c t (some e))

  | whileCond (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) :
    EvalErr st d env c →
    ExecErr st d env (.whileStmt c b)
  | whileBody (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = true →
    ExecErr st' d env b →
    ExecErr st d env (.whileStmt c b)
  | whileLoop (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v : Value) (status : Status) :
    EvalE st d env c st' v → v.truthy = true →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    ExecErr st'' d env (.whileStmt c b) →
    ExecErr st d env (.whileStmt c b)

  | forInit (st : St) (d : Nat) (env : Addr) (init : Stmt) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecErr ⟨store', st.out⟩ d outer init →
    ExecErr st d env (.forStmt (some init) cnd step b)
  | forLoop (st : St) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' : St) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    ForLoopErr st' d outer cnd step b →
    ExecErr st d env (.forStmt init cnd step b)
  | ret (st : St) (d : Nat) (env : Addr) (e : Expr) :
    EvalErr st d env e →
    ExecErr st d env (.ret (some e))

inductive ForLoopErr : St → Nat → Addr → Option Expr → Option Expr → Stmt →
    Prop where

  | cond (st : St) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr)
      (b : Stmt) :
    EvalErr st d env c →
    ForLoopErr st d env (some c) step b

  | body (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' : St) :
    ForCond st d env cnd st' →
    ExecErr st' d env b →
    ForLoopErr st d env cnd step b

  | step (st : St) (d : Nat) (env : Addr) (cnd : Option Expr) (e : Expr)
      (b : Stmt) (st' st'' : St) (status : Status) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    EvalErr st'' d env e →
    ForLoopErr st d env cnd (some e) b

  | loop (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' : St) (status : Status) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    ExecStep st'' d env step st''' →
    ForLoopErr st''' d env cnd step b →
    ForLoopErr st d env cnd step b

inductive ExecSeqErr : St → Nat → Addr → List Stmt → Prop where
  | head (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) :
    ExecErr st d env s →
    ExecSeqErr st d env (s :: ss)
  | tail (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : St) :
    ExecS st d env s st' .normal →
    ExecSeqErr st' d env ss →
    ExecSeqErr st d env (s :: ss)

end

def TopAbrupt (p : Program) : Prop :=
  ∃ (st' : St) (status : Status), status ≠ .normal ∧ ExecSeq initSt 0 0 p st' status

def BigStepErr (p : Program) : Prop :=
  ExecSeqErr initSt 0 0 p ∨ TopAbrupt p

mutual

inductive EApprox : Nat → St → Nat → Addr → Expr → Prop where
  | zero (st : St) (d : Nat) (env : Addr) (e : Expr) :
    EApprox 0 st d env e
  | assignE (n : Nat) (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) :
    EApprox n st d env e →
    EApprox (n + 1) st d env (.assign x e)
  | binaryL (n : Nat) (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) :
    EApprox n st d env l →
    EApprox (n + 1) st d env (.binary op l r)
  | binaryR (n : Nat) (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' : St) (lv : Value) :
    EvalE st d env l st' lv →
    EApprox n st' d env r →
    EApprox (n + 1) st d env (.binary op l r)
  | orL (n : Nat) (st : St) (d : Nat) (env : Addr) (l r : Expr) :
    EApprox n st d env l →
    EApprox (n + 1) st d env (.logical .or l r)
  | orR (n : Nat) (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) :
    EvalE st d env l st' lv → lv.truthy = false →
    EApprox n st' d env r →
    EApprox (n + 1) st d env (.logical .or l r)
  | andL (n : Nat) (st : St) (d : Nat) (env : Addr) (l r : Expr) :
    EApprox n st d env l →
    EApprox (n + 1) st d env (.logical .and l r)
  | andR (n : Nat) (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) :
    EvalE st d env l st' lv → lv.truthy = true →
    EApprox n st' d env r →
    EApprox (n + 1) st d env (.logical .and l r)
  | unaryE (n : Nat) (st : St) (d : Nat) (env : Addr) (op : UnOp) (e : Expr) :
    EApprox n st d env e →
    EApprox (n + 1) st d env (.unary op e)
  | callF (n : Nat) (st : St) (d : Nat) (env : Addr) (f : Expr)
      (args : List Expr) :
    EApprox n st d env f →
    EApprox (n + 1) st d env (.call f args)
  | callArgs (n : Nat) (st : St) (d : Nat) (env : Addr) (f : Expr)
      (args : List Expr) (st' : St) (fv : Value) :
    EvalE st d env f st' fv →
    args.length ≤ maxArgs →
    ArgsApprox n st' d env args →
    EApprox (n + 1) st d env (.call f args)
  | callC (n : Nat) (st : St) (d : Nat) (env : Addr) (f : Expr)
      (args : List Expr) (st' st'' : St) (fv : Value) (vs : List Value) :
    EvalE st d env f st' fv →
    args.length ≤ maxArgs →
    EvalArgs st' d env args st'' vs →
    CApprox n st'' d fv vs →
    EApprox (n + 1) st d env (.call f args)

inductive ArgsApprox : Nat → St → Nat → Addr → List Expr → Prop where
  | zero (st : St) (d : Nat) (env : Addr) (es : List Expr) :
    ArgsApprox 0 st d env es
  | head (n : Nat) (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr) :
    EApprox n st d env e →
    ArgsApprox (n + 1) st d env (e :: es)
  | tail (n : Nat) (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : St) (v : Value) :
    EvalE st d env e st' v →
    ArgsApprox n st' d env es →
    ArgsApprox (n + 1) st d env (e :: es)

inductive CApprox : Nat → St → Nat → Value → List Value → Prop where
  | zero (st : St) (d : Nat) (fv : Value) (vs : List Value) :
    CApprox 0 st d fv vs
  | body (n : Nat) (st : St) (d : Nat) (a : Addr) (cd : ClosureData)
      (vs : List Value) (store' : Store) (frame : Addr) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    Approx n ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st.out⟩ (d + 1) frame cd.body →
    CApprox (n + 1) st d (.closure a) vs

inductive SApprox : Nat → St → Nat → Addr → Stmt → Prop where
  | zero (st : St) (d : Nat) (env : Addr) (s : Stmt) :
    SApprox 0 st d env s
  | expr (n : Nat) (st : St) (d : Nat) (env : Addr) (e : Expr) :
    EApprox n st d env e →
    SApprox (n + 1) st d env (.expr e)
  | varInit (n : Nat) (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) :
    EApprox n st d env e →
    SApprox (n + 1) st d env (.varDecl x (some e))
  | block (n : Nat) (st : St) (d : Nat) (env : Addr) (ss : List Stmt)
      (store' : Store) (inner : Addr) :
    st.store.allocFrame (some env) = (store', inner) →
    Approx n ⟨store', st.out⟩ d inner ss →
    SApprox (n + 1) st d env (.block ss)
  | ifCond (n : Nat) (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) :
    EApprox n st d env c →
    SApprox (n + 1) st d env (.ifStmt c t e)
  | ifThen (n : Nat) (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = true →
    SApprox n st' d env t →
    SApprox (n + 1) st d env (.ifStmt c t e)
  | ifElse (n : Nat) (st : St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
      (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = false →
    SApprox n st' d env e →
    SApprox (n + 1) st d env (.ifStmt c t (some e))
  | whileCond (n : Nat) (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) :
    EApprox n st d env c →
    SApprox (n + 1) st d env (.whileStmt c b)
  | whileBody (n : Nat) (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = true →
    SApprox n st' d env b →
    SApprox (n + 1) st d env (.whileStmt c b)
  | whileLoop (n : Nat) (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v : Value) (status : Status) :
    EvalE st d env c st' v → v.truthy = true →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    SApprox n st'' d env (.whileStmt c b) →
    SApprox (n + 1) st d env (.whileStmt c b)
  | forInit (n : Nat) (st : St) (d : Nat) (env : Addr) (init : Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) :
    st.store.allocFrame (some env) = (store', outer) →
    SApprox n ⟨store', st.out⟩ d outer init →
    SApprox (n + 1) st d env (.forStmt (some init) cnd step b)
  | forLoop (n : Nat) (st : St) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' : St) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    FlApprox n st' d outer cnd step b →
    SApprox (n + 1) st d env (.forStmt init cnd step b)
  | ret (n : Nat) (st : St) (d : Nat) (env : Addr) (e : Expr) :
    EApprox n st d env e →
    SApprox (n + 1) st d env (.ret (some e))

inductive FlApprox : Nat → St → Nat → Addr → Option Expr → Option Expr → Stmt →
    Prop where
  | zero (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) :
    FlApprox 0 st d env cnd step b
  | cond (n : Nat) (st : St) (d : Nat) (env : Addr) (c : Expr)
      (step : Option Expr) (b : Stmt) :
    EApprox n st d env c →
    FlApprox (n + 1) st d env (some c) step b
  | body (n : Nat) (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' : St) :
    ForCond st d env cnd st' →
    SApprox n st' d env b →
    FlApprox (n + 1) st d env cnd step b
  | step (n : Nat) (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (e : Expr) (b : Stmt) (st' st'' : St) (status : Status) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    EApprox n st'' d env e →
    FlApprox (n + 1) st d env cnd (some e) b
  | loop (n : Nat) (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' : St) (status : Status) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    ExecStep st'' d env step st''' →
    FlApprox n st''' d env cnd step b →
    FlApprox (n + 1) st d env cnd step b

inductive Approx : Nat → St → Nat → Addr → List Stmt → Prop where

  | zero (st : St) (d : Nat) (env : Addr) (ss : List Stmt) :
    Approx 0 st d env ss

  | step (n : Nat) (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : St) :
    ExecS st d env s st' .normal →
    Approx n st' d env ss →
    Approx (n + 1) st d env (s :: ss)

  | head (n : Nat) (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) :
    SApprox n st d env s →
    Approx (n + 1) st d env (s :: ss)

end

def BigStepDiverges (p : Program) : Prop :=
  ∀ n, Approx n initSt 0 0 p

def Trichotomy : Prop :=
  ∀ p : Program, (∃ out, BigStep p out) ∨ BigStepErr p ∨ BigStepDiverges p

theorem stuck_of_trichotomy (htri : Trichotomy) (p : Program)
    (hno : ¬ ∃ out, BigStep p out) : BigStepErr p ∨ BigStepDiverges p := by
  rcases htri p with hbs | herr | hdiv
  · exact (hno hbs).elim
  · exact Or.inl herr
  · exact Or.inr hdiv

end Vsa.While
