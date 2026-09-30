import Vsa.While.ErrorSem

namespace Vsa.While.Types

open Vsa.While

inductive Ty where
  | int
  | bool
  | str
  | null

  | native (f : NativeFn)

  | fn (ps : List Ty) (r : Ty)
  deriving Repr

mutual

def Ty.decEq : (a b : Ty) → Decidable (a = b)
  | .int, .int => isTrue rfl
  | .bool, .bool => isTrue rfl
  | .str, .str => isTrue rfl
  | .null, .null => isTrue rfl
  | .native f, .native g =>
    if h : f = g then isTrue (h ▸ rfl) else isFalse fun e => by cases e; exact h rfl
  | .fn ps r, .fn qs u =>
    match Ty.decEqList ps qs, Ty.decEq r u with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h₁, _ => isFalse fun e => by cases e; exact h₁ rfl
    | _, isFalse h₂ => isFalse fun e => by cases e; exact h₂ rfl
  | .int, .bool | .int, .str | .int, .null | .int, .native _ | .int, .fn _ _
  | .bool, .int | .bool, .str | .bool, .null | .bool, .native _ | .bool, .fn _ _
  | .str, .int | .str, .bool | .str, .null | .str, .native _ | .str, .fn _ _
  | .null, .int | .null, .bool | .null, .str | .null, .native _ | .null, .fn _ _
  | .native _, .int | .native _, .bool | .native _, .str | .native _, .null
  | .native _, .fn _ _
  | .fn _ _, .int | .fn _ _, .bool | .fn _ _, .str | .fn _ _, .null
  | .fn _ _, .native _ => isFalse fun e => by cases e

def Ty.decEqList : (a b : List Ty) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse fun e => by cases e
  | _ :: _, [] => isFalse fun e => by cases e
  | t :: ts, u :: us =>
    match Ty.decEq t u, Ty.decEqList ts us with
    | isTrue h₁, isTrue h₂ => isTrue (h₁ ▸ h₂ ▸ rfl)
    | isFalse h₁, _ => isFalse fun e => by cases e; exact h₁ rfl
    | _, isFalse h₂ => isFalse fun e => by cases e; exact h₂ rfl

end

instance : DecidableEq Ty := Ty.decEq

abbrev TyEnv := String → Ty

inductive BinTy : BinOp → Ty → Ty → Ty → Prop where
  | addInt : BinTy .add .int .int .int
  | addStrL (t : Ty) : BinTy .add .str t .str
  | addStrR (t : Ty) : BinTy .add t .str .str
  | sub : BinTy .sub .int .int .int
  | mul : BinTy .mul .int .int .int
  | div : BinTy .div .int .int .int
  | mod : BinTy .mod .int .int .int
  | eq (t u : Ty) : BinTy .eq t u .bool
  | ne (t u : Ty) : BinTy .ne t u .bool
  | cmpInt (op : BinOp) : (op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge) →
      BinTy op .int .int .bool
  | cmpStr (op : BinOp) : (op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge) →
      BinTy op .str .str .bool

inductive CallTy : Ty → List Ty → Ty → Prop where
  | fn (ps : List Ty) (r : Ty) : CallTy (.fn ps r) ps r
  | print (ts : List Ty) : CallTy (.native .print) ts .null
  | println (ts : List Ty) : CallTy (.native .println) ts .null
  | assert1 (t : Ty) : CallTy (.native .assert) [t] .null
  | assert2 (t u : Ty) : CallTy (.native .assert) [t, u] .null

mutual

inductive MustExit : Stmt → Prop where
  | ret (e : Option Expr) : MustExit (.ret e)
  | brk : MustExit .brk
  | cont : MustExit .cont
  | block (ss : List Stmt) : MustExitSeq ss → MustExit (.block ss)
  | ite (c : Expr) (t e : Stmt) : MustExit t → MustExit e →
      MustExit (.ifStmt c t (some e))

inductive MustExitSeq : List Stmt → Prop where
  | head (s : Stmt) (ss : List Stmt) : MustExit s → MustExitSeq (s :: ss)
  | tail (s : Stmt) (ss : List Stmt) : MustExitSeq ss → MustExitSeq (s :: ss)

end

mutual

inductive WtE (Δ : TyEnv) : List String → Expr → Ty → Prop where
  | int (S : List String) (n : Int) : WtE Δ S (.int n) .int
  | str (S : List String) (s : String) : WtE Δ S (.str s) .str
  | bool (S : List String) (b : Bool) : WtE Δ S (.bool b) .bool
  | null (S : List String) : WtE Δ S .null .null
  | var (S : List String) (x : String) : x ∈ S → WtE Δ S (.var x) (Δ x)
  | assign (S : List String) (x : String) (e : Expr) :
      x ∈ S → WtE Δ S e (Δ x) → WtE Δ S (.assign x e) (Δ x)
  | binary (S : List String) (op : BinOp) (l r : Expr) (tl tr t : Ty) :
      WtE Δ S l tl → WtE Δ S r tr → BinTy op tl tr t →
      WtE Δ S (.binary op l r) t
  | logical (S : List String) (op : LogOp) (l r : Expr) (tl tr : Ty) :
      WtE Δ S l tl → WtE Δ S r tr → WtE Δ S (.logical op l r) .bool
  | neg (S : List String) (e : Expr) :
      WtE Δ S e .int → WtE Δ S (.unary .neg e) .int
  | not (S : List String) (e : Expr) (t : Ty) :
      WtE Δ S e t → WtE Δ S (.unary .not e) .bool
  | call (S : List String) (f : Expr) (args : List Expr) (tf : Ty)
      (ts : List Ty) (t : Ty) :
      WtE Δ S f tf → args.length ≤ maxArgs → WtArgs Δ S args ts →
      CallTy tf ts t → WtE Δ S (.call f args) t
  | fn (S : List String) (name : Option String) (params : List String)
      (body : List Stmt) (r : Ty) (S' : List String) :
      WtSeq Δ (params ++ S) (some r) false body S' →
      (r = .null ∨ MustExitSeq body) →
      WtE Δ S (.fn name params body) (.fn (params.map Δ) r)

inductive WtArgs (Δ : TyEnv) : List String → List Expr → List Ty → Prop where
  | nil (S : List String) : WtArgs Δ S [] []
  | cons (S : List String) (e : Expr) (es : List Expr) (t : Ty) (ts : List Ty) :
      WtE Δ S e t → WtArgs Δ S es ts → WtArgs Δ S (e :: es) (t :: ts)

inductive WtS (Δ : TyEnv) : List String → Option Ty → Bool → Stmt →
    List String → Prop where
  | expr (S : List String) (R : Option Ty) (L : Bool) (e : Expr) (t : Ty) :
      WtE Δ S e t → WtS Δ S R L (.expr e) S
  | varNull (S : List String) (R : Option Ty) (L : Bool) (x : String) :
      Δ x = .null → WtS Δ S R L (.varDecl x none) (x :: S)
  | varInit (S : List String) (R : Option Ty) (L : Bool) (x : String) (e : Expr) :
      WtE Δ S e (Δ x) → WtS Δ S R L (.varDecl x (some e)) (x :: S)

  | varRec (S : List String) (R : Option Ty) (L : Bool) (x : String)
      (name : Option String) (params : List String) (body : List Stmt)
      (r : Ty) (S' : List String) :
      WtSeq Δ (params ++ x :: S) (some r) false body S' →
      (r = .null ∨ MustExitSeq body) →
      Δ x = .fn (params.map Δ) r →
      WtS Δ S R L (.varDecl x (some (.fn name params body))) (x :: S)
  | block (S : List String) (R : Option Ty) (L : Bool) (ss : List Stmt)
      (S' : List String) :
      WtSeq Δ S R L ss S' → WtS Δ S R L (.block ss) S
  | ifSome (S : List String) (R : Option Ty) (L : Bool) (c : Expr) (t e : Stmt)
      (tc : Ty) (S₁ S₂ : List String) :
      WtE Δ S c tc → WtS Δ S R L t S₁ → WtS Δ S R L e S₂ →
      WtS Δ S R L (.ifStmt c t (some e)) S
  | ifNone (S : List String) (R : Option Ty) (L : Bool) (c : Expr) (t : Stmt)
      (tc : Ty) (S₁ : List String) :
      WtE Δ S c tc → WtS Δ S R L t S₁ → WtS Δ S R L (.ifStmt c t none) S
  | whileS (S : List String) (R : Option Ty) (L : Bool) (c : Expr) (b : Stmt)
      (tc : Ty) (S₁ : List String) :
      WtE Δ S c tc → WtS Δ S R true b S₁ → WtS Δ S R L (.whileStmt c b) S
  | forS (S : List String) (R : Option Ty) (L : Bool) (init : Option Stmt)
      (cnd step : Option Expr) (b : Stmt) (S₁ S₂ : List String) :
      WtInit Δ S R L init S₁ → WtEO Δ S₁ cnd → WtEO Δ S₁ step →
      WtS Δ S₁ R true b S₂ → WtS Δ S R L (.forStmt init cnd step b) S
  | ret (S : List String) (L : Bool) (e : Expr) (t : Ty) :
      WtE Δ S e t → WtS Δ S (some t) L (.ret (some e)) S
  | retNull (S : List String) (L : Bool) : WtS Δ S (some .null) L (.ret none) S
  | brk (S : List String) (R : Option Ty) : WtS Δ S R true .brk S
  | cont (S : List String) (R : Option Ty) : WtS Δ S R true .cont S

inductive WtInit (Δ : TyEnv) : List String → Option Ty → Bool → Option Stmt →
    List String → Prop where
  | none (S : List String) (R : Option Ty) (L : Bool) : WtInit Δ S R L none S
  | some (S : List String) (R : Option Ty) (L : Bool) (s : Stmt)
      (S' : List String) :
      WtS Δ S R L s S' → WtInit Δ S R L (some s) S'

inductive WtEO (Δ : TyEnv) : List String → Option Expr → Prop where
  | none (S : List String) : WtEO Δ S none
  | some (S : List String) (e : Expr) (t : Ty) : WtE Δ S e t → WtEO Δ S (some e)

inductive WtSeq (Δ : TyEnv) : List String → Option Ty → Bool → List Stmt →
    List String → Prop where
  | nil (S : List String) (R : Option Ty) (L : Bool) : WtSeq Δ S R L [] S
  | cons (S : List String) (R : Option Ty) (L : Bool) (s : Stmt)
      (ss : List Stmt) (S₁ S₂ : List String) :
      WtS Δ S R L s S₁ → WtSeq Δ S₁ R L ss S₂ → WtSeq Δ S R L (s :: ss) S₂

end

def builtinNames : List String := ["print", "println", "assert"]

structure BuiltinsTyped (Δ : TyEnv) : Prop where
  print : Δ "print" = .native .print
  println : Δ "println" = .native .println
  assert : Δ "assert" = .native .assert

structure WellTyped (Δ : TyEnv) (p : Program) : Prop where
  builtins : BuiltinsTyped Δ
  body : ∃ S', WtSeq Δ builtinNames none false p S'

def Defined (s : Store) (a : Addr) (x : String) : Prop :=
  ∃ v, s.get? a x = some v

def DefAll (s : Store) (a : Addr) (S : List String) : Prop :=
  ∀ x ∈ S, Defined s a x

inductive ValTy (Δ : TyEnv) (s : Store) : Value → Ty → Prop where
  | null : ValTy Δ s .null .null
  | bool (b : Bool) : ValTy Δ s (.bool b) .bool
  | int (n : Int) : ValTy Δ s (.int n) .int
  | str (x : String) : ValTy Δ s (.str x) .str
  | native (f : NativeFn) : ValTy Δ s (.native f) (.native f)
  | closure (a : Addr) (cd : ClosureData) (S S' : List String) (r : Ty) :
      s.closures[a]? = some cd →
      WtSeq Δ (cd.params ++ S) (some r) false cd.body S' →
      (r = .null ∨ MustExitSeq cd.body) →
      DefAll s cd.env S →
      ValTy Δ s (.closure a) (.fn (cd.params.map Δ) r)

inductive ValTys (Δ : TyEnv) (s : Store) : List Value → List Ty → Prop where
  | nil : ValTys Δ s [] []
  | cons (v : Value) (vs : List Value) (t : Ty) (ts : List Ty) :
      ValTy Δ s v t → ValTys Δ s vs ts → ValTys Δ s (v :: vs) (t :: ts)

def StoreOK (Δ : TyEnv) (s : Store) : Prop :=
  ∀ (a : Addr) (f : Frame), s.frames[a]? = some f → ∀ p ∈ f.vars, ValTy Δ s p.2 (Δ p.1)

def StatusOK (Δ : TyEnv) (s : Store) (R : Option Ty) (L : Bool) : Status → Prop
  | .normal => True
  | .brk => L = true
  | .cont => L = true
  | .ret v => ∃ t, R = some t ∧ ValTy Δ s v t

structure Ext (s s' : Store) : Prop where
  size_le : s.frames.size ≤ s'.frames.size
  frames : ∀ (a : Addr) (f : Frame), s.frames[a]? = some f → ∃ f' : Frame, s'.frames[a]? = some f' ∧
    f'.parent = f.parent ∧
    ∀ x, f.vars.any (·.1 == x) = true → f'.vars.any (·.1 == x) = true
  closures : ∀ (a : Addr) (cd : ClosureData), s.closures[a]? = some cd → s'.closures[a]? = some cd

mutual

inductive EvalErrN : St → Nat → Addr → Expr → Prop where
  | assignE (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) :
    EvalErrN st d env e → EvalErrN st d env (.assign x e)
  | binaryL (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) :
    EvalErrN st d env l → EvalErrN st d env (.binary op l r)
  | binaryR (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' : St) (lv : Value) :
    EvalE st d env l st' lv → EvalErrN st' d env r →
    EvalErrN st d env (.binary op l r)

  | divZero (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : St) (lv : Value) :
    (op = .div ∨ op = .mod) →
    EvalE st d env l st' lv → EvalE st' d env r st'' (.int 0) →
    EvalErrN st d env (.binary op l r)
  | orL (st : St) (d : Nat) (env : Addr) (l r : Expr) :
    EvalErrN st d env l → EvalErrN st d env (.logical .or l r)
  | orR (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St) (lv : Value) :
    EvalE st d env l st' lv → lv.truthy = false → EvalErrN st' d env r →
    EvalErrN st d env (.logical .or l r)
  | andL (st : St) (d : Nat) (env : Addr) (l r : Expr) :
    EvalErrN st d env l → EvalErrN st d env (.logical .and l r)
  | andR (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St) (lv : Value) :
    EvalE st d env l st' lv → lv.truthy = true → EvalErrN st' d env r →
    EvalErrN st d env (.logical .and l r)
  | unaryE (st : St) (d : Nat) (env : Addr) (op : UnOp) (e : Expr) :
    EvalErrN st d env e → EvalErrN st d env (.unary op e)
  | callF (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr) :
    EvalErrN st d env f → EvalErrN st d env (.call f args)
  | callArgs (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : St) (fv : Value) :
    EvalE st d env f st' fv → args.length ≤ maxArgs →
    EvalArgsErrN st' d env args → EvalErrN st d env (.call f args)
  | callC (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : St) (fv : Value) (vs : List Value) :
    EvalE st d env f st' fv → args.length ≤ maxArgs →
    EvalArgs st' d env args st'' vs → CallErrN st'' d fv vs →
    EvalErrN st d env (.call f args)

inductive EvalArgsErrN : St → Nat → Addr → List Expr → Prop where
  | head (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr) :
    EvalErrN st d env e → EvalArgsErrN st d env (e :: es)
  | tail (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : St) (v : Value) :
    EvalE st d env e st' v → EvalArgsErrN st' d env es →
    EvalArgsErrN st d env (e :: es)

inductive CallErrN : St → Nat → Value → List Value → Prop where

  | depth (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) :
    st.store.closures[a]? = some cd → vs.length = cd.params.length →
    ¬ d < maxCallDepth → CallErrN st d (.closure a) vs
  | body (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) :
    st.store.closures[a]? = some cd → vs.length = cd.params.length →
    d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeqErrN ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st.out⟩ (d + 1) frame cd.body →
    CallErrN st d (.closure a) vs

  | assertFail (st : St) (d : Nat) (vs : List Value) (v m : Value) :
    (vs = [v] ∨ vs = [v, m]) → v.truthy = false →
    CallErrN st d (.native .assert) vs

inductive ExecErrN : St → Nat → Addr → Stmt → Prop where
  | expr (st : St) (d : Nat) (env : Addr) (e : Expr) :
    EvalErrN st d env e → ExecErrN st d env (.expr e)
  | varInit (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) :
    EvalErrN st d env e → ExecErrN st d env (.varDecl x (some e))
  | block (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr) :
    st.store.allocFrame (some env) = (store', inner) →
    ExecSeqErrN ⟨store', st.out⟩ d inner ss → ExecErrN st d env (.block ss)
  | ifCond (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) :
    EvalErrN st d env c → ExecErrN st d env (.ifStmt c t e)
  | ifThen (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = true → ExecErrN st' d env t →
    ExecErrN st d env (.ifStmt c t e)
  | ifElse (st : St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
      (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = false → ExecErrN st' d env e →
    ExecErrN st d env (.ifStmt c t (some e))
  | whileCond (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt) :
    EvalErrN st d env c → ExecErrN st d env (.whileStmt c b)
  | whileBody (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = true → ExecErrN st' d env b →
    ExecErrN st d env (.whileStmt c b)
  | whileLoop (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v : Value) (status : Status) :
    EvalE st d env c st' v → v.truthy = true → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → ExecErrN st'' d env (.whileStmt c b) →
    ExecErrN st d env (.whileStmt c b)
  | forInit (st : St) (d : Nat) (env : Addr) (init : Stmt) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecErrN ⟨store', st.out⟩ d outer init →
    ExecErrN st d env (.forStmt (some init) cnd step b)
  | forLoop (st : St) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' : St) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    ForLoopErrN st' d outer cnd step b →
    ExecErrN st d env (.forStmt init cnd step b)
  | ret (st : St) (d : Nat) (env : Addr) (e : Expr) :
    EvalErrN st d env e → ExecErrN st d env (.ret (some e))

inductive ForLoopErrN : St → Nat → Addr → Option Expr → Option Expr → Stmt →
    Prop where
  | cond (st : St) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr)
      (b : Stmt) :
    EvalErrN st d env c → ForLoopErrN st d env (some c) step b
  | body (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' : St) :
    ForCond st d env cnd st' → ExecErrN st' d env b →
    ForLoopErrN st d env cnd step b
  | step (st : St) (d : Nat) (env : Addr) (cnd : Option Expr) (e : Expr)
      (b : Stmt) (st' st'' : St) (status : Status) :
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → EvalErrN st'' d env e →
    ForLoopErrN st d env cnd (some e) b
  | loop (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' : St) (status : Status) :
    ForCond st d env cnd st' → ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
    ForLoopErrN st''' d env cnd step b → ForLoopErrN st d env cnd step b

inductive ExecSeqErrN : St → Nat → Addr → List Stmt → Prop where
  | head (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) :
    ExecErrN st d env s → ExecSeqErrN st d env (s :: ss)
  | tail (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : St) :
    ExecS st d env s st' .normal → ExecSeqErrN st' d env ss →
    ExecSeqErrN st d env (s :: ss)

end

end Vsa.While.Types
