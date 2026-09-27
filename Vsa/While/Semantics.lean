import Vsa.While.Ast

namespace Vsa.While

abbrev Addr := Nat

inductive NativeFn where
  | print | println | assert
  deriving Repr, DecidableEq

inductive Value where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | closure (a : Addr)
  | native (f : NativeFn)
  deriving Repr, DecidableEq

structure ClosureData where
  env : Addr
  name : Option String
  params : List String
  body : List Stmt
  deriving Repr

structure Frame where
  parent : Option Addr
  vars : List (String × Value)
  deriving Repr

structure Store where
  frames : Array Frame
  closures : Array ClosureData
  deriving Repr

structure St where
  store : Store
  out : String
  deriving Repr

inductive Status where
  | normal | brk | cont | ret (v : Value)
  deriving Repr, DecidableEq

namespace Store

def allocFrame (s : Store) (parent : Option Addr) : Store × Addr :=
  ({ s with frames := s.frames.push ⟨parent, []⟩ }, s.frames.size)

def allocClosure (s : Store) (c : ClosureData) : Store × Addr :=
  ({ s with closures := s.closures.push c }, s.closures.size)

def define (s : Store) (a : Addr) (x : String) (v : Value) : Store :=
  { s with
    frames := s.frames.modify a fun f =>
      { f with vars :=
          if f.vars.any (·.1 == x) then
            f.vars.map fun p => if p.1 == x then (x, v) else p
          else
            f.vars ++ [(x, v)] } }

def lookup (s : Store) : (gas : Nat) → Addr → String → Option Value
  | 0, _, _ => none
  | gas + 1, a, x => do
    let f ← s.frames[a]?
    match f.vars.find? (·.1 == x) with
    | some (_, v) => some v
    | none => match f.parent with
      | some p => s.lookup gas p x
      | none => none

def set (s : Store) : (gas : Nat) → Addr → String → Value → Option Store
  | 0, _, _, _ => none
  | gas + 1, a, x, v => do
    let f ← s.frames[a]?
    if f.vars.any (·.1 == x) then
      some { s with
        frames := s.frames.modify a fun f =>
          { f with vars := f.vars.map fun p => if p.1 == x then (x, v) else p } }
    else match f.parent with
      | some p => s.set gas p x v
      | none => none

end Store

def Store.get? (s : Store) (a : Addr) (x : String) : Option Value :=
  s.lookup s.frames.size a x

def Store.set? (s : Store) (a : Addr) (x : String) (v : Value) : Option Store :=
  s.set s.frames.size a x v

def Value.truthy : Value → Bool
  | .null => false
  | .bool b => b
  | .int n => n != 0
  | _ => true

def Value.equal : Value → Value → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .str a, .str b => a == b
  | .closure a, .closure b => a == b
  | .native a, .native b => a == b
  | _, _ => false

def natDigits : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n =>
    if n < 10 then [Nat.digitChar n]
    else natDigits fuel (n / 10) ++ [Nat.digitChar (n % 10)]

def natToString (n : Nat) : String := (natDigits (n + 1) n).foldl .push ""

def intToString : Int → String
  | .ofNat m => natToString m
  | .negSucc m => "-" ++ natToString (m + 1)

def Value.display (s : Store) : Value → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .int n => intToString n
  | .str s0 => s0
  | .closure a =>
    match s.closures[a]? with
    | some c => match c.name with
      | some n => s!"<fn {n}>"
      | none => "<fn>"
    | none => "<fn>"
  | .native .print => "<native fn print>"
  | .native .println => "<native fn println>"
  | .native .assert => "<native fn assert>"

def printArgs (s : Store) (args : List Value) : String :=
  String.intercalate " " (args.map (Value.display s))

def fnCatRender (n : String) : String := String.ofList (("<fn " ++ n ++ ">").toList.take 63)

def Value.catDisplay (s : Store) : Value → String
  | .native _ => "<native fn>"
  | .closure a =>
    match s.closures[a]? with
    | some c => match c.name with
      | some n => fnCatRender n
      | none => "<fn>"
    | none => "<fn>"
  | v => v.display s

def wrap64 (z : Int) : Int := (BitVec.ofInt 64 z).toInt

theorem wrap64_toInt (v : BitVec 64) : wrap64 v.toInt = v.toInt := by
  unfold wrap64; rw [BitVec.ofInt_toInt]

theorem wrap64_tdiv_min : wrap64 ((-2^63 : Int).tdiv (-1)) = -2^63 := by decide

def binOpSem (s : Store) : BinOp → Value → Value → Option Value
  | .add, l, r =>
    match l, r with
    | .str _, _ | _, .str _ => some (.str (l.catDisplay s ++ r.catDisplay s))
    | .int a, .int b => some (.int (wrap64 (a + b)))
    | _, _ => none
  | .sub, .int a, .int b => some (.int (wrap64 (a - b)))
  | .mul, .int a, .int b => some (.int (wrap64 (a * b)))
  | .div, .int a, .int b => if b == 0 then none else some (.int (wrap64 (a.tdiv b)))
  | .mod, .int a, .int b => if b == 0 then none else some (.int (wrap64 (a.tmod b)))
  | .eq, l, r => some (.bool (l.equal r))
  | .ne, l, r => some (.bool (!(l.equal r)))
  | .lt, .str a, .str b => some (.bool (a < b))
  | .le, .str a, .str b => some (.bool (a < b || a == b))
  | .gt, .str a, .str b => some (.bool (b < a))
  | .ge, .str a, .str b => some (.bool (b < a || a == b))
  | .lt, .int a, .int b => some (.bool (a < b))
  | .le, .int a, .int b => some (.bool (a ≤ b))
  | .gt, .int a, .int b => some (.bool (a > b))
  | .ge, .int a, .int b => some (.bool (a ≥ b))
  | _, _, _ => none

def maxCallDepth : Nat := 1000

def maxArgs : Nat := 32

mutual

inductive EvalE : St → Nat → Addr → Expr → St → Value → Prop where
  | int (st : St) (d : Nat) (env : Addr) (n : Int) :
    EvalE st d env (.int n) st (.int n)
  | str (st : St) (d : Nat) (env : Addr) (s : String) :
    EvalE st d env (.str s) st (.str s)
  | bool (st : St) (d : Nat) (env : Addr) (b : Bool) :
    EvalE st d env (.bool b) st (.bool b)
  | null (st : St) (d : Nat) (env : Addr) :
    EvalE st d env .null st .null
  | var (st : St) (d : Nat) (env : Addr) (x : String) (v : Value) :
    st.store.get? env x = some v →
    EvalE st d env (.var x) st v
  | assign (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St)
      (v : Value) (store'' : Store) :
    EvalE st d env e st' v →
    st'.store.set? env x v = some store'' →
    EvalE st d env (.assign x e) ⟨store'', st'.out⟩ v
  | binary (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : St) (lv rv v : Value) :
    EvalE st d env l st' lv →
    EvalE st' d env r st'' rv →
    binOpSem st''.store op lv rv = some v →
    EvalE st d env (.binary op l r) st'' v
  | orTrue (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) :
    EvalE st d env l st' lv → lv.truthy = true →
    EvalE st d env (.logical .or l r) st' (.bool true)
  | orFalse (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St)
      (lv rv : Value) :
    EvalE st d env l st' lv → lv.truthy = false →
    EvalE st' d env r st'' rv →
    EvalE st d env (.logical .or l r) st'' (.bool rv.truthy)
  | andFalse (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) :
    EvalE st d env l st' lv → lv.truthy = false →
    EvalE st d env (.logical .and l r) st' (.bool false)
  | andTrue (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St)
      (lv rv : Value) :
    EvalE st d env l st' lv → lv.truthy = true →
    EvalE st' d env r st'' rv →
    EvalE st d env (.logical .and l r) st'' (.bool rv.truthy)
  | neg (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (n : Int) :
    EvalE st d env e st' (.int n) →
    EvalE st d env (.unary .neg e) st' (.int (wrap64 (-n)))
  | not (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) :
    EvalE st d env e st' v →
    EvalE st d env (.unary .not e) st' (.bool (!v.truthy))
  | call (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' st''' : St) (fv : Value) (vs : List Value) (v : Value) :
    EvalE st d env f st' fv →
    args.length ≤ maxArgs →
    EvalArgs st' d env args st'' vs →
    Call st'' d fv vs st''' v →
    EvalE st d env (.call f args) st''' v
  | fn (st : St) (d : Nat) (env : Addr) (name : Option String)
      (params : List String) (body : List Stmt) (store' : Store) (a : Addr) :
    st.store.allocClosure ⟨env, name, params, body⟩ = (store', a) →
    EvalE st d env (.fn name params body) ⟨store', st.out⟩ (.closure a)

inductive EvalArgs : St → Nat → Addr → List Expr → St → List Value → Prop where
  | nil (st : St) (d : Nat) (env : Addr) : EvalArgs st d env [] st []
  | cons (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' st'' : St) (v : Value) (vs : List Value) :
    EvalE st d env e st' v →
    EvalArgs st' d env es st'' vs →
    EvalArgs st d env (e :: es) st'' (v :: vs)

inductive Call : St → Nat → Value → List Value → St → Value → Prop where
  | closure (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : St) (status : Status)
      (v : Value) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st.out⟩ (d + 1) frame cd.body st' status →
    (status = .normal ∧ v = .null ∨ status = .ret v) →
    Call st d (.closure a) vs st' v
  | print (st : St) (d : Nat) (vs : List Value) :
    Call st d (.native .print) vs
      ⟨st.store, st.out ++ printArgs st.store vs⟩ .null
  | println (st : St) (d : Nat) (vs : List Value) :
    Call st d (.native .println) vs
      ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null
  | assertOk (st : St) (d : Nat) (vs : List Value) (v m : Value) :
    (vs = [v] ∨ vs = [v, m]) →
    v.truthy = true →
    Call st d (.native .assert) vs st .null

inductive ExecS : St → Nat → Addr → Stmt → St → Status → Prop where
  | expr (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) :
    EvalE st d env e st' v →
    ExecS st d env (.expr e) st' .normal
  | varInit (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St)
      (v : Value) :
    EvalE st d env e st' v →
    ExecS st d env (.varDecl x (some e))
      ⟨st'.store.define env x v, st'.out⟩ .normal
  | varNull (st : St) (d : Nat) (env : Addr) (x : String) :
    ExecS st d env (.varDecl x none)
      ⟨st.store.define env x .null, st.out⟩ .normal
  | block (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr) (st' : St) (status : Status) :
    st.store.allocFrame (some env) = (store', inner) →
    ExecSeq ⟨store', st.out⟩ d inner ss st' status →
    ExecS st d env (.block ss) st' status
  | ifTrue (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) (st' st'' : St) (v : Value) (status : Status) :
    EvalE st d env c st' v → v.truthy = true →
    ExecS st' d env t st'' status →
    ExecS st d env (.ifStmt c t e) st'' status
  | ifFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
      (st' st'' : St) (v : Value) (status : Status) :
    EvalE st d env c st' v → v.truthy = false →
    ExecS st' d env e st'' status →
    ExecS st d env (.ifStmt c t (some e)) st'' status
  | ifNone (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : St)
      (v : Value) :
    EvalE st d env c st' v → v.truthy = false →
    ExecS st d env (.ifStmt c t none) st' .normal
  | whileFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = false →
    ExecS st d env (.whileStmt c b) st' .normal
  | whileBreak (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = true →
    ExecS st' d env b st'' .brk →
    ExecS st d env (.whileStmt c b) st'' .normal
  | whileRet (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v rv : Value) :
    EvalE st d env c st' v → v.truthy = true →
    ExecS st' d env b st'' (.ret rv) →
    ExecS st d env (.whileStmt c b) st'' (.ret rv)
  | whileLoop (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' st''' : St) (v : Value) (status status' : Status) :
    EvalE st d env c st' v → v.truthy = true →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    ExecS st'' d env (.whileStmt c b) st''' status' →
    ExecS st d env (.whileStmt c b) st''' status'
  | forStart (st : St) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' st'' : St) (status : Status) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    ForLoop st' d outer cnd step b st'' status →
    ExecS st d env (.forStmt init cnd step b) st'' status
  | ret (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) :
    EvalE st d env e st' v →
    ExecS st d env (.ret (some e)) st' (.ret v)
  | retNull (st : St) (d : Nat) (env : Addr) :
    ExecS st d env (.ret none) st (.ret .null)
  | brk (st : St) (d : Nat) (env : Addr) : ExecS st d env .brk st .brk
  | cont (st : St) (d : Nat) (env : Addr) : ExecS st d env .cont st .cont

inductive ExecInit : St → Nat → Addr → Option Stmt → St → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ExecInit st d env none st
  | some (st : St) (d : Nat) (env : Addr) (s : Stmt) (st' : St) (status : Status) :
    ExecS st d env s st' status →
    ExecInit st d env (some s) st'

inductive ForLoop : St → Nat → Addr → Option Expr → Option Expr → Stmt → St →
    Status → Prop where
  | condFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr)
      (b : Stmt) (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = false →
    ForLoop st d env (some c) step b st' .normal
  | bodyBreak (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' : St) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' .brk →
    ForLoop st d env cnd step b st'' .normal
  | bodyRet (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' : St) (rv : Value) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' (.ret rv) →
    ForLoop st d env cnd step b st'' (.ret rv)
  | loop (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : St)
      (status status' : Status) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    ExecStep st'' d env step st''' →
    ForLoop st''' d env cnd step b st'''' status' →
    ForLoop st d env cnd step b st'''' status'

inductive ForCond : St → Nat → Addr → Option Expr → St → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ForCond st d env none st
  | some (st : St) (d : Nat) (env : Addr) (c : Expr) (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = true →
    ForCond st d env (some c) st'

inductive ExecStep : St → Nat → Addr → Option Expr → St → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ExecStep st d env none st
  | some (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) :
    EvalE st d env e st' v →
    ExecStep st d env (some e) st'

inductive ExecSeq : St → Nat → Addr → List Stmt → St → Status → Prop where
  | nil (st : St) (d : Nat) (env : Addr) : ExecSeq st d env [] st .normal
  | consNormal (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' st'' : St) (status : Status) :
    ExecS st d env s st' .normal →
    ExecSeq st' d env ss st'' status →
    ExecSeq st d env (s :: ss) st'' status
  | consAbrupt (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : St) (status : Status) :
    ExecS st d env s st' status →
    status ≠ .normal →
    ExecSeq st d env (s :: ss) st' status

end

def initSt : St :=
  { store :=
      { frames := #[⟨none, [("print", .native .print), ("println", .native .println),
          ("assert", .native .assert)]⟩]
        closures := #[] }
    out := "" }

def BigStep (p : Program) (out : String) : Prop :=
  ∃ st', ExecSeq initSt 0 0 p st' .normal ∧ st'.out = out

end Vsa.While
