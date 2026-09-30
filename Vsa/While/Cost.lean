import Vsa.While.Semantics

namespace Vsa.While

def roundUp16 (n : Nat) : Nat := (n + 15) / 16 * 16

def envBytes : Nat := 32

def closureBytes : Nat := 16

def nameCopyCost (x : String) : Nat := roundUp16 (x.length + 1)

def arrayReallocCost (cap : Nat) : Nat := roundUp16 (32 * cap)

def arrayCostAux : (fuel cap k : Nat) → Nat
  | 0, _, _ => 0
  | fuel + 1, cap, k =>
    if k ≤ cap then 0
    else
      let cap' := if cap = 0 then 8 else 2 * cap
      arrayReallocCost cap' + arrayCostAux fuel cap' k

def arrayCost (k : Nat) : Nat := arrayCostAux k 0 k

def defineCost (store : Store) (a : Addr) (x : String) : Nat :=
  match store.frames[a]? with
  | none => 0
  | some f =>
    if f.vars.any (·.1 == x) then 0
    else
      let c := f.vars.length
      let growth :=

        if c = 0 then arrayReallocCost 8
        else if arrayCostAux (c + 1) 0 (c + 1) ≠ arrayCostAux c 0 c then

          arrayCostAux (c + 1) 0 (c + 1) - arrayCostAux c 0 c
        else 0
      nameCopyCost x + growth

def stringifyCost (store : Store) (v : Value) : Nat :=
  roundUp16 ((v.catDisplay store).length + 1)

def concatCost (store : Store) (lv rv : Value) : Nat :=
  stringifyCost store lv + stringifyCost store rv +
    roundUp16 ((lv.catDisplay store).length + (rv.catDisplay store).length + 1)

def binOpCost (store : Store) (op : BinOp) (lv rv : Value) : Nat :=
  match op, lv, rv with
  | .add, .str _, _ => concatCost store lv rv
  | .add, _, .str _ => concatCost store lv rv
  | _, _, _ => 0

def bindParamsCost : Store → Addr → List (String × Value) → Nat
  | _, _, [] => 0
  | store, frame, (x, v) :: rest =>
    defineCost store frame x + bindParamsCost (store.define frame x v) frame rest

mutual

inductive EvalECost : St → Nat → Addr → Expr → St → Value → Nat → Prop where
  | int (st : St) (d : Nat) (env : Addr) (n : Int) :
    EvalECost st d env (.int n) st (.int n) 0
  | str (st : St) (d : Nat) (env : Addr) (s : String) :
    EvalECost st d env (.str s) st (.str s) 0
  | bool (st : St) (d : Nat) (env : Addr) (b : Bool) :
    EvalECost st d env (.bool b) st (.bool b) 0
  | null (st : St) (d : Nat) (env : Addr) :
    EvalECost st d env .null st .null 0
  | var (st : St) (d : Nat) (env : Addr) (x : String) (v : Value) :
    st.store.get? env x = some v →
    EvalECost st d env (.var x) st v 0
  | assign (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St)
      (v : Value) (store'' : Store) (n : Nat) :
    EvalECost st d env e st' v n →
    st'.store.set? env x v = some store'' →
    EvalECost st d env (.assign x e) ⟨store'', st'.out⟩ v n
  | binary (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : St) (lv rv v : Value) (nl nr : Nat) :
    EvalECost st d env l st' lv nl →
    EvalECost st' d env r st'' rv nr →
    binOpSem st''.store op lv rv = some v →
    EvalECost st d env (.binary op l r) st'' v (nl + nr + binOpCost st''.store op lv rv)
  | orTrue (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) (n : Nat) :
    EvalECost st d env l st' lv n → lv.truthy = true →
    EvalECost st d env (.logical .or l r) st' (.bool true) n
  | orFalse (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St)
      (lv rv : Value) (nl nr : Nat) :
    EvalECost st d env l st' lv nl → lv.truthy = false →
    EvalECost st' d env r st'' rv nr →
    EvalECost st d env (.logical .or l r) st'' (.bool rv.truthy) (nl + nr)
  | andFalse (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) (n : Nat) :
    EvalECost st d env l st' lv n → lv.truthy = false →
    EvalECost st d env (.logical .and l r) st' (.bool false) n
  | andTrue (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St)
      (lv rv : Value) (nl nr : Nat) :
    EvalECost st d env l st' lv nl → lv.truthy = true →
    EvalECost st' d env r st'' rv nr →
    EvalECost st d env (.logical .and l r) st'' (.bool rv.truthy) (nl + nr)
  | neg (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (n : Int)
      (m : Nat) :
    EvalECost st d env e st' (.int n) m →
    EvalECost st d env (.unary .neg e) st' (.int (wrap64 (-n))) m
  | not (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value)
      (m : Nat) :
    EvalECost st d env e st' v m →
    EvalECost st d env (.unary .not e) st' (.bool (!v.truthy)) m
  | call (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' st''' : St) (fv : Value) (vs : List Value) (v : Value)
      (nf na nc : Nat) :
    EvalECost st d env f st' fv nf →
    args.length ≤ maxArgs →
    EvalArgsCost st' d env args st'' vs na →
    CallCost st'' d fv vs st''' v nc →
    EvalECost st d env (.call f args) st''' v (nf + na + nc)
  | fn (st : St) (d : Nat) (env : Addr) (name : Option String)
      (params : List String) (body : List Stmt) (store' : Store) (a : Addr) :
    st.store.allocClosure ⟨env, name, params, body⟩ = (store', a) →
    EvalECost st d env (.fn name params body) ⟨store', st.out⟩ (.closure a) closureBytes

inductive EvalArgsCost : St → Nat → Addr → List Expr → St → List Value → Nat → Prop where
  | nil (st : St) (d : Nat) (env : Addr) : EvalArgsCost st d env [] st [] 0
  | cons (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' st'' : St) (v : Value) (vs : List Value) (ne nes : Nat) :
    EvalECost st d env e st' v ne →
    EvalArgsCost st' d env es st'' vs nes →
    EvalArgsCost st d env (e :: es) st'' (v :: vs) (ne + nes)

inductive CallCost : St → Nat → Value → List Value → St → Value → Nat → Prop where
  | closure (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : St) (status : Status)
      (v : Value) (nb : Nat) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeqCost ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st.out⟩ (d + 1) frame cd.body st' status nb →
    (status = .normal ∧ v = .null ∨ status = .ret v) →
    CallCost st d (.closure a) vs st' v
      (envBytes + bindParamsCost store' frame (cd.params.zip vs) + nb)
  | print (st : St) (d : Nat) (vs : List Value) :
    CallCost st d (.native .print) vs
      ⟨st.store, st.out ++ printArgs st.store vs⟩ .null 0
  | println (st : St) (d : Nat) (vs : List Value) :
    CallCost st d (.native .println) vs
      ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null 0
  | assertOk (st : St) (d : Nat) (vs : List Value) (v m : Value) :
    (vs = [v] ∨ vs = [v, m]) →
    v.truthy = true →
    CallCost st d (.native .assert) vs st .null 0

inductive ExecSCost : St → Nat → Addr → Stmt → St → Status → Nat → Prop where
  | expr (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value)
      (n : Nat) :
    EvalECost st d env e st' v n →
    ExecSCost st d env (.expr e) st' .normal n
  | varInit (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St)
      (v : Value) (n : Nat) :
    EvalECost st d env e st' v n →
    ExecSCost st d env (.varDecl x (some e))
      ⟨st'.store.define env x v, st'.out⟩ .normal (n + defineCost st'.store env x)
  | varNull (st : St) (d : Nat) (env : Addr) (x : String) :
    ExecSCost st d env (.varDecl x none)
      ⟨st.store.define env x .null, st.out⟩ .normal (defineCost st.store env x)
  | block (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr) (st' : St) (status : Status) (n : Nat) :
    st.store.allocFrame (some env) = (store', inner) →
    ExecSeqCost ⟨store', st.out⟩ d inner ss st' status n →
    ExecSCost st d env (.block ss) st' status (envBytes + n)
  | ifTrue (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) (st' st'' : St) (v : Value) (status : Status)
      (nc nt : Nat) :
    EvalECost st d env c st' v nc → v.truthy = true →
    ExecSCost st' d env t st'' status nt →
    ExecSCost st d env (.ifStmt c t e) st'' status (nc + nt)
  | ifFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
      (st' st'' : St) (v : Value) (status : Status) (nc ne : Nat) :
    EvalECost st d env c st' v nc → v.truthy = false →
    ExecSCost st' d env e st'' status ne →
    ExecSCost st d env (.ifStmt c t (some e)) st'' status (nc + ne)
  | ifNone (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : St)
      (v : Value) (nc : Nat) :
    EvalECost st d env c st' v nc → v.truthy = false →
    ExecSCost st d env (.ifStmt c t none) st' .normal nc
  | whileFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' : St) (v : Value) (nc : Nat) :
    EvalECost st d env c st' v nc → v.truthy = false →
    ExecSCost st d env (.whileStmt c b) st' .normal nc
  | whileBreak (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v : Value) (nc nb : Nat) :
    EvalECost st d env c st' v nc → v.truthy = true →
    ExecSCost st' d env b st'' .brk nb →
    ExecSCost st d env (.whileStmt c b) st'' .normal (nc + nb)
  | whileRet (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v rv : Value) (nc nb : Nat) :
    EvalECost st d env c st' v nc → v.truthy = true →
    ExecSCost st' d env b st'' (.ret rv) nb →
    ExecSCost st d env (.whileStmt c b) st'' (.ret rv) (nc + nb)
  | whileLoop (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' st''' : St) (v : Value) (status status' : Status)
      (nc nb nr : Nat) :
    EvalECost st d env c st' v nc → v.truthy = true →
    ExecSCost st' d env b st'' status nb →
    (status = .normal ∨ status = .cont) →
    ExecSCost st'' d env (.whileStmt c b) st''' status' nr →
    ExecSCost st d env (.whileStmt c b) st''' status' (nc + nb + nr)
  | forStart (st : St) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' st'' : St) (status : Status) (ni nl : Nat) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecInitCost ⟨store', st.out⟩ d outer init st' ni →
    ForLoopCost st' d outer cnd step b st'' status nl →
    ExecSCost st d env (.forStmt init cnd step b) st'' status (envBytes + ni + nl)
  | ret (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value)
      (n : Nat) :
    EvalECost st d env e st' v n →
    ExecSCost st d env (.ret (some e)) st' (.ret v) n
  | retNull (st : St) (d : Nat) (env : Addr) :
    ExecSCost st d env (.ret none) st (.ret .null) 0
  | brk (st : St) (d : Nat) (env : Addr) : ExecSCost st d env .brk st .brk 0
  | cont (st : St) (d : Nat) (env : Addr) : ExecSCost st d env .cont st .cont 0

inductive ExecInitCost : St → Nat → Addr → Option Stmt → St → Nat → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ExecInitCost st d env none st 0
  | some (st : St) (d : Nat) (env : Addr) (s : Stmt) (st' : St) (status : Status)
      (n : Nat) :
    ExecSCost st d env s st' status n →
    ExecInitCost st d env (some s) st' n

inductive ForLoopCost : St → Nat → Addr → Option Expr → Option Expr → Stmt → St →
    Status → Nat → Prop where
  | condFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr)
      (b : Stmt) (st' : St) (v : Value) (nc : Nat) :
    EvalECost st d env c st' v nc → v.truthy = false →
    ForLoopCost st d env (some c) step b st' .normal nc
  | bodyBreak (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' : St) (nc nb : Nat) :
    ForCondCost st d env cnd st' nc →
    ExecSCost st' d env b st'' .brk nb →
    ForLoopCost st d env cnd step b st'' .normal (nc + nb)
  | bodyRet (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' : St) (rv : Value) (nc nb : Nat) :
    ForCondCost st d env cnd st' nc →
    ExecSCost st' d env b st'' (.ret rv) nb →
    ForLoopCost st d env cnd step b st'' (.ret rv) (nc + nb)
  | loop (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : St)
      (status status' : Status) (nc nb ns nr : Nat) :
    ForCondCost st d env cnd st' nc →
    ExecSCost st' d env b st'' status nb →
    (status = .normal ∨ status = .cont) →
    ExecStepCost st'' d env step st''' ns →
    ForLoopCost st''' d env cnd step b st'''' status' nr →
    ForLoopCost st d env cnd step b st'''' status' (nc + nb + ns + nr)

inductive ForCondCost : St → Nat → Addr → Option Expr → St → Nat → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ForCondCost st d env none st 0
  | some (st : St) (d : Nat) (env : Addr) (c : Expr) (st' : St) (v : Value)
      (nc : Nat) :
    EvalECost st d env c st' v nc → v.truthy = true →
    ForCondCost st d env (some c) st' nc

inductive ExecStepCost : St → Nat → Addr → Option Expr → St → Nat → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ExecStepCost st d env none st 0
  | some (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value)
      (n : Nat) :
    EvalECost st d env e st' v n →
    ExecStepCost st d env (some e) st' n

inductive ExecSeqCost : St → Nat → Addr → List Stmt → St → Status → Nat → Prop where
  | nil (st : St) (d : Nat) (env : Addr) : ExecSeqCost st d env [] st .normal 0
  | consNormal (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' st'' : St) (status : Status) (n1 n2 : Nat) :
    ExecSCost st d env s st' .normal n1 →
    ExecSeqCost st' d env ss st'' status n2 →
    ExecSeqCost st d env (s :: ss) st'' status (n1 + n2)
  | consAbrupt (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : St) (status : Status) (n : Nat) :
    ExecSCost st d env s st' status n →
    status ≠ .normal →
    ExecSeqCost st d env (s :: ss) st' status n

end

private def M1 st d a e st' v (_ : EvalE st d a e st' v) : Prop :=
  ∃ n, EvalECost st d a e st' v n
private def M2 st d a es st' vs (_ : EvalArgs st d a es st' vs) : Prop :=
  ∃ n, EvalArgsCost st d a es st' vs n
private def M3 st d fv vs st' v (_ : Call st d fv vs st' v) : Prop :=
  ∃ n, CallCost st d fv vs st' v n
private def M4 st d a s st' status (_ : ExecS st d a s st' status) : Prop :=
  ∃ n, ExecSCost st d a s st' status n
private def M5 st d a init st' (_ : ExecInit st d a init st') : Prop :=
  ∃ n, ExecInitCost st d a init st' n
private def M6 st d a cnd step b st' status (_ : ForLoop st d a cnd step b st' status) : Prop :=
  ∃ n, ForLoopCost st d a cnd step b st' status n
private def M7 st d a cnd st' (_ : ForCond st d a cnd st') : Prop :=
  ∃ n, ForCondCost st d a cnd st' n
private def M8 st d a step st' (_ : ExecStep st d a step st') : Prop :=
  ∃ n, ExecStepCost st d a step st' n
private def M9 st d a ss st' status (_ : ExecSeq st d a ss st' status) : Prop :=
  ∃ n, ExecSeqCost st d a ss st' status n

private theorem c_int : ∀ st d env n, M1 st d env (.int n) st (.int n) (.int ..)
    := by
  intro _ _ _ _
  exact ⟨_, .int ..⟩
private theorem c_str : ∀ st d env s, M1 st d env (.str s) st (.str s) (.str ..)
    := by
  intro _ _ _ _
  exact ⟨_, .str ..⟩
private theorem c_bool : ∀ st d env b, M1 st d env (.bool b) st (.bool b) (.bool ..)
    := by
  intro _ _ _ _
  exact ⟨_, .bool ..⟩
private theorem c_null : ∀ st d env, M1 st d env .null st .null (.null ..)
    := by
  intro _ _ _
  exact ⟨_, .null ..⟩
private theorem c_var : ∀ st d env x v (hv : st.store.get? env x = some v),
    M1 st d env (.var x) st v (.var st d env x v hv)
    := by
  intro st d env x v hv
  exact ⟨_, .var _ _ _ _ _ hv⟩
private theorem c_assign : ∀ st d env x e st' v store''
    (he : EvalE st d env e st' v) (hs : st'.store.set? env x v = some store''),
    M1 st d env e st' v he →
    M1 st d env (.assign x e) ⟨store'', st'.out⟩ v (.assign st d env x e st' v store'' he hs)
    := by
  intro st d env x e st' v store'' he hs ih
  obtain ⟨n, hn⟩ := ih
  exact ⟨n, .assign _ _ _ _ _ _ _ _ _ hn hs⟩
private theorem c_bin : ∀ st d env op l r st' st'' lv rv v
    (hl : EvalE st d env l st' lv) (hr : EvalE st' d env r st'' rv)
    (hop : binOpSem st''.store op lv rv = some v),
    M1 st d env l st' lv hl → M1 st' d env r st'' rv hr →
    M1 st d env (.binary op l r) st'' v (.binary st d env op l r st' st'' lv rv v hl hr hop)
    := by
  intro st d env op l r st' st'' lv rv v hl hr hop ihl ihr
  obtain ⟨_, hnl⟩ := ihl
  obtain ⟨_, hnr⟩ := ihr
  exact ⟨_, .binary _ _ _ _ _ _ _ _ _ _ _ _ _ hnl hnr hop⟩
private theorem c_ort : ∀ st d env l r st' lv
    (hl : EvalE st d env l st' lv) (ht : lv.truthy = true),
    M1 st d env l st' lv hl →
    M1 st d env (.logical .or l r) st' (.bool true) (.orTrue st d env l r st' lv hl ht)
    := by
  intro st d env l r st' lv hl ht ih
  obtain ⟨n, hn⟩ := ih
  exact ⟨n, .orTrue _ _ _ _ _ _ _ _ hn ht⟩
private theorem c_orf : ∀ st d env l r st' st'' lv rv
    (hl : EvalE st d env l st' lv) (hf : lv.truthy = false) (hr : EvalE st' d env r st'' rv),
    M1 st d env l st' lv hl → M1 st' d env r st'' rv hr →
    M1 st d env (.logical .or l r) st'' (.bool rv.truthy) (.orFalse st d env l r st' st'' lv rv hl hf hr)
    := by
  intro st d env l r st' st'' lv rv hl hf hr ihl ihr
  obtain ⟨_, hnl⟩ := ihl
  obtain ⟨_, hnr⟩ := ihr
  exact ⟨_, .orFalse _ _ _ _ _ _ _ _ _ _ _ hnl hf hnr⟩
private theorem c_anf : ∀ st d env l r st' lv
    (hl : EvalE st d env l st' lv) (hf : lv.truthy = false),
    M1 st d env l st' lv hl →
    M1 st d env (.logical .and l r) st' (.bool false) (.andFalse st d env l r st' lv hl hf)
    := by
  intro st d env l r st' lv hl hf ih
  obtain ⟨n, hn⟩ := ih
  exact ⟨n, .andFalse _ _ _ _ _ _ _ _ hn hf⟩
private theorem c_ant : ∀ st d env l r st' st'' lv rv
    (hl : EvalE st d env l st' lv) (ht : lv.truthy = true) (hr : EvalE st' d env r st'' rv),
    M1 st d env l st' lv hl → M1 st' d env r st'' rv hr →
    M1 st d env (.logical .and l r) st'' (.bool rv.truthy) (.andTrue st d env l r st' st'' lv rv hl ht hr)
    := by
  intro st d env l r st' st'' lv rv hl ht hr ihl ihr
  obtain ⟨_, hnl⟩ := ihl
  obtain ⟨_, hnr⟩ := ihr
  exact ⟨_, .andTrue _ _ _ _ _ _ _ _ _ _ _ hnl ht hnr⟩
private theorem c_neg : ∀ st d env e st' n (he : EvalE st d env e st' (.int n)),
    M1 st d env e st' (.int n) he →
    M1 st d env (.unary .neg e) st' (.int (wrap64 (-n))) (.neg st d env e st' n he)
    := by
  intro st d env e st' n he ih
  obtain ⟨m, hm⟩ := ih
  exact ⟨m, .neg _ _ _ _ _ _ _ hm⟩
private theorem c_not : ∀ st d env e st' v (he : EvalE st d env e st' v),
    M1 st d env e st' v he →
    M1 st d env (.unary .not e) st' (.bool (!v.truthy)) (.not st d env e st' v he)
    := by
  intro st d env e st' v he ih
  obtain ⟨m, hm⟩ := ih
  exact ⟨m, .not _ _ _ _ _ _ _ hm⟩
private theorem c_call : ∀ st d env f args st' st'' st''' fv vs v
    (hf : EvalE st d env f st' fv) (hargs : args.length ≤ maxArgs)
    (ha : EvalArgs st' d env args st'' vs)
    (hc : Call st'' d fv vs st''' v),
    M1 st d env f st' fv hf → M2 st' d env args st'' vs ha → M3 st'' d fv vs st''' v hc →
    M1 st d env (.call f args) st''' v
      (.call st d env f args st' st'' st''' fv vs v hf hargs ha hc)
    := by
  intro st d env f args st' st'' st''' fv vs v hf hargs ha hc ihf iha ihc
  obtain ⟨_, hnf⟩ := ihf
  obtain ⟨_, hna⟩ := iha
  obtain ⟨_, hnc⟩ := ihc
  exact ⟨_, .call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnf hargs hna hnc⟩
private theorem c_fn : ∀ st d env name params body store' a
    (hc : st.store.allocClosure ⟨env, name, params, body⟩ = (store', a)),
    M1 st d env (.fn name params body) ⟨store', st.out⟩ (.closure a) (.fn st d env name params body store' a hc)
    := by
  intro st d env name params body store' a hc
  exact ⟨_, .fn _ _ _ _ _ _ _ _ hc⟩
private theorem c_anil : ∀ st d env, M2 st d env [] st [] (.nil ..)
    := by
  intro _ _ _
  exact ⟨_, .nil ..⟩
private theorem c_acons : ∀ st d env e es st' st'' v vs
    (he : EvalE st d env e st' v) (hes : EvalArgs st' d env es st'' vs),
    M1 st d env e st' v he → M2 st' d env es st'' vs hes →
    M2 st d env (e :: es) st'' (v :: vs) (.cons st d env e es st' st'' v vs he hes)
    := by
  intro st d env e es st' st'' v vs he hes ihe ihes
  obtain ⟨_, hne⟩ := ihe
  obtain ⟨_, hnes⟩ := ihes
  exact ⟨_, .cons _ _ _ _ _ _ _ _ _ _ _ hne hnes⟩
private theorem c_clo : ∀ st d a cd vs store' frame st' status v
    (hc : st.store.closures[a]? = some cd) (hlen : vs.length = cd.params.length)
    (hd : d < maxCallDepth) (hf : st.store.allocFrame (some cd.env) = (store', frame))
    (hst : ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
      (d + 1) frame cd.body st' status)
    (hstat : status = .normal ∧ v = .null ∨ status = .ret v),
    M9 ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
      (d + 1) frame cd.body st' status hst →
    M3 st d (.closure a) vs st' v (.closure st d a cd vs store' frame st' status v hc hlen hd hf hst hstat)
    := by
  intro st d a cd vs store' frame st' status v hc hlen hd hf hst hstat ihb
  obtain ⟨_, hnb⟩ := ihb
  exact ⟨_, .closure _ _ _ _ _ _ _ _ _ _ _ hc hlen hd hf hnb hstat⟩
private theorem c_pr : ∀ st d vs,
    M3 st d (.native .print) vs ⟨st.store, st.out ++ printArgs st.store vs⟩ .null (.print ..)
    := by
  intro _ _ _
  exact ⟨_, .print ..⟩
private theorem c_prl : ∀ st d vs,
    M3 st d (.native .println) vs ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null (.println ..)
    := by
  intro _ _ _
  exact ⟨_, .println ..⟩
private theorem c_as : ∀ st d vs v m (hvs : vs = [v] ∨ vs = [v, m]) (ht : v.truthy = true),
    M3 st d (.native .assert) vs st .null (.assertOk st d vs v m hvs ht)
    := by
  intro st d vs v m hvs ht
  exact ⟨_, .assertOk _ _ _ _ _ hvs ht⟩
private theorem c_sexpr : ∀ st d env e st' v (he : EvalE st d env e st' v),
    M1 st d env e st' v he → M4 st d env (.expr e) st' .normal (.expr st d env e st' v he)
    := by
  intro st d env e st' v he ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .expr _ _ _ _ _ _ _ hn⟩
private theorem c_svi : ∀ st d env x e st' v (he : EvalE st d env e st' v),
    M1 st d env e st' v he →
    M4 st d env (.varDecl x (some e)) ⟨st'.store.define env x v, st'.out⟩ .normal
      (.varInit st d env x e st' v he)
    := by
  intro st d env x e st' v he ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .varInit _ _ _ _ _ _ _ _ hn⟩
private theorem c_svn : ∀ st d env x,
    M4 st d env (.varDecl x none) ⟨st.store.define env x .null, st.out⟩ .normal (.varNull ..)
    := by
  intro _ _ _ _
  exact ⟨_, .varNull ..⟩
private theorem c_sblk : ∀ st d env ss store' inner st' status
    (hf : st.store.allocFrame (some env) = (store', inner))
    (hseq : ExecSeq ⟨store', st.out⟩ d inner ss st' status),
    M9 ⟨store', st.out⟩ d inner ss st' status hseq →
    M4 st d env (.block ss) st' status (.block st d env ss store' inner st' status hf hseq)
    := by
  intro st d env ss store' inner st' status hf hseq ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .block _ _ _ _ _ _ _ _ _ hf hn⟩
private theorem c_sift : ∀ st d env c t e st' st'' v status
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hs : ExecS st' d env t st'' status),
    M1 st d env c st' v hc → M4 st' d env t st'' status hs →
    M4 st d env (.ifStmt c t e) st'' status (.ifTrue st d env c t e st' st'' v status hc ht hs)
    := by
  intro st d env c t e st' st'' v status hc ht hs ihc iht
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnt⟩ := iht
  exact ⟨_, .ifTrue _ _ _ _ _ _ _ _ _ _ _ _ hnc ht hnt⟩
private theorem c_siff : ∀ st d env c t e st' st'' v status
    (hc : EvalE st d env c st' v) (hf : v.truthy = false) (hs : ExecS st' d env e st'' status),
    M1 st d env c st' v hc → M4 st' d env e st'' status hs →
    M4 st d env (.ifStmt c t (some e)) st'' status (.ifFalse st d env c t e st' st'' v status hc hf hs)
    := by
  intro st d env c t e st' st'' v status hc hf hs ihc ihe
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hne⟩ := ihe
  exact ⟨_, .ifFalse _ _ _ _ _ _ _ _ _ _ _ _ hnc hf hne⟩
private theorem c_sifn : ∀ st d env c t st' v
    (hc : EvalE st d env c st' v) (hf : v.truthy = false),
    M1 st d env c st' v hc →
    M4 st d env (.ifStmt c t none) st' .normal (.ifNone st d env c t st' v hc hf)
    := by
  intro st d env c t st' v hc hf ihc
  obtain ⟨_, hnc⟩ := ihc
  exact ⟨_, .ifNone _ _ _ _ _ _ _ _ hnc hf⟩
private theorem c_swf : ∀ st d env c b st' v
    (hc : EvalE st d env c st' v) (hf : v.truthy = false),
    M1 st d env c st' v hc →
    M4 st d env (.whileStmt c b) st' .normal (.whileFalse st d env c b st' v hc hf)
    := by
  intro st d env c b st' v hc hf ihc
  obtain ⟨_, hnc⟩ := ihc
  exact ⟨_, .whileFalse _ _ _ _ _ _ _ _ hnc hf⟩
private theorem c_swb : ∀ st d env c b st' st'' v
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hb : ExecS st' d env b st'' .brk),
    M1 st d env c st' v hc → M4 st' d env b st'' .brk hb →
    M4 st d env (.whileStmt c b) st'' .normal (.whileBreak st d env c b st' st'' v hc ht hb)
    := by
  intro st d env c b st' st'' v hc ht hb ihc ihb
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  exact ⟨_, .whileBreak _ _ _ _ _ _ _ _ _ _ hnc ht hnb⟩
private theorem c_swr : ∀ st d env c b st' st'' v rv
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hb : ExecS st' d env b st'' (.ret rv)),
    M1 st d env c st' v hc → M4 st' d env b st'' (.ret rv) hb →
    M4 st d env (.whileStmt c b) st'' (.ret rv) (.whileRet st d env c b st' st'' v rv hc ht hb)
    := by
  intro st d env c b st' st'' v rv hc ht hb ihc ihb
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  exact ⟨_, .whileRet _ _ _ _ _ _ _ _ _ _ _ hnc ht hnb⟩
private theorem c_swl : ∀ st d env c b st' st'' st''' v status status'
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hb : ExecS st' d env b st'' status)
    (hstat : status = .normal ∨ status = .cont)
    (hr : ExecS st'' d env (.whileStmt c b) st''' status'),
    M1 st d env c st' v hc → M4 st' d env b st'' status hb →
    M4 st'' d env (.whileStmt c b) st''' status' hr →
    M4 st d env (.whileStmt c b) st''' status'
      (.whileLoop st d env c b st' st'' st''' v status status' hc ht hb hstat hr)
    := by
  intro st d env c b st' st'' st''' v status status' hc ht hb hstat hr ihc ihb ihr
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  obtain ⟨_, hnr⟩ := ihr
  exact ⟨_, .whileLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnc ht hnb hstat hnr⟩
private theorem c_sfor : ∀ st d env init cnd step b store' outer st' st'' status
    (hf : st.store.allocFrame (some env) = (store', outer))
    (hi : ExecInit ⟨store', st.out⟩ d outer init st')
    (hl : ForLoop st' d outer cnd step b st'' status),
    M5 ⟨store', st.out⟩ d outer init st' hi → M6 st' d outer cnd step b st'' status hl →
    M4 st d env (.forStmt init cnd step b) st'' status
      (.forStart st d env init cnd step b store' outer st' st'' status hf hi hl)
    := by
  intro st d env init cnd step b store' outer st' st'' status hf hi hl ihi ihl
  obtain ⟨_, hni⟩ := ihi
  obtain ⟨_, hnl⟩ := ihl
  exact ⟨_, .forStart _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf hni hnl⟩
private theorem c_sret : ∀ st d env e st' v (he : EvalE st d env e st' v),
    M1 st d env e st' v he → M4 st d env (.ret (some e)) st' (.ret v) (.ret st d env e st' v he)
    := by
  intro st d env e st' v he ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .ret _ _ _ _ _ _ _ hn⟩
private theorem c_srn : ∀ st d env, M4 st d env (.ret none) st (.ret .null) (.retNull ..)
    := by
  intro _ _ _
  exact ⟨_, .retNull ..⟩
private theorem c_sbrk : ∀ st d env, M4 st d env .brk st .brk (.brk ..)
    := by
  intro _ _ _
  exact ⟨_, .brk ..⟩
private theorem c_scont : ∀ st d env, M4 st d env .cont st .cont (.cont ..)
    := by
  intro _ _ _
  exact ⟨_, .cont ..⟩
private theorem c_inone : ∀ st d env, M5 st d env none st (.none ..)
    := by
  intro _ _ _
  exact ⟨_, .none ..⟩
private theorem c_isome : ∀ st d env s st' status (hs : ExecS st d env s st' status),
    M4 st d env s st' status hs →
    M5 st d env (some s) st' (.some st d env s st' status hs)
    := by
  intro st d env s st' status hs ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .some _ _ _ _ _ _ _ hn⟩
private theorem c_lcf : ∀ st d env c step b st' v
    (hc : EvalE st d env c st' v) (hf : v.truthy = false),
    M1 st d env c st' v hc →
    M6 st d env (some c) step b st' .normal (.condFalse st d env c step b st' v hc hf)
    := by
  intro st d env c step b st' v hc hf ihc
  obtain ⟨_, hnc⟩ := ihc
  exact ⟨_, .condFalse _ _ _ _ _ _ _ _ _ hnc hf⟩
private theorem c_lbb : ∀ st d env cnd step b st' st''
    (hcond : ForCond st d env cnd st') (hb : ExecS st' d env b st'' .brk),
    M7 st d env cnd st' hcond → M4 st' d env b st'' .brk hb →
    M6 st d env cnd step b st'' .normal (.bodyBreak st d env cnd step b st' st'' hcond hb)
    := by
  intro st d env cnd step b st' st'' hcond hb ihc ihb
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  exact ⟨_, .bodyBreak _ _ _ _ _ _ _ _ _ _ hnc hnb⟩
private theorem c_lbr : ∀ st d env cnd step b st' st'' rv
    (hcond : ForCond st d env cnd st') (hb : ExecS st' d env b st'' (.ret rv)),
    M7 st d env cnd st' hcond → M4 st' d env b st'' (.ret rv) hb →
    M6 st d env cnd step b st'' (.ret rv) (.bodyRet st d env cnd step b st' st'' rv hcond hb)
    := by
  intro st d env cnd step b st' st'' rv hcond hb ihc ihb
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  exact ⟨_, .bodyRet _ _ _ _ _ _ _ _ _ _ _ hnc hnb⟩
private theorem c_lloop : ∀ st d env cnd step b st' st'' st''' st'''' status status'
    (hcond : ForCond st d env cnd st') (hb : ExecS st' d env b st'' status)
    (hstat : status = .normal ∨ status = .cont) (hs : ExecStep st'' d env step st''')
    (hr : ForLoop st''' d env cnd step b st'''' status'),
    M7 st d env cnd st' hcond → M4 st' d env b st'' status hb →
    M8 st'' d env step st''' hs → M6 st''' d env cnd step b st'''' status' hr →
    M6 st d env cnd step b st'''' status'
      (.loop st d env cnd step b st' st'' st''' st'''' status status' hcond hb hstat hs hr)
    := by
  intro st d env cnd step b st' st'' st''' st'''' status status' hcond hb hstat hs hr ihc ihb ihs ihr
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  obtain ⟨_, hns⟩ := ihs
  obtain ⟨_, hnr⟩ := ihr
  exact ⟨_, .loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnc hnb hstat hns hnr⟩
private theorem c_cnone : ∀ st d env, M7 st d env none st (.none ..)
    := by
  intro _ _ _
  exact ⟨_, .none ..⟩
private theorem c_csome : ∀ st d env c st' v
    (hc : EvalE st d env c st' v) (ht : v.truthy = true),
    M1 st d env c st' v hc → M7 st d env (some c) st' (.some st d env c st' v hc ht)
    := by
  intro st d env c st' v hc ht ihc
  obtain ⟨_, hnc⟩ := ihc
  exact ⟨_, .some _ _ _ _ _ _ _ hnc ht⟩
private theorem c_stnone : ∀ st d env, M8 st d env none st (.none ..)
    := by
  intro _ _ _
  exact ⟨_, .none ..⟩
private theorem c_stsome : ∀ st d env e st' v (he : EvalE st d env e st' v),
    M1 st d env e st' v he → M8 st d env (some e) st' (.some st d env e st' v he)
    := by
  intro st d env e st' v he ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .some _ _ _ _ _ _ _ hn⟩
private theorem c_qnil : ∀ st d env, M9 st d env [] st .normal (.nil ..)
    := by
  intro _ _ _
  exact ⟨_, .nil ..⟩
private theorem c_qcn : ∀ st d env s ss st' st'' status
    (hs : ExecS st d env s st' .normal) (hss : ExecSeq st' d env ss st'' status),
    M4 st d env s st' .normal hs → M9 st' d env ss st'' status hss →
    M9 st d env (s :: ss) st'' status (.consNormal st d env s ss st' st'' status hs hss)
    := by
  intro st d env s ss st' st'' status hs hss ihs ihss
  obtain ⟨_, hn1⟩ := ihs
  obtain ⟨_, hn2⟩ := ihss
  exact ⟨_, .consNormal _ _ _ _ _ _ _ _ _ _ hn1 hn2⟩
private theorem c_qca : ∀ st d env s ss st' status
    (hs : ExecS st d env s st' status) (hne : status ≠ .normal),
    M4 st d env s st' status hs →
    M9 st d env (s :: ss) st' status (.consAbrupt st d env s ss st' status hs hne)
    := by
  intro st d env s ss st' status hs hne ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .consAbrupt _ _ _ _ _ _ _ _ hn hne⟩

theorem cost_exists_mutual :
    (∀ {st d a e st' v}, EvalE st d a e st' v → ∃ n, EvalECost st d a e st' v n) ∧
    (∀ {st d a es st' vs}, EvalArgs st d a es st' vs → ∃ n, EvalArgsCost st d a es st' vs n) ∧
    (∀ {st d fv vs st' v}, Call st d fv vs st' v → ∃ n, CallCost st d fv vs st' v n) ∧
    (∀ {st d a s st' status}, ExecS st d a s st' status → ∃ n, ExecSCost st d a s st' status n) ∧
    (∀ {st d a init st'}, ExecInit st d a init st' → ∃ n, ExecInitCost st d a init st' n) ∧
    (∀ {st d a cnd step b st' status}, ForLoop st d a cnd step b st' status →
      ∃ n, ForLoopCost st d a cnd step b st' status n) ∧
    (∀ {st d a cnd st'}, ForCond st d a cnd st' → ∃ n, ForCondCost st d a cnd st' n) ∧
    (∀ {st d a step st'}, ExecStep st d a step st' → ∃ n, ExecStepCost st d a step st' n) ∧
    (∀ {st d a ss st' status}, ExecSeq st d a ss st' status →
      ∃ n, ExecSeqCost st d a ss st' status n) :=
  ⟨@fun st d a e st' v h => EvalE.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a es st' vs h => EvalArgs.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d fv vs st' v h => Call.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a s st' status h => ExecS.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a init st' h => ExecInit.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a cnd step b st' status h => ForLoop.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a cnd st' h => ForCond.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a step st' h => ExecStep.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a ss st' status h => ExecSeq.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h⟩

theorem execSeq_cost_exists {st d a ss st' status} :
    ExecSeq st d a ss st' status → ∃ n, ExecSeqCost st d a ss st' status n :=
  cost_exists_mutual.2.2.2.2.2.2.2.2

def StoreLe (a b : Store) : Prop :=
  a.frames.size ≤ b.frames.size ∧ a.closures.size ≤ b.closures.size

theorem StoreLe.trans {a b c : Store} : StoreLe a b → StoreLe b c → StoreLe a c :=
  fun h1 h2 => ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2 h2.2⟩

def BigStepBudget (p : Program) (out : String) (n : Nat) : Prop :=
  ∃ st' m, ExecSeqCost initSt 0 0 p st' .normal m ∧ st'.out = out ∧ m ≤ n

end Vsa.While
