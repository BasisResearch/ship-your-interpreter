import Vsa.AbsInt.State

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

structure Cfg where

  unroll : Nat := 200

  widenFuel : Nat := 60

  narrowFuel : Nat := 2
  deriving Repr

variable {A : Type} [AbsOps A]

structure ERes (A : Type) where
  st : AState A
  val : A
  al : List Kind

structure SRes (A : Type) where
  norm : AState A
  brk : AState A
  cont : AState A
  ret : AState A
  retv : A
  al : List Kind

def ERes.none : ERes A := ⟨.bot, top, []⟩

def SRes.normal (σ : AState A) (al : List Kind := []) : SRes A :=
  ⟨σ, .bot, .bot, .bot, top, al⟩

def joinRet (σ₁ : AState A) (v₁ : A) (σ₂ : AState A) (v₂ : A) : A :=
  if σ₁.isBot then v₂ else if σ₂.isBot then v₁ else join v₁ v₂

def SRes.join (r r' : SRes A) : SRes A :=
  ⟨r.norm.join r'.norm, r.brk.join r'.brk, r.cont.join r'.cont, r.ret.join r'.ret,
    joinRet r.ret r.retv r'.ret r'.retv, r.al ∪ r'.al⟩

def isPure : Expr → Bool
  | .int _ | .str _ | .bool _ | .null | .var _ => true
  | .binary _ l r | .logical _ l r => isPure l && isPure r
  | .unary _ e => isPure e
  | _ => false

def pureVal (σ : AState A) : Expr → Option A
  | .int n => some (ofValue (.int n))
  | .str s => some (ofValue (.str s))
  | .bool b => some (ofValue (.bool b))
  | .null => some (ofValue .null)
  | .var x => some (σ.lookup x).1
  | _ => none

def filterE (t : Bool) (σ : AState A) : Expr → AState A
  | .binary op (.var x) r =>
    match pureVal σ r with
    | some b =>
      if isBot (refine op t (σ.lookup x).1 b) then .bot
      else σ.strengthen x (refine op t (σ.lookup x).1 b)
    | none => σ
  | .unary .not e => filterE (!t) σ e
  | .logical .and l r =>
    if t && isPure l && isPure r then filterE true (filterE true σ l) r else σ
  | .logical .or l r =>
    if !t && isPure l && isPure r then filterE false (filterE false σ l) r else σ
  | _ => σ

def branch (t : Bool) (c : Expr) (r : ERes A) : AState A :=
  if (if t then mayT r.val else mayF r.val) then filterE t r.st c else .bot

def assertOk : List A → Bool
  | [a] => !mayF a
  | [a, _] => !mayF a
  | _ => false

def callSt (a : A) (σ : AState A) : AState A :=
  match asNative a with
  | some _ => σ
  | none => if σ.isBot then .bot else .top

def callVal (a : A) : A :=
  match asNative a with
  | some _ => ofValue .null
  | none => top

def callAl (a : A) (avs : List A) : List Kind :=
  match asNative a with
  | some .assert => if assertOk avs then [] else [.assert]
  | some _ => []
  | none => Kind.inCall

mutual

def aeval (σ : AState A) (e : Expr) : ERes A :=
  if σ.isBot then ERes.none else
  match e with
  | .int n => ⟨σ, ofValue (.int n), []⟩
  | .str s => ⟨σ, ofValue (.str s), []⟩
  | .bool b => ⟨σ, ofValue (.bool b), []⟩
  | .null => ⟨σ, ofValue .null, []⟩
  | .var x => ⟨σ, (σ.lookup x).1, if (σ.lookup x).2 then [.unbound] else []⟩
  | .assign x e =>
    let re := aeval σ e
    let ra := re.st.assign x re.val
    ⟨ra.1, re.val, re.al ∪ if ra.2 then [.unbound] else []⟩
  | .binary op l r =>
    let rl := aeval σ l
    let rr := aeval rl.st r
    ⟨rr.st, binop op rl.val rr.val, rl.al ∪ rr.al ∪ binErr op rl.val rr.val⟩
  | .logical .or l r =>
    let rl := aeval σ l
    let rr := aeval (branch false l rl) r
    ⟨(branch true l rl).join rr.st,
      boolOf (mayT rl.val || (mayF rl.val && mayT rr.val)) (mayF rl.val && mayF rr.val),
      rl.al ∪ rr.al⟩
  | .logical .and l r =>
    let rl := aeval σ l
    let rr := aeval (branch true l rl) r
    ⟨(branch false l rl).join rr.st,
      boolOf (mayT rl.val && mayT rr.val) (mayF rl.val || (mayT rl.val && mayF rr.val)),
      rl.al ∪ rr.al⟩
  | .unary .neg e =>
    let re := aeval σ e
    ⟨re.st, neg re.val, re.al ∪ if negErr re.val then [.type] else []⟩
  | .unary .not e =>
    let re := aeval σ e
    ⟨re.st, notOf re.val, re.al⟩
  | .call f args =>
    let rf := aeval σ f
    let ra := aevalArgs rf.st args
    ⟨callSt rf.val ra.1, callVal rf.val,
      rf.al ∪ (if args.length ≤ maxArgs then [] else [.call]) ∪ ra.2.2 ∪
        callAl rf.val ra.2.1⟩
  | .fn _ _ _ => ⟨σ, closure, []⟩

def aevalArgs (σ : AState A) : List Expr → AState A × List A × List Kind
  | [] => (σ, [], [])
  | e :: es =>
    let re := aeval σ e
    let rs := aevalArgs re.st es
    (rs.1, re.val :: rs.2.1, re.al ∪ rs.2.2)

end

structure LStep (A : Type) where

  exitN : AState A
  ret : AState A
  retv : A

  next : AState A
  al : List Kind

def LStep.out (r : LStep A) : SRes A := ⟨r.exitN, .bot, .bot, r.ret, r.retv, r.al⟩

def fixIter (F : AState A → AState A) : Nat → AState A → AState A
  | 0, J => J
  | n + 1, J => if (F J).le J then J else fixIter F n (J.widen (F J))

def isPost (F : AState A → AState A) (I J : AState A) : Bool := I.le J && (F J).le J

def narrowIter (F : AState A → AState A) (I : AState A) : Nat → AState A → AState A
  | 0, J => J
  | n + 1, J => if isPost F I (I.join (F J)) then narrowIter F I n (I.join (F J)) else J

def postFix (F : AState A → AState A) (fuel narrow : Nat) (I : AState A) : AState A :=
  if isPost F I (fixIter F fuel I) then narrowIter F I narrow (fixIter F fuel I) else .top

def loopAbs (cfg : Cfg) (F : AState A → LStep A) : Nat → AState A → SRes A
  | 0, I => (F (postFix (fun J => (F J).next) cfg.widenFuel cfg.narrowFuel I)).out
  | k + 1, I =>
    if (F I).next.isBot || (F I).next.le I then (F I).out
    else (F I).out.join (loopAbs cfg F k (F I).next)

def whileStep (evalC : AState A → ERes A) (c : Expr) (execB : AState A → SRes A)
    (I : AState A) : LStep A :=
  let rc := evalC I
  let rb := execB (branch true c rc)
  ⟨(branch false c rc).join rb.brk, rb.ret, rb.retv, rb.norm.join rb.cont, rc.al ∪ rb.al⟩

def forStep (evalC : AState A → ERes A) (cnd : Option Expr)
    (execB : AState A → SRes A) (evalS : AState A → ERes A) (step : Option Expr)
    (I : AState A) : LStep A :=
  let rc := evalC I
  let enter : AState A := match cnd with
    | none => I
    | some c => branch true c rc
  let leave : AState A := match cnd with
    | none => .bot
    | some c => branch false c rc
  let rb := execB enter
  let mid := rb.norm.join rb.cont
  let rs := evalS mid
  let after : AState A := match step with
    | none => mid
    | some _ => rs.st
  let alC : List Kind := match cnd with
    | none => []
    | some _ => rc.al
  let alS : List Kind := match step with
    | none => []
    | some _ => rs.al
  ⟨leave.join rb.brk, rb.ret, rb.retv, after, alC ∪ rb.al ∪ alS⟩

def optEval (e : Option Expr) (I : AState A) : ERes A :=
  match e with
  | none => ERes.none
  | some e => aeval I e

def SRes.seq (r r' : SRes A) : SRes A :=
  { r' with brk := r.brk.join r'.brk, cont := r.cont.join r'.cont,
            ret := r.ret.join r'.ret, retv := joinRet r.ret r.retv r'.ret r'.retv,
            al := r.al ∪ r'.al }

def SRes.pop (r : SRes A) : SRes A :=
  ⟨r.norm.pop, r.brk.pop, r.cont.pop, r.ret.pop, r.retv, r.al⟩

def SRes.any (r : SRes A) : AState A := ((r.norm.join r.brk).join r.cont).join r.ret

mutual

def aexec (cfg : Cfg) (σ : AState A) : Stmt → SRes A
  | .expr e => let re := aeval σ e; SRes.normal re.st re.al
  | .varDecl x (some e) =>
    let re := aeval σ e
    SRes.normal (re.st.define x re.val) re.al
  | .varDecl x none => SRes.normal (σ.define x (ofValue .null))
  | .block ss => (aexecSeq cfg σ.push ss).pop
  | .ifStmt c t e =>
    let rc := aeval σ c
    let rt := aexec cfg (branch true c rc) t
    let re := aexecOpt cfg (branch false c rc) e
    let r := rt.join re
    { r with al := rc.al ∪ r.al }
  | .whileStmt c b =>
    loopAbs cfg (whileStep (fun I => aeval I c) c (fun I => aexec cfg I b)) cfg.unroll σ
  | .forStmt init cnd step b =>
    let ri := aexecOpt cfg σ.push init
    let r := loopAbs cfg
      (forStep (optEval cnd) cnd (fun I => aexec cfg I b) (optEval step) step)
      cfg.unroll ri.any
    { r.pop with al := ri.al ∪ r.al }
  | .ret (some e) => let re := aeval σ e; ⟨.bot, .bot, .bot, re.st, re.val, re.al⟩
  | .ret none => ⟨.bot, .bot, .bot, σ, ofValue .null, []⟩
  | .brk => ⟨.bot, σ, .bot, .bot, top, []⟩
  | .cont => ⟨.bot, .bot, σ, .bot, top, []⟩

def aexecOpt (cfg : Cfg) (σ : AState A) : Option Stmt → SRes A
  | none => SRes.normal σ
  | some s => aexec cfg σ s

def aexecSeq (cfg : Cfg) (σ : AState A) : List Stmt → SRes A
  | [] => SRes.normal σ
  | s :: ss =>
    let r := aexec cfg σ s
    SRes.seq r (aexecSeq cfg r.norm ss)

end

def whileF (cfg : Cfg) (c : Expr) (b : Stmt) : AState A → LStep A :=
  whileStep (fun I => aeval I c) c (fun I => aexec cfg I b)

def forF (cfg : Cfg) (cnd step : Option Expr) (b : Stmt) : AState A → LStep A :=
  forStep (optEval cnd) cnd (fun I => aexec cfg I b) (optEval step) step

def initState : AState A :=
  .sc [[("print", ⟨ofValue (.native .print), true⟩),
        ("println", ⟨ofValue (.native .println), true⟩),
        ("assert", ⟨ofValue (.native .assert), true⟩)]]

def analyze (cfg : Cfg) (p : Program) : SRes A := aexecSeq cfg initState p

def alarms (cfg : Cfg) (p : Program) : List Kind :=
  let r := analyze (A := A) cfg p
  r.al ∪ if r.brk.isBot && r.cont.isBot && r.ret.isBot then [] else [.abrupt]

end Vsa.AbsInt
