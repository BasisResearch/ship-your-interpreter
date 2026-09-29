import Vsa.AbsInt.State

/-!
# The generic abstract interpreter

`aeval`/`aexec` interpret WHILE syntax over `AState A` for any value domain
`A`. Expression results carry the post-state, the abstract value and the
alarms raised; statement results carry one post-state per completion status
(`normal`, `break`, `continue`, `return`), the abstract returned value and
the alarms.

Loops (`loopAbs`) are first unrolled `Cfg.unroll` times; the remaining
iterations are covered by a post-fixpoint found by widening (`postFix`),
checked with `AState.le` and replaced by `⊤` if the check fails.

Calls to natives the domain identifies (`asNative`) leave the store unchanged
and return `null`. Any other call is not analysed: the state becomes `⊤` and
every in-call error kind is raised.
-/

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

/-- Analysis parameters. -/
structure Cfg where
  /-- Loop iterations analysed separately before widening. -/
  unroll : Nat := 200
  /-- Widening iterations before falling back to `⊤`. -/
  widenFuel : Nat := 60
  /-- Narrowing steps after a post-fixpoint is found. -/
  narrowFuel : Nat := 2
  deriving Repr

variable {A : Type} [AbsOps A]

/-- Result of abstract expression evaluation. -/
structure ERes (A : Type) where
  st : AState A
  val : A
  al : List Kind

/-- Result of abstract statement execution, one state per status. -/
structure SRes (A : Type) where
  norm : AState A
  brk : AState A
  cont : AState A
  ret : AState A
  retv : A
  al : List Kind

/-- Unreachable expression result. -/
def ERes.none : ERes A := ⟨.bot, top, []⟩

/-- A statement result that completes normally in `σ`. -/
def SRes.normal (σ : AState A) (al : List Kind := []) : SRes A :=
  ⟨σ, .bot, .bot, .bot, top, al⟩

/-- Join of returned values, ignoring an unreachable side. -/
def joinRet (σ₁ : AState A) (v₁ : A) (σ₂ : AState A) (v₂ : A) : A :=
  if σ₁.isBot then v₂ else if σ₂.isBot then v₁ else join v₁ v₂

/-- Join of statement results. -/
def SRes.join (r r' : SRes A) : SRes A :=
  ⟨r.norm.join r'.norm, r.brk.join r'.brk, r.cont.join r'.cont, r.ret.join r'.ret,
    joinRet r.ret r.retv r'.ret r'.retv, r.al ∪ r'.al⟩

/-! ## Conditions -/

/-- Expressions whose evaluation cannot change the state. -/
def isPure : Expr → Bool
  | .int _ | .str _ | .bool _ | .null | .var _ => true
  | .binary _ l r | .logical _ l r => isPure l && isPure r
  | .unary _ e => isPure e
  | _ => false

/-- Abstract value of a literal or variable operand. -/
def pureVal (σ : AState A) : Expr → Option A
  | .int n => some (ofValue (.int n))
  | .str s => some (ofValue (.str s))
  | .bool b => some (ofValue (.bool b))
  | .null => some (ofValue .null)
  | .var x => some (σ.lookup x).1
  | _ => none

/-- Refine `σ` (the state after evaluating the pure condition `c`) knowing
that `c`'s value has truthiness `t`. -/
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

/-- Branch states after a condition with abstract value `a`. -/
def branch (t : Bool) (c : Expr) (r : ERes A) : AState A :=
  if (if t then mayT r.val else mayF r.val) then filterE t r.st c else .bot

/-! ## Expressions -/

/-- `assert`'s arguments certainly pass. -/
def assertOk : List A → Bool
  | [a] => !mayF a
  | [a, _] => !mayF a
  | _ => false

/-- State after calling a value of `a`: natives keep the state; other
callees are not analysed. -/
def callSt (a : A) (σ : AState A) : AState A :=
  match asNative a with
  | some _ => σ
  | none => if σ.isBot then .bot else .top

/-- Result of calling a value of `a`. -/
def callVal (a : A) : A :=
  match asNative a with
  | some _ => ofValue .null
  | none => top

/-- Errors a call of a value of `a` on arguments `avs` may raise. -/
def callAl (a : A) (avs : List A) : List Kind :=
  match asNative a with
  | some .assert => if assertOk avs then [] else [.assert]
  | some _ => []
  | none => Kind.inCall

mutual

/-- Abstract `eval_expr`; unreachable states give unreachable results. -/
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

/-- Abstract left-to-right argument evaluation. -/
def aevalArgs (σ : AState A) : List Expr → AState A × List A × List Kind
  | [] => (σ, [], [])
  | e :: es =>
    let re := aeval σ e
    let rs := aevalArgs re.st es
    (rs.1, re.val :: rs.2.1, re.al ∪ rs.2.2)

end

/-! ## Loops -/

/-- One abstract loop iteration from head state `I`. -/
structure LStep (A : Type) where
  /-- States leaving the loop normally in this iteration. -/
  exitN : AState A
  ret : AState A
  retv : A
  /-- Head state of the next iteration. -/
  next : AState A
  al : List Kind

/-- The completions of one iteration. -/
def LStep.out (r : LStep A) : SRes A := ⟨r.exitN, .bot, .bot, r.ret, r.retv, r.al⟩

/-- Widening iteration towards a post-fixpoint of `F` above `J`. -/
def fixIter (F : AState A → AState A) : Nat → AState A → AState A
  | 0, J => J
  | n + 1, J => if (F J).le J then J else fixIter F n (J.widen (F J))

/-- `J` is a post-fixpoint of `F` above `I`. -/
def isPost (F : AState A → AState A) (I J : AState A) : Bool := I.le J && (F J).le J

/-- Narrowing: replace a post-fixpoint `J` by `I ⊔ F J` while that is still a
post-fixpoint. -/
def narrowIter (F : AState A → AState A) (I : AState A) : Nat → AState A → AState A
  | 0, J => J
  | n + 1, J => if isPost F I (I.join (F J)) then narrowIter F I n (I.join (F J)) else J

/-- A checked post-fixpoint of `F` above `I`, narrowed, or `⊤`. -/
def postFix (F : AState A → AState A) (fuel narrow : Nat) (I : AState A) : AState A :=
  if isPost F I (fixIter F fuel I) then narrowIter F I narrow (fixIter F fuel I) else .top

/-- Abstract loop: up to `k` unrolled iterations, then a post-fixpoint. An
unrolled head state whose successor it already covers is a post-fixpoint. -/
def loopAbs (cfg : Cfg) (F : AState A → LStep A) : Nat → AState A → SRes A
  | 0, I => (F (postFix (fun J => (F J).next) cfg.widenFuel cfg.narrowFuel I)).out
  | k + 1, I =>
    if (F I).next.isBot || (F I).next.le I then (F I).out
    else (F I).out.join (loopAbs cfg F k (F I).next)

/-- One `while` iteration. -/
def whileStep (evalC : AState A → ERes A) (c : Expr) (execB : AState A → SRes A)
    (I : AState A) : LStep A :=
  let rc := evalC I
  let rb := execB (branch true c rc)
  ⟨(branch false c rc).join rb.brk, rb.ret, rb.retv, rb.norm.join rb.cont, rc.al ∪ rb.al⟩

/-- One `for` iteration: condition, body, step. -/
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

/-! ## Statements -/

/-- Abstract evaluation of an optional expression. -/
def optEval (e : Option Expr) (I : AState A) : ERes A :=
  match e with
  | none => ERes.none
  | some e => aeval I e

/-- Sequencing: `r'` runs from `r.norm`; abrupt completions of `r` are kept. -/
def SRes.seq (r r' : SRes A) : SRes A :=
  { r' with brk := r.brk.join r'.brk, cont := r.cont.join r'.cont,
            ret := r.ret.join r'.ret, retv := joinRet r.ret r.retv r'.ret r'.retv,
            al := r.al ∪ r'.al }

/-- Pop the loop/block scope from every completion. -/
def SRes.pop (r : SRes A) : SRes A :=
  ⟨r.norm.pop, r.brk.pop, r.cont.pop, r.ret.pop, r.retv, r.al⟩

/-- Every completion state of a result. -/
def SRes.any (r : SRes A) : AState A := ((r.norm.join r.brk).join r.cont).join r.ret

mutual

/-- Abstract `exec_stmt`. -/
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

/-- Abstract execution of an optional statement (absent: completes normally). -/
def aexecOpt (cfg : Cfg) (σ : AState A) : Option Stmt → SRes A
  | none => SRes.normal σ
  | some s => aexec cfg σ s

/-- Abstract statement sequence. -/
def aexecSeq (cfg : Cfg) (σ : AState A) : List Stmt → SRes A
  | [] => SRes.normal σ
  | s :: ss =>
    let r := aexec cfg σ s
    SRes.seq r (aexecSeq cfg r.norm ss)

end

/-- The iteration of `while (c) b`. -/
def whileF (cfg : Cfg) (c : Expr) (b : Stmt) : AState A → LStep A :=
  whileStep (fun I => aeval I c) c (fun I => aexec cfg I b)

/-- The iteration of `for (…; cnd; step) b`. -/
def forF (cfg : Cfg) (cnd step : Option Expr) (b : Stmt) : AState A → LStep A :=
  forStep (optEval cnd) cnd (fun I => aexec cfg I b) (optEval step) step

/-! ## Programs -/

/-- The abstract initial state: the globals frame with the three natives. -/
def initState : AState A :=
  .sc [[("print", ⟨ofValue (.native .print), true⟩),
        ("println", ⟨ofValue (.native .println), true⟩),
        ("assert", ⟨ofValue (.native .assert), true⟩)]]

/-- Analyse a program from the initial state. -/
def analyze (cfg : Cfg) (p : Program) : SRes A := aexecSeq cfg initState p

/-- The alarms of a program: every error kind the analysis cannot exclude,
including an abrupt top-level completion. -/
def alarms (cfg : Cfg) (p : Program) : List Kind :=
  let r := analyze (A := A) cfg p
  r.al ∪ if r.brk.isBot && r.cont.isBot && r.ret.isBot then [] else [.abrupt]

end Vsa.AbsInt
