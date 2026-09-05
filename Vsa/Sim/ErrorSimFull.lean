import Vsa.Sim.ErrorSim
import Vsa.Sim.TermSimAssembly

/-!
# Layer 5 — the FULL error forward-simulation assembly (`errorSim_of_sites`)

`Vsa/Sim/ErrorSim.lean` proved `errorTailHalts` (Part A: the reusable
`runtime_error → exit(70)` chain) and `errorSim_execSeq` (Part B for the single
`ExecSeqErr` relation).  This file **widens Part B to the full six-relation
mutual error judgment** (`EvalErr`/`EvalArgsErr`/`CallErr`/`ExecErr`/
`ForLoopErr`/`ExecSeqErr`, `Vsa/While/ErrorSem.lean`) by applying the mutual
recursor `@ExecSeqErr.rec`, exactly as `TermSimAssembly.term_sim_of_cases`
applies `@EvalE.rec`.

## The assembly

Every one of the six recursor motives is the *constant* `ErrHalts c :=
∃ out, Halts c out 70` — the recursor node (the derivation) and every sub-IH are
ignored, precisely as `term_sim_of_cases`'s motives ignore the derivation.  With
all six motives constant, each minor premise of `@ExecSeqErr.rec` is the residual
"this error node's compiled code reaches a `jal runtime_error` site and hence a
`Halts c out 70`" — taken here as an explicit hypothesis, one per error
constructor (44 total).  For a *recursive* error constructor (e.g.
`ExecSeqErr.tail`, `CallErr.body`, the `EvalErr`/`ExecErr`/`ForLoopErr`
propagation rules) the recursor additionally supplies the sub-derivation's
`ErrHalts c` as an IH; since the motive is constant those IHs are already
`ErrHalts c`, and the hypothesis may either use them or reach a fresh
`runtime_error` site directly.

`errorSim_of_sites` is the full six-motive `@ExecSeqErr.rec` application: it
TYPE-CHECKS iff the six constant `ErrHalts` motives compose through every
constructor of the mutual family.  `errorSimFull` specializes it to the top-level
`BigStepErr p = ExecSeqErr initSt 0 0 p`, and `stuck_of_bigStepErrFull` composes it
into `stuck_sim`'s nonzero-halt disjunct via `stuck_of_halts_70`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail
open Register
open Vsa.Machine (Config Halts)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr (NativeAddrs Arena)
open Vsa.Alloc (StackLayout)
open Vsa.While

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. Entry-indexed error motives

Each motive starts from the machine entry for that semantic node.  Recursive
constructors must therefore provide a real parent-to-child-to-resume seam;
they cannot reuse a child halt at an unrelated configuration. -/

/-- One reusable recursive machine seam.  The predicates close over the exact
parent and child semantic indices. -/
structure ChildSeam
    (parent childEntry childExit resumeEntry done : Config → Prop) : Prop where
  dispatch : Triple parent childEntry
  resume_ready : ∀ c, childExit c → resumeEntry c
  resume : Triple resumeEntry done

theorem ChildSeam.run
    {parent childEntry childExit resumeEntry done : Config → Prop}
    (seam : ChildSeam parent childEntry childExit resumeEntry done)
    (child : Triple childEntry childExit) : Triple parent done := by
  intro c hc
  obtain ⟨cChild, hsDispatch, hChild⟩ := seam.dispatch c hc
  obtain ⟨cRet, hsChild, hRet⟩ := child cChild hChild
  obtain ⟨cDone, hsResume, hDone⟩ :=
    seam.resume cRet (seam.resume_ready cRet hRet)
  exact ⟨cDone, hsDispatch.trans (hsChild.trans hsResume), hDone⟩

/-- Prepending machine steps preserves an exit-70 result. -/
theorem errHalts_of_steps {c c' : Config} (hs : Vsa.Machine.Steps c c') :
    ErrHalts c' → ErrHalts c := by
  rintro ⟨out, cf, σf, hs', hh, hout⟩
  exact ⟨out, cf, σf, hs.trans hs', hh, hout⟩

/-- `EvalErr` at the ordinary `eval_expr` entry. -/
def EvalErrI (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) : Prop :=
  ∀ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r sret aEnv aExpr : BitVec 64) (c : Config),
    EvalEntry g N A SL φf φc st d env e sp r sret aEnv aExpr m0 c → ErrHalts c

/-- `EvalArgsErr` at the exact prefix-indexed argument-loop entry. -/
def EvalArgsErrI (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (env : Addr) (es : List Expr) : Prop :=
  ∀ (esPrefix : List Expr) (vsPrefix : List Value),
    esPrefix.length = vsPrefix.length →
  ∀ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (c : Config),
    EvalArgsPrefixEntryI g N A SL φf φc st d env
      esPrefix es vsPrefix dLeft aLeft m0 c → ErrHalts c

/-- `CallErr` at the value-dispatch entry. -/
def CallErrI (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value) : Prop :=
  ∀ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (dLeft aLeft : Nat) (sp sret : BitVec 64) (c : Config),
    CallEntryI g N A SL φf φc st d fv vs dLeft aLeft sp sret m0 c → ErrHalts c

/-- `ExecErr` at `exec_stmt` entry. -/
def ExecErrI (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) : Prop :=
  ∀ (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (sp r aInterp aStmt aEnv aRet : BitVec 64) (c : Config),
    ExecEntry g N A SL φf φc st d env s
      sp r aInterp aStmt aEnv aRet m0 c → ErrHalts c

/-- `ForLoopErr` at the concrete for-loop header. -/
def ForLoopErrI (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr)
    (body : Stmt) : Prop :=
  ∀ (init : Option Stmt) (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat) (sp r aInterp aStmt aEnv aRet : BitVec 64)
    (ment : Vsa.MemRepr.Mem) (c : Config),
    (∃ liveRA, TermSimAssembly.ForLoopReady g N A SL φf φc st d env
      init cnd step body sp r aInterp aStmt aEnv aRet m0 ment c
        (liveRA := liveRA)) → ErrHalts c

/-- `ExecSeqErr` at one of the three physical sequence-loop copies. -/
def ExecSeqErrI (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) : Prop :=
  ∀ (copy : ExecSeqCopy) (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat) (sp aRet : BitVec 64) (c : Config),
    ExecSeqEntryI copy g N A SL φf φc st d env ss sp aRet m0 c → ErrHalts c

def mEvalErr (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (env : Addr) (e : Expr)
    (_h : EvalErr st d env e) : Prop := EvalErrI g m0 st d env e

def mEvalArgsErr (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (env : Addr) (es : List Expr)
    (_h : EvalArgsErr st d env es) : Prop := EvalArgsErrI g m0 st d env es

def mCallErr (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value)
    (_h : CallErr st d fv vs) : Prop := CallErrI g m0 st d fv vs

def mExecErr (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt)
    (_h : ExecErr st d env s) : Prop := ExecErrI g m0 st d env s

def mForLoopErr (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (env : Addr) (cnd step : Option Expr)
    (body : Stmt) (_h : ForLoopErr st d env cnd step body) : Prop :=
  ForLoopErrI g m0 st d env cnd step body

def mExecSeqErr (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt)
    (_h : ExecSeqErr st d env ss) : Prop := ExecSeqErrI g m0 st d env ss

/-- The indexed `EvalErr.callTooMany` constructor seam. -/
def CallTooManyCaseI
    (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem) : Prop :=
  ∀ st d env f args st' fv, EvalE st d env f st' fv →
    maxArgs < args.length → EvalErrI g m0 st d env (.call f args)

/-- The remaining constructor seams for the six entry-indexed error motives.
The compiled `callTooMany` seam is a parameter, so it cannot be replaced by an
unrelated arbitrary-configuration leaf obligation.  Every other field is
an executable parent/child composition obligation, not a free halt at an
unrelated configuration. -/
structure ErrorCasesI
    (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (_hCallTooMany : CallTooManyCaseI g m0) : Prop where
  hVarUndef : ∀ st d env x, st.store.get? env x = none →
    EvalErrI g m0 st d env (.var x)
  hAssignE : ∀ st d env x e, EvalErr st d env e → EvalErrI g m0 st d env e →
    EvalErrI g m0 st d env (.assign x e)
  hAssignUnbound : ∀ st d env x e st' v, EvalE st d env e st' v →
    st'.store.set? env x v = none → EvalErrI g m0 st d env (.assign x e)
  hBinaryL : ∀ st d env op l r, EvalErr st d env l → EvalErrI g m0 st d env l →
    EvalErrI g m0 st d env (.binary op l r)
  hBinaryR : ∀ st d env op l r st' lv, EvalE st d env l st' lv →
    EvalErr st' d env r → EvalErrI g m0 st' d env r →
    EvalErrI g m0 st d env (.binary op l r)
  hBinaryOp : ∀ st d env op l r st' st'' lv rv,
    EvalE st d env l st' lv → EvalE st' d env r st'' rv →
    binOpSem st''.store op lv rv = none → EvalErrI g m0 st d env (.binary op l r)
  hOrL : ∀ st d env l r, EvalErr st d env l → EvalErrI g m0 st d env l →
    EvalErrI g m0 st d env (.logical .or l r)
  hOrR : ∀ st d env l r st' lv, EvalE st d env l st' lv → lv.truthy = false →
    EvalErr st' d env r → EvalErrI g m0 st' d env r →
    EvalErrI g m0 st d env (.logical .or l r)
  hAndL : ∀ st d env l r, EvalErr st d env l → EvalErrI g m0 st d env l →
    EvalErrI g m0 st d env (.logical .and l r)
  hAndR : ∀ st d env l r st' lv, EvalE st d env l st' lv → lv.truthy = true →
    EvalErr st' d env r → EvalErrI g m0 st' d env r →
    EvalErrI g m0 st d env (.logical .and l r)
  hUnaryE : ∀ st d env op e, EvalErr st d env e → EvalErrI g m0 st d env e →
    EvalErrI g m0 st d env (.unary op e)
  hNegType : ∀ st d env e st' v, EvalE st d env e st' v →
    (∀ n : Int, v ≠ .int n) → EvalErrI g m0 st d env (.unary .neg e)
  hCallF : ∀ st d env f args, EvalErr st d env f → EvalErrI g m0 st d env f →
    EvalErrI g m0 st d env (.call f args)
  hCallArgs : ∀ st d env f args st' fv, EvalE st d env f st' fv →
    args.length ≤ maxArgs → EvalArgsErr st' d env args →
    EvalArgsErrI g m0 st' d env args → EvalErrI g m0 st d env (.call f args)
  hCallC : ∀ st d env f args st' st'' fv vs, EvalE st d env f st' fv →
    args.length ≤ maxArgs → EvalArgs st' d env args st'' vs →
    CallErr st'' d fv vs → CallErrI g m0 st'' d fv vs →
    EvalErrI g m0 st d env (.call f args)
  hArgsHead : ∀ st d env e es, EvalErr st d env e → EvalErrI g m0 st d env e →
    EvalArgsErrI g m0 st d env (e :: es)
  hArgsTail : ∀ st d env e es st' v, EvalE st d env e st' v →
    EvalArgsErr st' d env es → EvalArgsErrI g m0 st' d env es →
    EvalArgsErrI g m0 st d env (e :: es)
  hNotCallable : ∀ st d fv vs, (∀ a, fv ≠ .closure a) →
    (∀ f, fv ≠ .native f) → CallErrI g m0 st d fv vs
  hBadClosure : ∀ st d a vs, st.store.closures[a]? = none →
    CallErrI g m0 st d (.closure a) vs
  hArity : ∀ st d a cd vs, st.store.closures[a]? = some cd →
    vs.length ≠ cd.params.length → CallErrI g m0 st d (.closure a) vs
  hDepth : ∀ st d a cd vs, st.store.closures[a]? = some cd →
    vs.length = cd.params.length → ¬ d < maxCallDepth →
    CallErrI g m0 st d (.closure a) vs
  hBody : ∀ st d a cd vs store' frame, st.store.closures[a]? = some cd →
    vs.length = cd.params.length → d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    ∀ h : ExecSeqErr ⟨(cd.params.zip vs).foldl
      (fun s xv => s.define frame xv.1 xv.2) store', st.out⟩ (d + 1) frame cd.body,
    ExecSeqErrI g m0 ⟨(cd.params.zip vs).foldl
      (fun s xv => s.define frame xv.1 xv.2) store', st.out⟩ (d + 1) frame cd.body →
    CallErrI g m0 st d (.closure a) vs
  hEscape : ∀ st d a cd vs store' frame st' status,
    st.store.closures[a]? = some cd → vs.length = cd.params.length →
    d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeq ⟨(cd.params.zip vs).foldl
      (fun s xv => s.define frame xv.1 xv.2) store', st.out⟩
      (d + 1) frame cd.body st' status →
    (status = .brk ∨ status = .cont) → CallErrI g m0 st d (.closure a) vs
  hAssertFail : ∀ st d vs v msg, (vs = [v] ∨ vs = [v, msg]) →
    v.truthy = false → CallErrI g m0 st d (.native .assert) vs
  hAssertArity : ∀ st d vs, (∀ v, vs ≠ [v]) → (∀ v msg, vs ≠ [v, msg]) →
    CallErrI g m0 st d (.native .assert) vs
  hExpr : ∀ st d env e, EvalErr st d env e → EvalErrI g m0 st d env e →
    ExecErrI g m0 st d env (.expr e)
  hVarInit : ∀ st d env x e, EvalErr st d env e → EvalErrI g m0 st d env e →
    ExecErrI g m0 st d env (.varDecl x (some e))
  hBlock : ∀ st d env ss store' inner,
    st.store.allocFrame (some env) = (store', inner) →
    ∀ h : ExecSeqErr ⟨store', st.out⟩ d inner ss,
    ExecSeqErrI g m0 ⟨store', st.out⟩ d inner ss →
    ExecErrI g m0 st d env (.block ss)
  hIfCond : ∀ st d env cnd t e, EvalErr st d env cnd →
    EvalErrI g m0 st d env cnd → ExecErrI g m0 st d env (.ifStmt cnd t e)
  hIfThen : ∀ st d env cnd t e st' v, EvalE st d env cnd st' v →
    v.truthy = true → ExecErr st' d env t → ExecErrI g m0 st' d env t →
    ExecErrI g m0 st d env (.ifStmt cnd t e)
  hIfElse : ∀ st d env cnd t e st' v, EvalE st d env cnd st' v →
    v.truthy = false → ExecErr st' d env e → ExecErrI g m0 st' d env e →
    ExecErrI g m0 st d env (.ifStmt cnd t (some e))
  hWhileCond : ∀ st d env cnd body, EvalErr st d env cnd →
    EvalErrI g m0 st d env cnd → ExecErrI g m0 st d env (.whileStmt cnd body)
  hWhileBody : ∀ st d env cnd body st' v, EvalE st d env cnd st' v →
    v.truthy = true → ExecErr st' d env body → ExecErrI g m0 st' d env body →
    ExecErrI g m0 st d env (.whileStmt cnd body)
  hWhileLoop : ∀ st d env cnd body st' st'' v status,
    EvalE st d env cnd st' v → v.truthy = true →
    ExecS st' d env body st'' status → (status = .normal ∨ status = .cont) →
    ExecErr st'' d env (.whileStmt cnd body) →
    ExecErrI g m0 st'' d env (.whileStmt cnd body) →
    ExecErrI g m0 st d env (.whileStmt cnd body)
  hForInit : ∀ st d env init cnd step body store' outer,
    st.store.allocFrame (some env) = (store', outer) →
    ExecErr ⟨store', st.out⟩ d outer init →
    ExecErrI g m0 ⟨store', st.out⟩ d outer init →
    ExecErrI g m0 st d env (.forStmt (some init) cnd step body)
  hForLoop : ∀ st d env init cnd step body store' outer st',
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    ForLoopErr st' d outer cnd step body →
    ForLoopErrI g m0 st' d outer cnd step body →
    ExecErrI g m0 st d env (.forStmt init cnd step body)
  hRet : ∀ st d env e, EvalErr st d env e → EvalErrI g m0 st d env e →
    ExecErrI g m0 st d env (.ret (some e))
  hFlCond : ∀ st d env cnd step body, EvalErr st d env cnd →
    EvalErrI g m0 st d env cnd →
    ForLoopErrI g m0 st d env (some cnd) step body
  hFlBody : ∀ st d env cnd step body st', ForCond st d env cnd st' →
    ExecErr st' d env body → ExecErrI g m0 st' d env body →
    ForLoopErrI g m0 st d env cnd step body
  hFlStep : ∀ st d env cnd e body st' st'' status,
    ForCond st d env cnd st' → ExecS st' d env body st'' status →
    (status = .normal ∨ status = .cont) → EvalErr st'' d env e →
    EvalErrI g m0 st'' d env e →
    ForLoopErrI g m0 st d env cnd (some e) body
  hFlLoop : ∀ st d env cnd step body st' st'' st''' status,
    ForCond st d env cnd st' → ExecS st' d env body st'' status →
    (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
    ForLoopErr st''' d env cnd step body →
    ForLoopErrI g m0 st''' d env cnd step body →
    ForLoopErrI g m0 st d env cnd step body
  hSeqHead : ∀ st d env s ss, ExecErr st d env s → ExecErrI g m0 st d env s →
    ExecSeqErrI g m0 st d env (s :: ss)
  hSeqTail : ∀ st d env s ss st', ExecS st d env s st' .normal →
    ExecSeqErr st' d env ss → ExecSeqErrI g m0 st' d env ss →
    ExecSeqErrI g m0 st d env (s :: ss)

/-! ## §2. The assembled mutual induction — `errorSim_of_sites`

The full six-motive `@ExecSeqErr.rec` application with the constant `ErrHalts`
motives.  Each of the 44 minor premises is an explicit hypothesis, in the exact
∀-closed shape the recursor demands: the constructor's arguments (including its
sub-derivation proofs), then the sub-derivation IHs in the (constant) motive
shape (`ErrHalts c`), then the (constant) motive conclusion `ErrHalts c`.

Because every motive is constant `ErrHalts c`, every minor premise is precisely
the per-error-site residual "reaching this error node's compiled code reaches a
`jal runtime_error` site ⇒ `Halts c out 70`" (for recursive nodes, with the
sub-node's `ErrHalts c` additionally available as an IH argument).  The
hypothesis names below record the constructor ↔ residual mapping:

* EvalErr (16): hVarUndef, hAssignE, hAssignUnbound, hBinaryL, hBinaryR,
  hBinaryOp, hOrL, hOrR, hAndL, hAndR, hUnaryE, hNegType, hCallF, hCallArgs,
  hCallTooMany, hCallC.
* EvalArgsErr (2): hArgsHead, hArgsTail.
* CallErr (8): hNotCallable, hBadClosure, hArity, hDepth, hBody, hEscape,
  hAssertFail, hAssertArity.
* ExecErr (12): hExpr, hVarInit, hBlock, hIfCond, hIfThen, hIfElse, hWhileCond,
  hWhileBody, hWhileLoop, hForInit, hForLoop, hRet.
* ForLoopErr (4): hFlCond, hFlBody, hFlStep, hFlLoop.
* ExecSeqErr (2): hSeqHead, hSeqTail.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`. -/

/- The former constant-motive assembly is retained below only as source-history
while the indexed interface is migrated.  It is deliberately not elaborated.
theorem errorSim_of_sites
    -- EvalErr constructors -------------------------------------------------
    (hVarUndef : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      st.store.get? env x = none → ErrHalts c)
    (hAssignE : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hAssignUnbound : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → st'.store.set? env x v = none → ErrHalts c)
    (hBinaryL : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hBinaryR : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' : SpecSt) (lv : Value),
      EvalE st d env l st' lv → EvalErr st' d env r → ErrHalts c → ErrHalts c)
    (hBinaryOp : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → EvalE st' d env r st'' rv →
      binOpSem st''.store op lv rv = none → ErrHalts c)
    (hOrL : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hOrR : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt)
      (lv : Value),
      EvalE st d env l st' lv → lv.truthy = false → EvalErr st' d env r →
      ErrHalts c → ErrHalts c)
    (hAndL : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hAndR : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt)
      (lv : Value),
      EvalE st d env l st' lv → lv.truthy = true → EvalErr st' d env r →
      ErrHalts c → ErrHalts c)
    (hUnaryE : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : UnOp) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hNegType : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ErrHalts c)
    (hCallF : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr),
      EvalErr st d env f → ErrHalts c → ErrHalts c)
    (hCallTooMany : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr)
      (args : List Expr) (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → maxArgs < args.length → ErrHalts c)
    (hCallArgs : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → args.length ≤ maxArgs →
      EvalArgsErr st' d env args → ErrHalts c → ErrHalts c)
    (hCallC : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : SpecSt) (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → args.length ≤ maxArgs →
      EvalArgs st' d env args st'' vs →
      CallErr st'' d fv vs → ErrHalts c → ErrHalts c)
    -- EvalArgsErr constructors ---------------------------------------------
    (hArgsHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hArgsTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalArgsErr st' d env es → ErrHalts c → ErrHalts c)
    -- CallErr constructors -------------------------------------------------
    (hNotCallable : ∀ (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value),
      (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) → ErrHalts c)
    -- Dangling closure address (`CallErr.badClosure`, the leaf added by the
    -- landed amendment; `st.store.closures[a]? = none`).  Same exit-70
    -- constant-motive shape as the other CallErr sites; unreachable from a
    -- well-formed `initSt` but demanded by the `@ExecSeqErr.rec` minor premises.
    (hBadClosure : ∀ (st : SpecSt) (d : Nat) (a : Addr) (vs : List Value),
      st.store.closures[a]? = none → ErrHalts c)
    (hArity : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length ≠ cd.params.length → ErrHalts c)
    (hDepth : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      ¬ d < maxCallDepth → ErrHalts c)
    (hBody : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeqErr ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body → ErrHalts c → ErrHalts c)
    (hEscape : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body st' status →
      (status = .brk ∨ status = .cont) → ErrHalts c)
    (hAssertFail : ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value),
      (vs = [v] ∨ vs = [v, m]) → v.truthy = false → ErrHalts c)
    (hAssertArity : ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) → ErrHalts c)
    -- ExecErr constructors -------------------------------------------------
    (hExpr : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hVarInit : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hBlock : ∀ (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr),
      st.store.allocFrame (some env) = (store', inner) →
      ExecSeqErr ⟨store', st.out⟩ d inner ss → ErrHalts c → ErrHalts c)
    (hIfCond : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t : Stmt)
      (e : Option Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hIfThen : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t : Stmt)
      (e : Option Stmt) (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → ExecErr st' d env t →
      ErrHalts c → ErrHalts c)
    (hIfElse : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t e : Stmt)
      (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = false → ExecErr st' d env e →
      ErrHalts c → ErrHalts c)
    (hWhileCond : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hWhileBody : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt)
      (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → ExecErr st' d env b →
      ErrHalts c → ErrHalts c)
    (hWhileLoop : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt)
      (st' st'' : SpecSt) (v : Value) (status : Status),
      EvalE st d env cnd st' v → v.truthy = true → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecErr st'' d env (.whileStmt cnd b) →
      ErrHalts c → ErrHalts c)
    (hForInit : ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Stmt) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr),
      st.store.allocFrame (some env) = (store', outer) →
      ExecErr ⟨store', st.out⟩ d outer init → ErrHalts c → ErrHalts c)
    (hForLoop : ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' : SpecSt),
      st.store.allocFrame (some env) = (store', outer) →
      ExecInit ⟨store', st.out⟩ d outer init st' →
      ForLoopErr st' d outer cnd step b → ErrHalts c → ErrHalts c)
    (hRet : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    -- ForLoopErr constructors ----------------------------------------------
    (hFlCond : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (step : Option Expr)
      (b : Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hFlBody : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' : SpecSt),
      ForCond st d env cnd st' → ExecErr st' d env b → ErrHalts c → ErrHalts c)
    (hFlStep : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr) (e : Expr)
      (b : Stmt) (st' st'' : SpecSt) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → EvalErr st'' d env e → ErrHalts c → ErrHalts c)
    (hFlLoop : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' : SpecSt) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
      ForLoopErr st''' d env cnd step b → ErrHalts c → ErrHalts c)
    -- ExecSeqErr constructors ----------------------------------------------
    (hSeqHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt),
      ExecErr st d env s → ErrHalts c → ErrHalts c)
    (hSeqTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : SpecSt),
      ExecS st d env s st' .normal → ExecSeqErr st' d env ss → ErrHalts c → ErrHalts c)
    -- the target: an arbitrary ExecSeqErr node reaches `ErrHalts c` -------
    {st : SpecSt} {d : Nat} {env : Addr} {ss : List Stmt}
    (h : ExecSeqErr st d env ss) : ErrHalts c :=
  @ExecSeqErr.rec (mEvalErr c) (mEvalArgsErr c) (mCallErr c) (mExecErr c)
    (mForLoopErr c) (mExecSeqErr c)
    hVarUndef hAssignE hAssignUnbound hBinaryL hBinaryR hBinaryOp hOrL hOrR hAndL
    hAndR hUnaryE hNegType hCallF hCallTooMany hCallArgs hCallC
    hArgsHead hArgsTail
    hNotCallable hBadClosure hArity hDepth hBody hEscape hAssertFail hAssertArity
    hExpr hVarInit hBlock hIfCond hIfThen hIfElse hWhileCond hWhileBody hWhileLoop
    hForInit hForLoop hRet
    hFlCond hFlBody hFlStep hFlLoop
    hSeqHead hSeqTail
    st d env ss h

/-! ## §3. Program-level specialization and `stuck_sim` composition -/

/-- **Full error simulation, program level.**  Specializing `errorSim_of_sites`
to the top-level `BigStepErr p = ExecSeqErr initSt 0 0 p` yields the whole-program
error simulation, conditional only on the 44 per-error-site residuals. -/
theorem errorSimFull (p : Program)
    (hVarUndef : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      st.store.get? env x = none → ErrHalts c)
    (hAssignE : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hAssignUnbound : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → st'.store.set? env x v = none → ErrHalts c)
    (hBinaryL : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hBinaryR : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' : SpecSt) (lv : Value),
      EvalE st d env l st' lv → EvalErr st' d env r → ErrHalts c → ErrHalts c)
    (hBinaryOp : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → EvalE st' d env r st'' rv →
      binOpSem st''.store op lv rv = none → ErrHalts c)
    (hOrL : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hOrR : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt)
      (lv : Value),
      EvalE st d env l st' lv → lv.truthy = false → EvalErr st' d env r →
      ErrHalts c → ErrHalts c)
    (hAndL : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hAndR : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt)
      (lv : Value),
      EvalE st d env l st' lv → lv.truthy = true → EvalErr st' d env r →
      ErrHalts c → ErrHalts c)
    (hUnaryE : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : UnOp) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hNegType : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ErrHalts c)
    (hCallF : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr),
      EvalErr st d env f → ErrHalts c → ErrHalts c)
    (hCallTooMany : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr)
      (args : List Expr) (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → maxArgs < args.length → ErrHalts c)
    (hCallArgs : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → args.length ≤ maxArgs →
      EvalArgsErr st' d env args → ErrHalts c → ErrHalts c)
    (hCallC : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : SpecSt) (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → args.length ≤ maxArgs →
      EvalArgs st' d env args st'' vs →
      CallErr st'' d fv vs → ErrHalts c → ErrHalts c)
    (hArgsHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hArgsTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalArgsErr st' d env es → ErrHalts c → ErrHalts c)
    (hNotCallable : ∀ (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value),
      (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) → ErrHalts c)
    -- Dangling closure address (`CallErr.badClosure`); see
    -- `errorSim_of_sites`.
    (hBadClosure : ∀ (st : SpecSt) (d : Nat) (a : Addr) (vs : List Value),
      st.store.closures[a]? = none → ErrHalts c)
    (hArity : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length ≠ cd.params.length → ErrHalts c)
    (hDepth : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      ¬ d < maxCallDepth → ErrHalts c)
    (hBody : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeqErr ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body → ErrHalts c → ErrHalts c)
    (hEscape : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body st' status →
      (status = .brk ∨ status = .cont) → ErrHalts c)
    (hAssertFail : ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value),
      (vs = [v] ∨ vs = [v, m]) → v.truthy = false → ErrHalts c)
    (hAssertArity : ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) → ErrHalts c)
    (hExpr : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hVarInit : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hBlock : ∀ (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr),
      st.store.allocFrame (some env) = (store', inner) →
      ExecSeqErr ⟨store', st.out⟩ d inner ss → ErrHalts c → ErrHalts c)
    (hIfCond : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t : Stmt)
      (e : Option Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hIfThen : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t : Stmt)
      (e : Option Stmt) (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → ExecErr st' d env t →
      ErrHalts c → ErrHalts c)
    (hIfElse : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t e : Stmt)
      (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = false → ExecErr st' d env e →
      ErrHalts c → ErrHalts c)
    (hWhileCond : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hWhileBody : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt)
      (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → ExecErr st' d env b →
      ErrHalts c → ErrHalts c)
    (hWhileLoop : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt)
      (st' st'' : SpecSt) (v : Value) (status : Status),
      EvalE st d env cnd st' v → v.truthy = true → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecErr st'' d env (.whileStmt cnd b) →
      ErrHalts c → ErrHalts c)
    (hForInit : ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Stmt) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr),
      st.store.allocFrame (some env) = (store', outer) →
      ExecErr ⟨store', st.out⟩ d outer init → ErrHalts c → ErrHalts c)
    (hForLoop : ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' : SpecSt),
      st.store.allocFrame (some env) = (store', outer) →
      ExecInit ⟨store', st.out⟩ d outer init st' →
      ForLoopErr st' d outer cnd step b → ErrHalts c → ErrHalts c)
    (hRet : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hFlCond : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (step : Option Expr)
      (b : Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hFlBody : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' : SpecSt),
      ForCond st d env cnd st' → ExecErr st' d env b → ErrHalts c → ErrHalts c)
    (hFlStep : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr) (e : Expr)
      (b : Stmt) (st' st'' : SpecSt) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → EvalErr st'' d env e → ErrHalts c → ErrHalts c)
    (hFlLoop : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' : SpecSt) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
      ForLoopErr st''' d env cnd step b → ErrHalts c → ErrHalts c)
    (hSeqHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt),
      ExecErr st d env s → ErrHalts c → ErrHalts c)
    (hSeqTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : SpecSt),
      ExecS st d env s st' .normal → ExecSeqErr st' d env ss → ErrHalts c → ErrHalts c)
    -- The separate top-level error route: an `ExecSeq` completing with an abrupt
    -- status (`TopAbrupt p`, the new `BigStepErr` disjunct — `interp_run`,
    -- `c/src/interp.c:333-361`, prints `runtime error` and `exit 70`).  Same
    -- exit-70 shape as the 44 constructor residuals; no new machine proof here.
    (hTopAbrupt : TopAbrupt p → ErrHalts c)
    (h : BigStepErr p) : ∃ out, Halts c out 70 := by
  rcases h with hseq | habrupt
  · exact errorSim_of_sites c
      hVarUndef hAssignE hAssignUnbound hBinaryL hBinaryR hBinaryOp hOrL hOrR hAndL
      hAndR hUnaryE hNegType hCallF hCallTooMany hCallArgs hCallC hArgsHead hArgsTail hNotCallable
      hBadClosure hArity hDepth hBody hEscape hAssertFail hAssertArity hExpr hVarInit hBlock hIfCond
      hIfThen hIfElse hWhileCond hWhileBody hWhileLoop hForInit hForLoop hRet hFlCond
      hFlBody hFlStep hFlLoop hSeqHead hSeqTail hseq
  · exact hTopAbrupt habrupt

/-- **Discharging `stuck_sim`'s error disjunct (full assembly).**  From the full
six-relation error simulation and `stuck_of_halts_70`, a program that hits any
runtime error lands in `stuck_sim`'s nonzero-halt disjunct.  This composes
`errorSimFull` (any error node → `Halts c out 70`) with the machine-side exit-code
faithfulness gadget. -/
theorem stuck_of_bigStepErrFull (p : Program)
    (hVarUndef : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      st.store.get? env x = none → ErrHalts c)
    (hAssignE : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hAssignUnbound : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → st'.store.set? env x v = none → ErrHalts c)
    (hBinaryL : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hBinaryR : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' : SpecSt) (lv : Value),
      EvalE st d env l st' lv → EvalErr st' d env r → ErrHalts c → ErrHalts c)
    (hBinaryOp : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → EvalE st' d env r st'' rv →
      binOpSem st''.store op lv rv = none → ErrHalts c)
    (hOrL : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hOrR : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt)
      (lv : Value),
      EvalE st d env l st' lv → lv.truthy = false → EvalErr st' d env r →
      ErrHalts c → ErrHalts c)
    (hAndL : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hAndR : ∀ (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt)
      (lv : Value),
      EvalE st d env l st' lv → lv.truthy = true → EvalErr st' d env r →
      ErrHalts c → ErrHalts c)
    (hUnaryE : ∀ (st : SpecSt) (d : Nat) (env : Addr) (op : UnOp) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hNegType : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ErrHalts c)
    (hCallF : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr),
      EvalErr st d env f → ErrHalts c → ErrHalts c)
    (hCallTooMany : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr)
      (args : List Expr) (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → maxArgs < args.length → ErrHalts c)
    (hCallArgs : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → args.length ≤ maxArgs →
      EvalArgsErr st' d env args → ErrHalts c → ErrHalts c)
    (hCallC : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : SpecSt) (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → args.length ≤ maxArgs →
      EvalArgs st' d env args st'' vs →
      CallErr st'' d fv vs → ErrHalts c → ErrHalts c)
    (hArgsHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hArgsTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalArgsErr st' d env es → ErrHalts c → ErrHalts c)
    (hNotCallable : ∀ (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value),
      (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) → ErrHalts c)
    -- Dangling closure address (`CallErr.badClosure`); see
    -- `errorSim_of_sites`.
    (hBadClosure : ∀ (st : SpecSt) (d : Nat) (a : Addr) (vs : List Value),
      st.store.closures[a]? = none → ErrHalts c)
    (hArity : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length ≠ cd.params.length → ErrHalts c)
    (hDepth : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      ¬ d < maxCallDepth → ErrHalts c)
    (hBody : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeqErr ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body → ErrHalts c → ErrHalts c)
    (hEscape : ∀ (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body st' status →
      (status = .brk ∨ status = .cont) → ErrHalts c)
    (hAssertFail : ∀ (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value),
      (vs = [v] ∨ vs = [v, m]) → v.truthy = false → ErrHalts c)
    (hAssertArity : ∀ (st : SpecSt) (d : Nat) (vs : List Value),
      (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) → ErrHalts c)
    (hExpr : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hVarInit : ∀ (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hBlock : ∀ (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr),
      st.store.allocFrame (some env) = (store', inner) →
      ExecSeqErr ⟨store', st.out⟩ d inner ss → ErrHalts c → ErrHalts c)
    (hIfCond : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t : Stmt)
      (e : Option Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hIfThen : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t : Stmt)
      (e : Option Stmt) (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → ExecErr st' d env t →
      ErrHalts c → ErrHalts c)
    (hIfElse : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t e : Stmt)
      (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = false → ExecErr st' d env e →
      ErrHalts c → ErrHalts c)
    (hWhileCond : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hWhileBody : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt)
      (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → ExecErr st' d env b →
      ErrHalts c → ErrHalts c)
    (hWhileLoop : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt)
      (st' st'' : SpecSt) (v : Value) (status : Status),
      EvalE st d env cnd st' v → v.truthy = true → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecErr st'' d env (.whileStmt cnd b) →
      ErrHalts c → ErrHalts c)
    (hForInit : ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Stmt) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr),
      st.store.allocFrame (some env) = (store', outer) →
      ExecErr ⟨store', st.out⟩ d outer init → ErrHalts c → ErrHalts c)
    (hForLoop : ∀ (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' : SpecSt),
      st.store.allocFrame (some env) = (store', outer) →
      ExecInit ⟨store', st.out⟩ d outer init st' →
      ForLoopErr st' d outer cnd step b → ErrHalts c → ErrHalts c)
    (hRet : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hFlCond : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (step : Option Expr)
      (b : Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hFlBody : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' : SpecSt),
      ForCond st d env cnd st' → ExecErr st' d env b → ErrHalts c → ErrHalts c)
    (hFlStep : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr) (e : Expr)
      (b : Stmt) (st' st'' : SpecSt) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → EvalErr st'' d env e → ErrHalts c → ErrHalts c)
    (hFlLoop : ∀ (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' : SpecSt) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
      ForLoopErr st''' d env cnd step b → ErrHalts c → ErrHalts c)
    (hSeqHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt),
      ExecErr st d env s → ErrHalts c → ErrHalts c)
    (hSeqTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : SpecSt),
      ExecS st d env s st' .normal → ExecSeqErr st' d env ss → ErrHalts c → ErrHalts c)
    -- The separate top-level abrupt route (top-level abrupt → exit 70).
    (hTopAbrupt : TopAbrupt p → ErrHalts c)
    (h : BigStepErr p) :
    Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ e ≠ 0 := by
  obtain ⟨out, hh⟩ :=
    errorSimFull c p
      hVarUndef hAssignE hAssignUnbound hBinaryL hBinaryR hBinaryOp hOrL hOrR hAndL
      hAndR hUnaryE hNegType hCallF hCallTooMany hCallArgs hCallC hArgsHead hArgsTail hNotCallable
      hBadClosure hArity hDepth hBody hEscape hAssertFail hAssertArity hExpr hVarInit hBlock hIfCond
      hIfThen hIfElse hWhileCond hWhileBody hWhileLoop hForInit hForLoop hRet hFlCond
      hFlBody hFlStep hFlLoop hSeqHead hSeqTail hTopAbrupt h
  exact stuck_of_halts_70 hh
-/

/-! ## §2. Indexed mutual assembly -/

/-- Kernel-checked mutual assembly over the six indexed motives. -/
theorem errorSim_of_sites
    {g : (R : Register) → Option (RegisterType R)}
    {m0 : Vsa.MemRepr.Mem}
    {hCallTooMany : CallTooManyCaseI g m0}
    (K : ErrorCasesI g m0 hCallTooMany)
    {st : SpecSt} {d : Nat} {env : Addr} {ss : List Stmt}
    (h : ExecSeqErr st d env ss) : ExecSeqErrI g m0 st d env ss :=
  @ExecSeqErr.rec (mEvalErr g m0) (mEvalArgsErr g m0) (mCallErr g m0)
    (mExecErr g m0) (mForLoopErr g m0) (mExecSeqErr g m0)
    K.hVarUndef K.hAssignE K.hAssignUnbound K.hBinaryL K.hBinaryR K.hBinaryOp
    K.hOrL K.hOrR K.hAndL K.hAndR K.hUnaryE K.hNegType K.hCallF
    hCallTooMany K.hCallArgs K.hCallC K.hArgsHead K.hArgsTail
    K.hNotCallable K.hBadClosure K.hArity K.hDepth K.hBody K.hEscape
    K.hAssertFail K.hAssertArity K.hExpr K.hVarInit K.hBlock K.hIfCond
    K.hIfThen K.hIfElse K.hWhileCond K.hWhileBody K.hWhileLoop K.hForInit
    K.hForLoop K.hRet K.hFlCond K.hFlBody K.hFlStep K.hFlLoop K.hSeqHead
    K.hSeqTail st d env ss h

/-- A top-level error entry after the concrete `interp_run` prologue.  This is
the explicit root bridge previously erased by the constant motive. -/
def ErrorProgramEntry
    (g : (R : Register) → Option (RegisterType R))
    (m0 : Vsa.MemRepr.Mem)
    (p : Program) (c : Config) : Prop :=
  ∃ (c1 : Config) (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (φf φc : Addr → Nat) (sp aRet : BitVec 64),
    Vsa.Machine.Steps c c1 ∧
    ExecSeqEntryI .interpRun g N A SL φf φc initSt 0 0 p sp aRet m0 c1

/-- All error-side work for one loaded program/config pair.  The machine
ghosts are selected once at entry and shared by every constructor seam. -/
structure ErrorProgramWork (p : Program) (c : Config) : Type where
  g : (R : Register) → Option (RegisterType R)
  m0 : Vsa.MemRepr.Mem
  hCallTooMany : CallTooManyCaseI g m0
  cases : ErrorCasesI g m0 hCallTooMany
  entry : ErrorProgramEntry g m0 p c
  topAbrupt : TopAbrupt p → ErrHalts c

/-- Program-level indexed error simulation. -/
theorem errorSimFull
    {g : (R : Register) → Option (RegisterType R)}
    {m0 : Vsa.MemRepr.Mem}
    {hCallTooMany : CallTooManyCaseI g m0}
    (p : Program) (K : ErrorCasesI g m0 hCallTooMany) {c : Config}
    (hEntry : ErrorProgramEntry g m0 p c)
    (hTopAbrupt : TopAbrupt p → ErrHalts c)
    (h : BigStepErr p) : ErrHalts c := by
  rcases h with hseq | habrupt
  · obtain ⟨c1, N, A, SL, φf, φc, sp, aRet, hs, hEntryI⟩ := hEntry
    exact errHalts_of_steps hs
      ((errorSim_of_sites K hseq) .interpRun N A SL φf φc sp aRet c1 hEntryI)
  · exact hTopAbrupt habrupt

/-- The indexed error result supplies the nonzero-halt disjunct. -/
theorem stuck_of_bigStepErrFull
    {g : (R : Register) → Option (RegisterType R)}
    {m0 : Vsa.MemRepr.Mem}
    {hCallTooMany : CallTooManyCaseI g m0}
    (p : Program) (K : ErrorCasesI g m0 hCallTooMany) {c : Config}
    (hEntry : ErrorProgramEntry g m0 p c)
    (hTopAbrupt : TopAbrupt p → ErrHalts c) (h : BigStepErr p) :
    Vsa.Machine.Diverges c ∨
      ∃ out e, Vsa.Machine.Halts c out e ∧ e ≠ 0 := by
  obtain ⟨out, hh⟩ := errorSimFull p K hEntry hTopAbrupt h
  exact stuck_of_halts_70 hh

/-- Public one-program wrapper over the indexed internal work bundle. -/
theorem stuck_of_bigStepErrFull_work (p : Program) (c : Config)
    (W : ErrorProgramWork p c) (h : BigStepErr p) :
    Vsa.Machine.Diverges c ∨
      ∃ out e, Vsa.Machine.Halts c out e ∧ e ≠ 0 :=
  stuck_of_bigStepErrFull p W.cases W.entry W.topAbrupt h

end Vsa.Sim
