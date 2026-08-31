import Vsa.Sim.ErrorSim

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
constructor (42 total).  For a *recursive* error constructor (e.g.
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
open Vsa.Machine (Config Halts)
open Vsa.While

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The six error-motives — all constant `ErrHalts c`

Mirroring `term_sim_of_cases`'s `mEvalE …` motives, but every motive ignores its
node and all indices and returns the fixed conclusion `ErrHalts c`.  The mutual
recursor demands one motive per relation, in the order
`EvalErr, EvalArgsErr, CallErr, ExecErr, ForLoopErr, ExecSeqErr`. -/

variable (c : Config)

/-- `EvalErr` motive (constant `ErrHalts c`). -/
def mEvalErr (_st : SpecSt) (_d : Nat) (_env : Addr) (_e : Expr)
    (_h : EvalErr _st _d _env _e) : Prop := ErrHalts c

/-- `EvalArgsErr` motive (constant `ErrHalts c`). -/
def mEvalArgsErr (_st : SpecSt) (_d : Nat) (_env : Addr) (_es : List Expr)
    (_h : EvalArgsErr _st _d _env _es) : Prop := ErrHalts c

/-- `CallErr` motive (constant `ErrHalts c`). -/
def mCallErr (_st : SpecSt) (_d : Nat) (_fv : Value) (_vs : List Value)
    (_h : CallErr _st _d _fv _vs) : Prop := ErrHalts c

/-- `ExecErr` motive (constant `ErrHalts c`). -/
def mExecErr (_st : SpecSt) (_d : Nat) (_env : Addr) (_s : Stmt)
    (_h : ExecErr _st _d _env _s) : Prop := ErrHalts c

/-- `ForLoopErr` motive (constant `ErrHalts c`). -/
def mForLoopErr (_st : SpecSt) (_d : Nat) (_env : Addr) (_cnd _step : Option Expr)
    (_b : Stmt) (_h : ForLoopErr _st _d _env _cnd _step _b) : Prop := ErrHalts c

/-- `ExecSeqErr` motive (constant `ErrHalts c`). -/
def mExecSeqErr (_st : SpecSt) (_d : Nat) (_env : Addr) (_ss : List Stmt)
    (_h : ExecSeqErr _st _d _env _ss) : Prop := ErrHalts c

/-! ## §2. The assembled mutual induction — `errorSim_of_sites`

The full six-motive `@ExecSeqErr.rec` application with the constant `ErrHalts`
motives.  Each of the 42 minor premises is an explicit hypothesis, in the exact
∀-closed shape the recursor demands: the constructor's arguments (including its
sub-derivation proofs), then the sub-derivation IHs in the (constant) motive
shape (`ErrHalts c`), then the (constant) motive conclusion `ErrHalts c`.

Because every motive is constant `ErrHalts c`, every minor premise is precisely
the per-error-site residual "reaching this error node's compiled code reaches a
`jal runtime_error` site ⇒ `Halts c out 70`" (for recursive nodes, with the
sub-node's `ErrHalts c` additionally available as an IH argument).  The
hypothesis names below record the constructor ↔ residual mapping:

* EvalErr (15): hVarUndef, hAssignE, hAssignUnbound, hBinaryL, hBinaryR,
  hBinaryOp, hOrL, hOrR, hAndL, hAndR, hUnaryE, hNegType, hCallF, hCallArgs,
  hCallC.
* EvalArgsErr (2): hArgsHead, hArgsTail.
* CallErr (7): hNotCallable, hArity, hDepth, hBody, hEscape, hAssertFail,
  hAssertArity.
* ExecErr (12): hExpr, hVarInit, hBlock, hIfCond, hIfThen, hIfElse, hWhileCond,
  hWhileBody, hWhileLoop, hForInit, hForLoop, hRet.
* ForLoopErr (4): hFlCond, hFlBody, hFlStep, hFlLoop.
* ExecSeqErr (2): hSeqHead, hSeqTail.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`. -/

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
    (hCallArgs : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → EvalArgsErr st' d env args → ErrHalts c → ErrHalts c)
    (hCallC : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : SpecSt) (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
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
    -- 43rd site: dangling closure address (`CallErr.badClosure`, the leaf added
    -- by the landed amendment; `st.store.closures[a]? = none`).  Same exit-70
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
    hAndR hUnaryE hNegType hCallF hCallArgs hCallC
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
error simulation, conditional only on the 42 per-error-site residuals. -/
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
    (hCallArgs : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → EvalArgsErr st' d env args → ErrHalts c → ErrHalts c)
    (hCallC : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : SpecSt) (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
      CallErr st'' d fv vs → ErrHalts c → ErrHalts c)
    (hArgsHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hArgsTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalArgsErr st' d env es → ErrHalts c → ErrHalts c)
    (hNotCallable : ∀ (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value),
      (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) → ErrHalts c)
    -- 43rd site: dangling closure address (`CallErr.badClosure`); see
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
    -- The 43rd error route: a top-level `ExecSeq` completing with an abrupt
    -- status (`TopAbrupt p`, the new `BigStepErr` disjunct — `interp_run`,
    -- `c/src/interp.c:333-361`, prints `runtime error` and `exit 70`).  Same
    -- exit-70 shape as the other 42 site residuals; no new machine proof here.
    (hTopAbrupt : TopAbrupt p → ErrHalts c)
    (h : BigStepErr p) : ∃ out, Halts c out 70 := by
  rcases h with hseq | habrupt
  · exact errorSim_of_sites c
      hVarUndef hAssignE hAssignUnbound hBinaryL hBinaryR hBinaryOp hOrL hOrR hAndL
      hAndR hUnaryE hNegType hCallF hCallArgs hCallC hArgsHead hArgsTail hNotCallable
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
    (hCallArgs : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → EvalArgsErr st' d env args → ErrHalts c → ErrHalts c)
    (hCallC : ∀ (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : SpecSt) (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
      CallErr st'' d fv vs → ErrHalts c → ErrHalts c)
    (hArgsHead : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hArgsTail : ∀ (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalArgsErr st' d env es → ErrHalts c → ErrHalts c)
    (hNotCallable : ∀ (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value),
      (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) → ErrHalts c)
    -- 43rd site: dangling closure address (`CallErr.badClosure`); see
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
    -- The 43rd error route (top-level abrupt → exit 70); see `errorSimFull`.
    (hTopAbrupt : TopAbrupt p → ErrHalts c)
    (h : BigStepErr p) :
    Vsa.Machine.Diverges c ∨ ∃ out e, Vsa.Machine.Halts c out e ∧ e ≠ 0 := by
  obtain ⟨out, hh⟩ :=
    errorSimFull c p
      hVarUndef hAssignE hAssignUnbound hBinaryL hBinaryR hBinaryOp hOrL hOrR hAndL
      hAndR hUnaryE hNegType hCallF hCallArgs hCallC hArgsHead hArgsTail hNotCallable
      hBadClosure hArity hDepth hBody hEscape hAssertFail hAssertArity hExpr hVarInit hBlock hIfCond
      hIfThen hIfElse hWhileCond hWhileBody hWhileLoop hForInit hForLoop hRet hFlCond
      hFlBody hFlStep hFlLoop hSeqHead hSeqTail hTopAbrupt h
  exact stuck_of_halts_70 hh

end Vsa.Sim
