import Vsa.While.Semantics
import Vsa.Machine

/-!
# Layer 5 spec gadgets for `stuck_sim`: the error judgment and bounded progress

`stuck_sim` (`Vsa/Refinement.lean`) says a program with **no** `BigStep`
derivation never halts cleanly: the machine diverges, or halts with a nonzero
exit code.  The `BigStep` semantics (`Vsa/While/Semantics.lean`) only records
*successful* runs — every runtime error and every divergence is, by design,
*absent* from `BigStep`.  To reason about "no derivation" we need two spec-side
gadgets, defined here:

1. **The error judgment** (`EvalErr`/`EvalArgsErr`/`CallErr`/`ExecErr`/… ) — a
   mutual inductive that *positively* witnesses a runtime error, mirroring the
   failure modes the C interpreter turns into a `runtime_error(…)` call: an
   undefined variable (`env_get` miss), a type error (`binOpSem = none`),
   division by zero, a non-callable callee / arity mismatch, an `assert`
   failure, and the call-depth cap being hit.  Structurally it shadows the 8
   `BigStep` relations: each rule either *is* a leaf error or *propagates* an
   error out of a sub-evaluation, in exactly the left-to-right order the
   evaluator uses.

2. **Bounded progress** (`Approx`) — a fuel-indexed relation "the configuration
   is still running after `n` rule steps".  Its trichotomy lemma (every
   configuration terminates, errors, or `Approx n` for every `n`) is the
   classical case-split behind `stuck_sim`: no `BigStep` ⇒ (error ∨ ∀ n Approx).

The forward-simulation side (error derivation ↦ `exit 70`, `Approx n` ↦ ≥ n
machine steps ↦ `Diverges`) reuses the M4 machinery, `Vsa/Sim/JmpSpec.lean`
(`runtime_error_spec`/`longjmp_spec` land control at interp_run's setjmp
continuation `0x80004428`) and the HTIF exit lemma (`Vsa/Sim/Htif.lean`
`htif_store_exit`).  The first green piece — the Machine-level *exit-code
faithfulness* gadget — is at the bottom of this file: any halt with a nonzero
code already lands in `stuck_sim`'s second disjunct, no machine plumbing needed.
-/

namespace Vsa.While

/-! ## 1. The error judgment

Mirrors the failure modes of `eval_expr`/`exec_stmt`/`call_value` (the C sites
that call `runtime_error(…)`; `experiments/disasm.txt` @ the `jal … <runtime_error>`
call sites).  The relations do not thread an output state: once an error is
reached the interpreter `longjmp`s out, so only the *fact* of the error matters
(the diagnostic text carries line numbers the deep embedding lacks — `stuck_sim`
does not constrain the console text).  The depth `d` and scope `env` are carried
exactly as in `BigStep`.  -/

mutual

/-- An expression evaluation reaches a runtime error (`eval_expr`).  Leaf
errors: undefined variable (`env_get` returns `NULL`), a binary type error or
div/mod-by-zero (`binOpSem = none`), unary `neg` on a non-int, a callee that is
not callable, an argument-count mismatch, the depth cap.  Propagation: an error
in any sub-expression, evaluated left to right. -/
inductive EvalErr : St → Nat → Addr → Expr → Prop where
  -- leaf: undefined variable
  | varUndef (st : St) (d : Nat) (env : Addr) (x : String) :
    st.store.get? env x = none →
    EvalErr st d env (.var x)
  -- propagate through assignment's RHS
  | assignE (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) :
    EvalErr st d env e →
    EvalErr st d env (.assign x e)
  -- leaf: assignment to an unbound variable (`env_set` miss)
  | assignUnbound (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : St) (v : Value) :
    EvalE st d env e st' v →
    st'.store.set? env x v = none →
    EvalErr st d env (.assign x e)
  -- propagate through a binary operand (left, then right)
  | binaryL (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr) :
    EvalErr st d env l →
    EvalErr st d env (.binary op l r)
  | binaryR (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' : St) (lv : Value) :
    EvalE st d env l st' lv →
    EvalErr st' d env r →
    EvalErr st d env (.binary op l r)
  -- leaf: binary type error / division by zero (`binOpSem = none`)
  | binaryOp (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : St) (lv rv : Value) :
    EvalE st d env l st' lv →
    EvalE st' d env r st'' rv →
    binOpSem st''.store op lv rv = none →
    EvalErr st d env (.binary op l r)
  -- propagate through a logical operand (short-circuit order)
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
  -- propagate through / leaf on a unary operand
  | unaryE (st : St) (d : Nat) (env : Addr) (op : UnOp) (e : Expr) :
    EvalErr st d env e →
    EvalErr st d env (.unary op e)
  -- leaf: unary `neg` applied to a non-int value (C's `eval_unary` type check)
  | negType (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) :
    EvalE st d env e st' v →
    (∀ n : Int, v ≠ .int n) →
    EvalErr st d env (.unary .neg e)
  -- propagate through the callee, then the arguments
  | callF (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr) :
    EvalErr st d env f →
    EvalErr st d env (.call f args)
  | callArgs (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : St) (fv : Value) :
    EvalE st d env f st' fv →
    EvalArgsErr st' d env args →
    EvalErr st d env (.call f args)
  -- leaf/propagate: the call itself errors
  | callC (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : St) (fv : Value) (vs : List Value) :
    EvalE st d env f st' fv →
    EvalArgs st' d env args st'' vs →
    CallErr st'' d fv vs →
    EvalErr st d env (.call f args)

/-- An argument list's evaluation reaches an error (left to right). -/
inductive EvalArgsErr : St → Nat → Addr → List Expr → Prop where
  | head (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr) :
    EvalErr st d env e →
    EvalArgsErr st d env (e :: es)
  | tail (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : St) (v : Value) :
    EvalE st d env e st' v →
    EvalArgsErr st' d env es →
    EvalArgsErr st d env (e :: es)

/-- Calling a value reaches a runtime error (`call_value`).  Leaf errors: the
callee is not callable (not a closure or native), arity mismatch, the depth cap
(`d ≥ maxCallDepth`), an `assert` whose argument is falsy or has bad arity.
Propagation: the closure body errors, or finishes with an escaping `brk`/`cont`
status (which `call_value` treats as an error). -/
inductive CallErr : St → Nat → Value → List Value → Prop where
  -- leaf: not callable (any value that is not a closure or a native)
  | notCallable (st : St) (d : Nat) (fv : Value) (vs : List Value) :
    (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) →
    CallErr st d fv vs
  -- leaf: a closure value whose address does not resolve in the store
  -- (`st.store.closures[a]? = none`).  `call_value` (`c/src/interp.c:171`)
  -- dereferences `callee.as.fn`, valid by construction (closures come from
  -- `allocClosure`), so this never arises from `initSt`; it is the
  -- spec-completeness closure for the arbitrary-config quantifiers of
  -- `StmtDispatchD` (see `DanglingClosureErrs`).
  | badClosure (st : St) (d : Nat) (a : Addr) (vs : List Value) :
    st.store.closures[a]? = none →
    CallErr st d (.closure a) vs
  -- leaf: closure arity mismatch
  | arity (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) :
    st.store.closures[a]? = some cd →
    vs.length ≠ cd.params.length →
    CallErr st d (.closure a) vs
  -- leaf: call-depth cap reached (`if (++call_depth > MAX_CALL_DEPTH) error`)
  | depth (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    ¬ d < maxCallDepth →
    CallErr st d (.closure a) vs
  -- propagate: the closure body errors, run at depth `d + 1`
  | body (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeqErr ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st.out⟩ (d + 1) frame cd.body →
    CallErr st d (.closure a) vs
  -- leaf: closure body escapes with `brk`/`cont` (an error in `call_value`)
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
  -- leaf: `assert(false)` / `assert` with wrong arity
  | assertFail (st : St) (d : Nat) (vs : List Value) (v m : Value) :
    (vs = [v] ∨ vs = [v, m]) →
    v.truthy = false →
    CallErr st d (.native .assert) vs
  | assertArity (st : St) (d : Nat) (vs : List Value) :
    (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) →
    CallErr st d (.native .assert) vs

/-- A statement's execution reaches a runtime error (`exec_stmt`).  Propagates
through the sub-relations in evaluation order. -/
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
  -- if: condition errors, or the taken branch errors
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
  -- while: condition errors, or the body errors (on the entering iteration
  -- or on a later iteration reached through a normal/cont status)
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
  -- for: initializer, condition, body, or step errors
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

/-- A `for` loop reaches a runtime error. -/
inductive ForLoopErr : St → Nat → Addr → Option Expr → Option Expr → Stmt →
    Prop where
  -- the condition errors
  | cond (st : St) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr)
      (b : Stmt) :
    EvalErr st d env c →
    ForLoopErr st d env (some c) step b
  -- the body errors (this iteration passed the condition)
  | body (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' : St) :
    ForCond st d env cnd st' →
    ExecErr st' d env b →
    ForLoopErr st d env cnd step b
  -- the step expression errors
  | step (st : St) (d : Nat) (env : Addr) (cnd : Option Expr) (e : Expr)
      (b : Stmt) (st' st'' : St) (status : Status) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    EvalErr st'' d env e →
    ForLoopErr st d env cnd (some e) b
  -- a later iteration errors (reached through a normal/cont body + step)
  | loop (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' : St) (status : Status) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    ExecStep st'' d env step st''' →
    ForLoopErr st''' d env cnd step b →
    ForLoopErr st d env cnd step b

/-- A statement sequence reaches a runtime error: the first statement errors,
or it finishes normally and the tail errors. -/
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

/-- **A top-level statement sequence completes with an abrupt status.**
`interp_run` (`c/src/interp.c:333-361`) runs each top-level statement and, if it
returns `EXEC_RETURN`/`EXEC_BREAK`/`EXEC_CONTINUE` (any non-`.normal` status),
prints a `runtime error` and `return 1` (→ `run_source` returns the exit code
`70`).  Unlike a nested `.block` sequence — which *propagates* an abrupt head
(`ExecSeq.consAbrupt`, mirroring `ST_BLOCK`'s `return st` at `interp.c:286`) —
the TOP-LEVEL driver turns an abrupt completion into an error.  This is a
top-level-only judgment; `ExecSeqErr` (shared by blocks) is deliberately left
unchanged. -/
def TopAbrupt (p : Program) : Prop :=
  ∃ (st' : St) (status : Status), status ≠ .normal ∧ ExecSeq initSt 0 0 p st' status

/-- **A program hits a runtime error** iff its top-level statement sequence, run
in the global scope at depth 0, either reaches a `runtime_error` node
(`ExecSeqErr`) or completes with an abrupt status (`TopAbrupt`, the top-level
`return`/`break`/`continue` that `interp_run` rejects).  Both drive the machine
to `runtime_error`/`longjmp` → `exit 70`. -/
def BigStepErr (p : Program) : Prop :=
  ExecSeqErr initSt 0 0 p ∨ TopAbrupt p

/-! ## 2. Bounded progress (`Approx`)

`Approx n st d env s status?` — the machine, executing statement sequence `s`
in state `st`, is **still running after `n` rule steps** (has neither returned a
value nor errored).  It is a coarse fuel counter: each constructor consumes one
unit of fuel and hands the rest to a sub-computation, so `Approx n` witnesses at
least `n` `exec_stmt`/`eval_expr` dispatch steps, which the divergence
simulation maps to ≥ `n` machine steps (`TripleN`, `Vsa/Triple.lean`).

`Approx 0` always holds (no progress required).  The load-bearing content is the
successor case: to be running for `n+1` steps, the head statement must run and
the tail be running for `n` more — OR the head itself be a loop/call that is
running for `n` more.  We keep the relation minimal (sequence-level): it is
enough for the trichotomy, whose real work is the classical case split, not the
inductive structure of `Approx`. -/

mutual

/-- An expression's evaluation is **still running after `n` rule steps**.  The
1:1 fuel mirror of `EvalErr`'s propagation constructors (error LEAVES have no
divergence analogue — they terminate the computation): a sub-computation still
running after a normal prefix keeps the whole expression running one step
longer.  Expression divergence enters through calls (`CApprox`). -/
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
    ArgsApprox n st' d env args →
    EApprox (n + 1) st d env (.call f args)
  | callC (n : Nat) (st : St) (d : Nat) (env : Addr) (f : Expr)
      (args : List Expr) (st' st'' : St) (fv : Value) (vs : List Value) :
    EvalE st d env f st' fv →
    EvalArgs st' d env args st'' vs →
    CApprox n st'' d fv vs →
    EApprox (n + 1) st d env (.call f args)

/-- An argument list's evaluation is still running (mirror of `EvalArgsErr`). -/
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

/-- A call is still running: the closure body's sequence is still running at
depth `d + 1` (mirror of `CallErr.body`; natives always terminate). -/
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

/-- A single statement is still running after `n` rule steps — the
WITHIN-statement divergence relation (mirror of `ExecErr`'s propagation
constructors).  `whileLoop` is the load-bearing case: each loop iteration whose
cond+body complete normally consumes one unit of fuel, so `while (true) {}`
satisfies `SApprox n` for every `n`. -/
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

/-- A `for` loop is still running (mirror of `ForLoopErr`). -/
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

/-- The sequence-level bounded-progress relation.  The original two constructors
are UNCHANGED; `head` is the amendment (2026-08-31) that lets a head statement
consume fuel INTERNALLY (`SApprox`), so within-statement divergence — a
diverging loop or a non-terminating closure body — is finally in `Approx`'s
range.  (Before the amendment `Approx (n+1)` forced the head to complete
`.normal`, making `BigStepDiverges`, and with it `Trichotomy`, FALSE at
`[while (true) {}]` — the machine-checked finding in `Vsa/While/StmtDispatch`.) -/
inductive Approx : Nat → St → Nat → Addr → List Stmt → Prop where
  /-- Zero fuel: always still running. -/
  | zero (st : St) (d : Nat) (env : Addr) (ss : List Stmt) :
    Approx 0 st d env ss
  /-- The head statement runs to a normal status, and the tail is still running
  for `n` more steps. -/
  | step (n : Nat) (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : St) :
    ExecS st d env s st' .normal →
    Approx n st' d env ss →
    Approx (n + 1) st d env (s :: ss)
  /-- The head statement is itself still running after `n` internal steps. -/
  | head (n : Nat) (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) :
    SApprox n st d env s →
    Approx (n + 1) st d env (s :: ss)

end

/-- **A program runs forever** (spec-side divergence): for every fuel `n`, the
top-level sequence is still running after `n` steps.  The divergence simulation
maps this to `Diverges c`. -/
def BigStepDiverges (p : Program) : Prop :=
  ∀ n, Approx n initSt 0 0 p

/-! ### The trichotomy (statement)

Every top-level program either terminates (`BigStep`), errors (`BigStepErr`), or
diverges (`BigStepDiverges`).  This is the classical case split behind
`stuck_sim`: given `¬ ∃ out, BigStep p out`, trichotomy yields `BigStepErr p ∨
BigStepDiverges p`, whose two forward simulations land in the two `stuck_sim`
disjuncts.  The proof (induction on `n` + `Classical.em` at each dispatch) is
deferred; the statement pins the obligation. -/

/-- The trichotomy obligation, as a `Prop` to be discharged by the bounded-
progress lemma.  Kept as an explicit statement (not yet proved) so downstream
`stuck_sim` assembly can consume it by name. -/
def Trichotomy : Prop :=
  ∀ p : Program, (∃ out, BigStep p out) ∨ BigStepErr p ∨ BigStepDiverges p

/-- From the trichotomy, a program with no clean `BigStep` errors or diverges —
the exact shape `stuck_sim`'s spec side needs.  This part *is* proved: it is the
elimination half of the classical split. -/
theorem stuck_of_trichotomy (htri : Trichotomy) (p : Program)
    (hno : ¬ ∃ out, BigStep p out) : BigStepErr p ∨ BigStepDiverges p := by
  rcases htri p with hbs | herr | hdiv
  · exact (hno hbs).elim
  · exact Or.inl herr
  · exact Or.inr hdiv

/-! ## 3. First green piece — Machine-side exit-code faithfulness

The simplest `stuck_sim` fragment, fully proved and self-contained: *any* halt
with a nonzero exit code already realizes `stuck_sim`'s second disjunct.  The
error simulation's job (deferred) is to reach exactly such a halt — the C
interpreter's `main` returns `70` on a caught `runtime_error`, and crt0's
`j exit` (`experiments/disasm.txt:22`) drives `_exit`'s HTIF store of
`(70<<<1)|1` to `tohost` (`htif_store_exit`, `Vsa/Sim/Htif.lean`), so `e = 70`.
This gadget is the target the error path is aimed at. -/

open Vsa.Machine in
/-- A halt with a nonzero exit code lands in `stuck_sim`'s `∃ out e, Halts c out
e ∧ e ≠ 0` disjunct.  (The forward error simulation supplies such a halt with
`e = 70`.) -/
theorem stuck_of_halts_nonzero {c : Config} {out : String} {e : Nat}
    (h : Halts c out e) (he : e ≠ 0) :
    Diverges c ∨ ∃ out' e', Halts c out' e' ∧ e' ≠ 0 :=
  Or.inr ⟨out, e, h, he⟩

open Vsa.Machine in
/-- Specialization to the interpreter's runtime-error exit code `70` (`EX_SOFTWARE`
in `main`'s `fprintf`/`return 70`): reaching this halt discharges `stuck_sim`. -/
theorem stuck_of_halts_70 {c : Config} {out : String}
    (h : Halts c out 70) :
    Diverges c ∨ ∃ out' e', Halts c out' e' ∧ e' ≠ 0 :=
  stuck_of_halts_nonzero h (by decide)

open Vsa.Machine in
/-- A diverging machine directly realizes `stuck_sim`'s first disjunct — the
target of the `Approx`/`BigStepDiverges` simulation. -/
theorem stuck_of_diverges {c : Config} (h : Diverges c) :
    Diverges c ∨ ∃ out' e', Halts c out' e' ∧ e' ≠ 0 :=
  Or.inl h

end Vsa.While
