import Vsa.While.StmtDispatch

/-!
# `StmtDispatchClose` — closing `htri`'s two final residuals

`Vsa/While/Trichotomy.lean` §5 reduced the whole `Trichotomy` obligation to
exactly two spec-layer residuals (`trichotomy_of_stmtDispatchD`):

* `StmtDispatchD` — the classical per-statement trichotomy: every statement,
  at any config, runs to some status (`ExecS`), errors (`ExecErr`), or diverges
  in place (`∀ n, SApprox n`);
* `hroot` — a top-level completing sequence yields a `BigStep`.

This file closes `StmtDispatchD` and `hroot` via a classical mutual totality
induction over the whole `EvalE`/`EvalArgs`/`Call`/`ExecS`/… family.  It was
originally conditional on **three precisely-named spec-completeness holes** — each
an *arbitrary-config* shape (malformed AST or store) that the then-LANDED error
judgment could not dispatch but that is UNREACHABLE from `initSt`.  All three are
now CLOSED by the (authorized) landed-def amendments cross-checked against the C
source (`c/src/interp.c`):

* Hole 1 — a top-level `break`/`continue`/`return` (`interp_run`,
  `c/src/interp.c:333-361`) is a runtime error (exit 70).  A nested `.block`'s
  abrupt head, by contrast, *propagates* (`ST_BLOCK`, `c/src/interp.c:286`,
  `return st`), so this is a TOP-LEVEL-only judgment: `BigStepErr` gained a
  `TopAbrupt` disjunct (`Vsa/While/ErrorSem.lean`), `ExecSeqErr` unchanged.
  Discharged by `topLevelAbruptErrs`.
* Hole 2 — a `.closure a` with `closures[a]? = none` (never arises: closures come
  from `allocClosure`) is stuck.  Added the `CallErr.badClosure` leaf; discharged
  by `danglingClosureErrs`.
* Hole 3 — a `for (break; …)` init completes abrupt, which the C *swallows*
  (`c/src/interp.c:308`: `exec_stmt(init)`'s status is discarded, the loop
  proceeds).  So `ExecInit.some` was GENERALIZED to accept any completing status
  (a SEMANTICS change, C-faithful) — the abrupt init PROGRESSES rather than
  errors, so no error premise is needed (the former `ForInitAbruptErrs`, which
  demanded an `ExecErr`, was FALSE and is removed).

`trichotomy_unconditional` is therefore a plain `Trichotomy` with no residual
premises.

## The `StmtDispatchD` proof: fuel-bounded classical progress

The content is a single **progress lemma** (`progress`), proved by structural
induction on a fuel counter `n`, mutually across every judgment:

  for each judgment `J` with fuel mirror `JA`,
    `¬ (∃ result, J …) → ¬ (JErr …) → JA n …`

("a computation that neither completes nor errors is still running at every
fuel").  The mutual recursion is on `n` (structural), NOT on the syntax — a
`while` loop recurses on the *same* statement at *smaller* fuel, which is exactly
what the fuel counter licenses.  Every stuck configuration is routed into an
`*Err` constructor (undefined var, `binOpSem = none`, depth cap, arity, …); the
three configurations that are neither progressing nor covered by an error rule
(Holes 1–3 above) are the ones surfaced as premises.

`StmtDispatchD` then follows by `Classical.em` twice: split on `∃ result`, then
on `*Err`; the remaining branch is `progress` at every `n`.

## The `hroot` hole — top-level abrupt status (`c/src/interp.c:333` `interp_run`)

`hroot : (∃ st' status, ExecSeq initSt 0 0 p st' status) → ∃ out, BigStep p out`
is **false as stated**.  `BigStep` requires the top-level status to be `.normal`,
but `ExecSeq.consAbrupt` derives `ExecSeq initSt 0 0 [.brk] initSt .brk` — an
abrupt top-level completion with NO `BigStep`.  The C interpreter (`interp_run`,
`c/src/interp.c:333`) treats exactly this as a runtime error:

    if (st == EXEC_RETURN)  → "runtime error: 'return' outside of a function"
    if (st == EXEC_BREAK||EXEC_CONTINUE) → "runtime error: 'break'/'continue' outside of a loop"
    return 1;   // → run_source returns 70 (main.c), the runtime-error exit code

so a top-level abrupt status belongs in `BigStepErr` (exit 70), the SAME disjunct
as any `runtime_error`.  BUT the landed `ExecSeqErr`/`ExecErr` judgment
(`Vsa/While/ErrorSem.lean`) has **no constructor** for "the head statement of a
sequence ran to an abrupt status" — `ExecSeqErr.tail` requires a `.normal` head,
and `ExecErr` has no `.brk`/`.cont` leaf nor a top-level-`.ret` rule.  So for
`p = [.brk]` all three trichotomy disjuncts fail: not `BigStep` (abrupt), not
`BigStepErr` (no `ExecErr` rule), not `BigStepDiverges`.

This was a genuine spec-completeness hole in the then-LANDED error judgment.  The
authorized amendment took the `BigStepErr` re-route (NOT an `ExecSeqErr` rule,
which would wrongly error a nested `.block`'s propagated abrupt head): `BigStepErr`
now = `ExecSeqErr initSt 0 0 p ∨ TopAbrupt p` (`Vsa/While/ErrorSem.lean`), so a
top-level abrupt completion lands in the error disjunct directly.  The former
premise `TopLevelAbruptErrs` is therefore a theorem (`topLevelAbruptErrs`, via
`Or.inr`) and `trichotomy_unconditional` is unconditional.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.  `#print axioms` ⊆
{`propext`, `Classical.choice`, `Quot.sound`}.
-/

namespace Vsa.While

open Vsa.Sim.Trichotomy

/-! ## The two precisely-named spec-completeness premises

Both name configurations that `StmtDispatchD`/`hroot` cannot dispatch because the
LANDED error judgment (`Vsa/While/ErrorSem.lean`) lacks a constructor for them.
Neither arises in any state reachable from `initSt` (both are excluded by
store/closure well-formedness invariants the semantics maintains but the
per-config quantifiers of `StmtDispatchD` drop), so both are UNREACHABLE for the
top-level `Trichotomy` — but closing them for *arbitrary* configs is a landed-def
change, out of this file's additive scope.  We surface each as a typed premise. -/

/-- **Hole 1 — top-level abrupt status is a runtime error (NOW PROVABLE).**
`interp_run` (`c/src/interp.c:333-361`) turns a top-level `.brk`/`.cont`/`.ret`
into a runtime error (exit 70).  The landed-def amendment routed this through
`BigStepErr`'s new `TopAbrupt` disjunct (`Vsa/While/ErrorSem.lean`), so the
premise is a theorem: an abrupt top-level `ExecSeq` completion is a `BigStepErr`.
(This is a top-level-only judgment; a nested `.block`'s abrupt head still
PROPAGATES via `ExecSeq.consAbrupt`, mirroring `ST_BLOCK`.) -/
theorem topLevelAbruptErrs (p : Program) (st' : St) (status : Status)
    (hne : status ≠ .normal) (h : ExecSeq initSt 0 0 p st' status) : BigStepErr p :=
  Or.inr ⟨st', status, hne, h⟩

/-- **Hole 2 — a closure value whose address does not resolve is an error (NOW
PROVABLE).**  `call_value` (`c/src/interp.c:171`) dereferences the closure
pointer, valid by construction; a `.closure a` with `st.store.closures[a]? =
none` never arises from `initSt`.  The landed-def amendment added the
`CallErr.badClosure` leaf (`Vsa/While/ErrorSem.lean`), so the premise is a
theorem. -/
theorem danglingClosureErrs (st : St) (d : Nat) (a : Addr) (vs : List Value)
    (hcl : st.store.closures[a]? = none) : CallErr st d (.closure a) vs :=
  .badClosure st d a vs hcl

/-! ## The combined fuel-bounded progress bundle

`Progress n` bundles the progress obligation for all six divergence-carrying
judgments at fuel `n`.  Each conjunct says: a config that neither completes nor
errors is still running (`*Approx n`).  Proved `∀ n` by structural induction on
`n`; the successor case is a syntax case-split at each judgment that consumes the
fuel-`n` bundle (the IH) on sub-computations. -/

/-- Progress for expression evaluation at fuel `n`. -/
def ProgressE (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (e : Expr),
    ¬ (∃ st' v, EvalE st d env e st' v) → ¬ EvalErr st d env e →
    EApprox n st d env e

/-- Progress for argument-list evaluation at fuel `n`. -/
def ProgressArgs (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (es : List Expr),
    ¬ (∃ st' vs, EvalArgs st d env es st' vs) → ¬ EvalArgsErr st d env es →
    ArgsApprox n st d env es

/-- Progress for a call at fuel `n`. -/
def ProgressC (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (fv : Value) (vs : List Value),
    ¬ (∃ st' v, Call st d fv vs st' v) → ¬ CallErr st d fv vs →
    CApprox n st d fv vs

/-- Progress for a single statement at fuel `n`. -/
def ProgressS (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (s : Stmt),
    ¬ (∃ st' status, ExecS st d env s st' status) → ¬ ExecErr st d env s →
    SApprox n st d env s

/-- Progress for a for-loop at fuel `n`. -/
def ProgressFl (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (cnd : Option Expr) (step : Option Expr)
    (b : Stmt),
    ¬ (∃ st' status, ForLoop st d env cnd step b st' status) →
    ¬ ForLoopErr st d env cnd step b →
    FlApprox n st d env cnd step b

/-- Progress for a statement sequence at fuel `n`. -/
def ProgressSeq (n : Nat) : Prop :=
  ∀ (st : St) (d : Nat) (env : Addr) (ss : List Stmt),
    ¬ (∃ st' status, ExecSeq st d env ss st' status) → ¬ ExecSeqErr st d env ss →
    Approx n st d env ss

/-- The full bundle. -/
def Progress (n : Nat) : Prop :=
  ProgressE n ∧ ProgressArgs n ∧ ProgressC n ∧ ProgressS n ∧ ProgressFl n ∧
    ProgressSeq n

/-! ### The progress induction

`progress : ∀ n, Progress n`, by structural induction on `n`.  In the successor
case each judgment is handled by a syntax case-split; sub-computations are routed
through the fuel-`n` IH via a local **trichotomy** (complete / error / still
running) obtained from the IH by `Classical.em`. -/

/-- Local trichotomy for expression evaluation from `ProgressE n`. -/
theorem evalTri (hE : ProgressE n) (st : St) (d : Nat) (env : Addr) (e : Expr) :
    (∃ st' v, EvalE st d env e st' v) ∨ EvalErr st d env e ∨
      EApprox n st d env e := by
  by_cases hc : ∃ st' v, EvalE st d env e st' v
  · exact Or.inl hc
  by_cases he : EvalErr st d env e
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hE st d env e hc he))

/-- Local trichotomy for argument-list evaluation from `ProgressArgs n`. -/
theorem argsTri (hA : ProgressArgs n) (st : St) (d : Nat) (env : Addr)
    (es : List Expr) :
    (∃ st' vs, EvalArgs st d env es st' vs) ∨ EvalArgsErr st d env es ∨
      ArgsApprox n st d env es := by
  by_cases hc : ∃ st' vs, EvalArgs st d env es st' vs
  · exact Or.inl hc
  by_cases he : EvalArgsErr st d env es
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hA st d env es hc he))

/-- Local trichotomy for calls from `ProgressC n`. -/
theorem callTri (hC : ProgressC n) (st : St) (d : Nat) (fv : Value)
    (vs : List Value) :
    (∃ st' v, Call st d fv vs st' v) ∨ CallErr st d fv vs ∨
      CApprox n st d fv vs := by
  by_cases hc : ∃ st' v, Call st d fv vs st' v
  · exact Or.inl hc
  by_cases he : CallErr st d fv vs
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hC st d fv vs hc he))

/-- Local trichotomy for statements from `ProgressS n`. -/
theorem stmtTri (hS : ProgressS n) (st : St) (d : Nat) (env : Addr) (s : Stmt) :
    (∃ st' status, ExecS st d env s st' status) ∨ ExecErr st d env s ∨
      SApprox n st d env s := by
  by_cases hc : ∃ st' status, ExecS st d env s st' status
  · exact Or.inl hc
  by_cases he : ExecErr st d env s
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hS st d env s hc he))

/-- Local trichotomy for for-loops from `ProgressFl n`. -/
theorem flTri (hFl : ProgressFl n) (st : St) (d : Nat) (env : Addr)
    (cnd : Option Expr) (step : Option Expr) (b : Stmt) :
    (∃ st' status, ForLoop st d env cnd step b st' status) ∨
      ForLoopErr st d env cnd step b ∨ FlApprox n st d env cnd step b := by
  by_cases hc : ∃ st' status, ForLoop st d env cnd step b st' status
  · exact Or.inl hc
  by_cases he : ForLoopErr st d env cnd step b
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hFl st d env cnd step b hc he))

/-- Expression progress at `n+1` from the fuel-`n` sub-bundles. -/
theorem progressE_succ (hE : ProgressE n) (hA : ProgressArgs n) (hC : ProgressC n)
    (st : St) (d : Nat) (env : Addr) (e : Expr)
    (hnc : ¬ (∃ st' v, EvalE st d env e st' v)) (hne : ¬ EvalErr st d env e) :
    EApprox (n + 1) st d env e := by
  cases e with
  | int m => exact absurd ⟨st, .int m, .int st d env m⟩ hnc
  | str s => exact absurd ⟨st, .str s, .str st d env s⟩ hnc
  | bool b => exact absurd ⟨st, .bool b, .bool st d env b⟩ hnc
  | null => exact absurd ⟨st, .null, .null st d env⟩ hnc
  | var x =>
    cases hget : st.store.get? env x with
    | none => exact absurd (.varUndef st d env x hget) hne
    | some v => exact absurd ⟨st, v, .var st d env x v hget⟩ hnc
  | assign x e =>
    rcases evalTri hE st d env e with ⟨st', v, hrun⟩ | herr | hdiv
    · cases hset : st'.store.set? env x v with
      | none => exact absurd (.assignUnbound st d env x e st' v hrun hset) hne
      | some store'' =>
        exact absurd ⟨⟨store'', st'.out⟩, v, .assign st d env x e st' v store'' hrun hset⟩ hnc
    · exact absurd (.assignE st d env x e herr) hne
    · exact .assignE n st d env x e hdiv
  | binary op l r =>
    rcases evalTri hE st d env l with ⟨st', lv, hl⟩ | herr | hdiv
    · rcases evalTri hE st' d env r with ⟨st'', rv, hr⟩ | herr | hdiv
      · cases hbo : binOpSem st''.store op lv rv with
        | none => exact absurd (.binaryOp st d env op l r st' st'' lv rv hl hr hbo) hne
        | some v => exact absurd ⟨st'', v, .binary st d env op l r st' st'' lv rv v hl hr hbo⟩ hnc
      · exact absurd (.binaryR st d env op l r st' lv hl herr) hne
      · exact .binaryR n st d env op l r st' lv hl hdiv
    · exact absurd (.binaryL st d env op l r herr) hne
    · exact .binaryL n st d env op l r hdiv
  | logical op l r =>
    cases op with
    | or =>
      rcases evalTri hE st d env l with ⟨st', lv, hl⟩ | herr | hdiv
      · by_cases htr : lv.truthy = true
        · exact absurd ⟨st', .bool true, .orTrue st d env l r st' lv hl htr⟩ hnc
        · have hf : lv.truthy = false := by
            cases h : lv.truthy with
            | true => exact absurd h htr
            | false => rfl
          rcases evalTri hE st' d env r with ⟨st'', rv, hr⟩ | herr | hdiv
          · exact absurd ⟨st'', .bool rv.truthy,
              .orFalse st d env l r st' st'' lv rv hl hf hr⟩ hnc
          · exact absurd (.orR st d env l r st' lv hl hf herr) hne
          · exact .orR n st d env l r st' lv hl hf hdiv
      · exact absurd (.orL st d env l r herr) hne
      · exact .orL n st d env l r hdiv
    | and =>
      rcases evalTri hE st d env l with ⟨st', lv, hl⟩ | herr | hdiv
      · by_cases htr : lv.truthy = true
        · rcases evalTri hE st' d env r with ⟨st'', rv, hr⟩ | herr | hdiv
          · exact absurd ⟨st'', .bool rv.truthy,
              .andTrue st d env l r st' st'' lv rv hl htr hr⟩ hnc
          · exact absurd (.andR st d env l r st' lv hl htr herr) hne
          · exact .andR n st d env l r st' lv hl htr hdiv
        · have hf : lv.truthy = false := by
            cases h : lv.truthy with
            | true => exact absurd h htr
            | false => rfl
          exact absurd ⟨st', .bool false, .andFalse st d env l r st' lv hl hf⟩ hnc
      · exact absurd (.andL st d env l r herr) hne
      · exact .andL n st d env l r hdiv
  | unary op e =>
    rcases evalTri hE st d env e with ⟨st', v, hrun⟩ | herr | hdiv
    · cases op with
      | not => exact absurd ⟨st', .bool (!v.truthy), .not st d env e st' v hrun⟩ hnc
      | neg =>
        cases v with
        | int m => exact absurd ⟨st', .int (wrap64 (-m)), .neg st d env e st' m hrun⟩ hnc
        | null => exact absurd (.negType st d env e st' .null hrun (by intro n h; cases h)) hne
        | bool b => exact absurd (.negType st d env e st' (.bool b) hrun (by intro n h; cases h)) hne
        | str s => exact absurd (.negType st d env e st' (.str s) hrun (by intro n h; cases h)) hne
        | closure a => exact absurd (.negType st d env e st' (.closure a) hrun (by intro n h; cases h)) hne
        | native f => exact absurd (.negType st d env e st' (.native f) hrun (by intro n h; cases h)) hne
    · exact absurd (.unaryE st d env op e herr) hne
    · exact .unaryE n st d env op e hdiv
  | call f args =>
    rcases evalTri hE st d env f with ⟨st', fv, hf⟩ | herr | hdiv
    · rcases argsTri hA st' d env args with ⟨st'', vs, hargs⟩ | herr | hdiv
      · rcases callTri hC st'' d fv vs with ⟨st''', v, hcall⟩ | herr | hdiv
        · exact absurd ⟨st''', v, .call st d env f args st' st'' st''' fv vs v hf hargs hcall⟩ hnc
        · exact absurd (.callC st d env f args st' st'' fv vs hf hargs herr) hne
        · exact .callC n st d env f args st' st'' fv vs hf hargs hdiv
      · exact absurd (.callArgs st d env f args st' fv hf herr) hne
      · exact .callArgs n st d env f args st' fv hf hdiv
    · exact absurd (.callF st d env f args herr) hne
    · exact .callF n st d env f args hdiv
  | fn name params body =>
    exact absurd
      ⟨⟨(st.store.allocClosure ⟨env, name, params, body⟩).1, st.out⟩,
        .closure (st.store.allocClosure ⟨env, name, params, body⟩).2,
        .fn st d env name params body _ _ rfl⟩ hnc

/-- Local trichotomy for sequences from `ProgressSeq n`. -/
theorem seqTri (hSeq : ProgressSeq n) (st : St) (d : Nat) (env : Addr)
    (ss : List Stmt) :
    (∃ st' status, ExecSeq st d env ss st' status) ∨ ExecSeqErr st d env ss ∨
      Approx n st d env ss := by
  by_cases hc : ∃ st' status, ExecSeq st d env ss st' status
  · exact Or.inl hc
  by_cases he : ExecSeqErr st d env ss
  · exact Or.inr (Or.inl he)
  · exact Or.inr (Or.inr (hSeq st d env ss hc he))

/-- Argument-list progress at `n+1`. -/
theorem progressArgs_succ (hE : ProgressE n) (hA : ProgressArgs n)
    (st : St) (d : Nat) (env : Addr) (es : List Expr)
    (hnc : ¬ (∃ st' vs, EvalArgs st d env es st' vs))
    (hne : ¬ EvalArgsErr st d env es) :
    ArgsApprox (n + 1) st d env es := by
  cases es with
  | nil => exact absurd ⟨st, [], .nil st d env⟩ hnc
  | cons e es' =>
    rcases evalTri hE st d env e with ⟨st', v, hrun⟩ | herr | hdiv
    · rcases argsTri hA st' d env es' with ⟨st'', vs, hargs⟩ | herr | hdiv
      · exact absurd ⟨st'', v :: vs, .cons st d env e es' st' st'' v vs hrun hargs⟩ hnc
      · exact absurd (.tail st d env e es' st' v hrun herr) hne
      · exact .tail n st d env e es' st' v hrun hdiv
    · exact absurd (.head st d env e es' herr) hne
    · exact .head n st d env e es' hdiv

/-- Call progress at `n+1`.  Hole 2 (dangling closure) is now discharged
directly via `CallErr.badClosure`. -/
theorem progressC_succ (hSeq : ProgressSeq n)
    (st : St) (d : Nat) (fv : Value) (vs : List Value)
    (hnc : ¬ (∃ st' v, Call st d fv vs st' v)) (hne : ¬ CallErr st d fv vs) :
    CApprox (n + 1) st d fv vs := by
  cases fv with
  | null => exact absurd (.notCallable st d .null vs (by intro a h; cases h) (by intro f h; cases h)) hne
  | bool b => exact absurd (.notCallable st d (.bool b) vs (by intro a h; cases h) (by intro f h; cases h)) hne
  | int m => exact absurd (.notCallable st d (.int m) vs (by intro a h; cases h) (by intro f h; cases h)) hne
  | str s => exact absurd (.notCallable st d (.str s) vs (by intro a h; cases h) (by intro f h; cases h)) hne
  | native f =>
    cases f with
    | print => exact absurd ⟨_, _, .print st d vs⟩ hnc
    | println => exact absurd ⟨_, _, .println st d vs⟩ hnc
    | assert =>
      -- assert either succeeds (arg present + truthy), fails (falsy), or has bad arity
      by_cases harity1 : ∃ v, vs = [v]
      · obtain ⟨v, hv⟩ := harity1; subst hv
        by_cases htr : v.truthy = true
        · exact absurd ⟨st, .null, .assertOk st d [v] v v (Or.inl rfl) htr⟩ hnc
        · have hf : v.truthy = false := by
            cases h : v.truthy with
            | true => exact absurd h htr
            | false => rfl
          exact absurd (.assertFail st d [v] v v (Or.inl rfl) hf) hne
      · by_cases harity2 : ∃ v m, vs = [v, m]
        · obtain ⟨v, m, hv⟩ := harity2; subst hv
          by_cases htr : v.truthy = true
          · exact absurd ⟨st, .null, .assertOk st d [v, m] v m (Or.inr rfl) htr⟩ hnc
          · have hf : v.truthy = false := by
              cases h : v.truthy with
              | true => exact absurd h htr
              | false => rfl
            exact absurd (.assertFail st d [v, m] v m (Or.inr rfl) hf) hne
        · exact absurd (.assertArity st d vs
            (by intro v h; exact harity1 ⟨v, h⟩)
            (by intro v m h; exact harity2 ⟨v, m, h⟩)) hne
  | closure a =>
    cases hcl : st.store.closures[a]? with
    | none => exact absurd (.badClosure st d a vs hcl) hne
    | some cd =>
      by_cases harity : vs.length = cd.params.length
      · by_cases hdepth : d < maxCallDepth
        · -- valid closure call: body sequence either completes (→ Call), errors
          -- (→ CallErr.body), escapes (→ CallErr.escape), or is running (→ CApprox.body)
          cases halloc : st.store.allocFrame (some cd.env) with
          | mk store' frame =>
          rcases seqTri hSeq
              ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
                st.out⟩ (d + 1) frame cd.body with
            ⟨st'', status, hseq⟩ | herr | hdiv
          · -- completes: is it normal/ret (→ Call) or brk/cont (→ escape err)?
            cases status with
            | normal =>
              exact absurd ⟨st'', .null,
                .closure st d a cd vs store' frame st'' .normal .null hcl harity hdepth
                  halloc hseq (Or.inl ⟨rfl, rfl⟩)⟩ hnc
            | ret rv =>
              exact absurd ⟨st'', rv,
                .closure st d a cd vs store' frame st'' (.ret rv) rv hcl harity hdepth
                  halloc hseq (Or.inr rfl)⟩ hnc
            | brk =>
              exact absurd (.escape st d a cd vs store' frame st'' .brk hcl harity
                hdepth halloc hseq (Or.inl rfl)) hne
            | cont =>
              exact absurd (.escape st d a cd vs store' frame st'' .cont hcl harity
                hdepth halloc hseq (Or.inr rfl)) hne
          · exact absurd (.body st d a cd vs store' frame hcl harity hdepth halloc herr) hne
          · exact .body n st d a cd vs store' frame hcl harity hdepth halloc hdiv
        · exact absurd (.depth st d a cd vs hcl harity hdepth) hne
      · exact absurd (.arity st d a cd vs hcl harity) hne

/-- Sequence progress at `n+1`. -/
theorem progressSeq_succ (hS : ProgressS n) (hSeq : ProgressSeq n)
    (st : St) (d : Nat) (env : Addr) (ss : List Stmt)
    (hnc : ¬ (∃ st' status, ExecSeq st d env ss st' status))
    (hne : ¬ ExecSeqErr st d env ss) :
    Approx (n + 1) st d env ss := by
  cases ss with
  | nil => exact absurd ⟨st, .normal, .nil st d env⟩ hnc
  | cons s ss' =>
    rcases stmtTri hS st d env s with ⟨st', status, hrun⟩ | herr | hdiv
    · cases status with
      | normal =>
        -- head runs normal; tail either completes (→ ExecSeq), errors (→ tail err),
        -- or is running (→ Approx.step)
        rcases (by
          by_cases hc : ∃ st'' status, ExecSeq st' d env ss' st'' status
          · exact Or.inl hc
          by_cases herr : ExecSeqErr st' d env ss'
          · exact Or.inr (Or.inl herr)
          · exact Or.inr (Or.inr (hSeq st' d env ss' hc herr))
          : (∃ st'' status, ExecSeq st' d env ss' st'' status) ∨
              ExecSeqErr st' d env ss' ∨ Approx n st' d env ss') with
          ⟨st'', status, hseq⟩ | herr | hdiv
        · exact absurd ⟨st'', status, .consNormal st d env s ss' st' st'' status hrun hseq⟩ hnc
        · exact absurd (.tail st d env s ss' st' hrun herr) hne
        · exact .step n st d env s ss' st' hrun hdiv
      | brk =>
        exact absurd ⟨st', .brk, .consAbrupt st d env s ss' st' .brk hrun (by intro h; cases h)⟩ hnc
      | cont =>
        exact absurd ⟨st', .cont, .consAbrupt st d env s ss' st' .cont hrun (by intro h; cases h)⟩ hnc
      | ret rv =>
        exact absurd ⟨st', .ret rv, .consAbrupt st d env s ss' st' (.ret rv) hrun (by intro h; cases h)⟩ hnc
    · exact absurd (.head st d env s ss' herr) hne
    · exact .head n st d env s ss' hdiv

/-- Statement progress at `n+1`.  Hole 3 (abrupt `for`-init) is now discharged
directly: the C swallows the init's status (`ExecInit.some` accepts any status),
so an abrupt init makes the `for` PROGRESS rather than error. -/
theorem progressS_succ (hE : ProgressE n)
    (hS : ProgressS n) (hFl : ProgressFl n) (hSeq : ProgressSeq n)
    (st : St) (d : Nat) (env : Addr) (s : Stmt)
    (hnc : ¬ (∃ st' status, ExecS st d env s st' status)) (hne : ¬ ExecErr st d env s) :
    SApprox (n + 1) st d env s := by
  cases s with
  | expr e =>
    rcases evalTri hE st d env e with ⟨st', v, hrun⟩ | herr | hdiv
    · exact absurd ⟨st', .normal, .expr st d env e st' v hrun⟩ hnc
    · exact absurd (.expr st d env e herr) hne
    · exact .expr n st d env e hdiv
  | varDecl x init =>
    cases init with
    | none => exact absurd ⟨⟨st.store.define env x .null, st.out⟩, .normal, .varNull st d env x⟩ hnc
    | some e =>
      rcases evalTri hE st d env e with ⟨st', v, hrun⟩ | herr | hdiv
      · exact absurd ⟨⟨st'.store.define env x v, st'.out⟩, .normal,
          .varInit st d env x e st' v hrun⟩ hnc
      · exact absurd (.varInit st d env x e herr) hne
      · exact .varInit n st d env x e hdiv
  | block ss =>
    cases halloc : st.store.allocFrame (some env) with
    | mk store' inner =>
      rcases seqTri hSeq ⟨store', st.out⟩ d inner ss with
        ⟨st', status, hseq⟩ | herr | hdiv
      · exact absurd ⟨st', status, .block st d env ss store' inner st' status halloc hseq⟩ hnc
      · exact absurd (.block st d env ss store' inner halloc herr) hne
      · exact .block n st d env ss store' inner halloc hdiv
  | ifStmt c t e =>
    rcases evalTri hE st d env c with ⟨st', v, hc⟩ | herr | hdiv
    · by_cases htr : v.truthy = true
      · rcases stmtTri hS st' d env t with ⟨st'', status, ht⟩ | herr | hdiv
        · exact absurd ⟨st'', status, .ifTrue st d env c t e st' st'' v status hc htr ht⟩ hnc
        · exact absurd (.ifThen st d env c t e st' v hc htr herr) hne
        · exact .ifThen n st d env c t e st' v hc htr hdiv
      · have hf : v.truthy = false := by
          cases h : v.truthy with | true => exact absurd h htr | false => rfl
        cases e with
        | none => exact absurd ⟨st', .normal, .ifNone st d env c t st' v hc hf⟩ hnc
        | some e' =>
          rcases stmtTri hS st' d env e' with ⟨st'', status, he'⟩ | herr | hdiv
          · exact absurd ⟨st'', status, .ifFalse st d env c t e' st' st'' v status hc hf he'⟩ hnc
          · exact absurd (.ifElse st d env c t e' st' v hc hf herr) hne
          · exact .ifElse n st d env c t e' st' v hc hf hdiv
    · exact absurd (.ifCond st d env c t e herr) hne
    · exact .ifCond n st d env c t e hdiv
  | whileStmt c b =>
    rcases evalTri hE st d env c with ⟨st', v, hc⟩ | herr | hdiv
    · by_cases htr : v.truthy = true
      · rcases stmtTri hS st' d env b with ⟨st'', status, hb⟩ | herr | hdiv
        · cases status with
          | brk => exact absurd ⟨st'', .normal, .whileBreak st d env c b st' st'' v hc htr hb⟩ hnc
          | ret rv => exact absurd ⟨st'', .ret rv, .whileRet st d env c b st' st'' v rv hc htr hb⟩ hnc
          | normal =>
            rcases stmtTri hS st'' d env (.whileStmt c b) with
              ⟨st''', status', hloop⟩ | herr | hdiv
            · exact absurd ⟨st''', status', .whileLoop st d env c b st' st'' st''' v .normal status' hc htr hb (Or.inl rfl) hloop⟩ hnc
            · exact absurd (.whileLoop st d env c b st' st'' v .normal hc htr hb (Or.inl rfl) herr) hne
            · exact .whileLoop n st d env c b st' st'' v .normal hc htr hb (Or.inl rfl) hdiv
          | cont =>
            rcases stmtTri hS st'' d env (.whileStmt c b) with
              ⟨st''', status', hloop⟩ | herr | hdiv
            · exact absurd ⟨st''', status', .whileLoop st d env c b st' st'' st''' v .cont status' hc htr hb (Or.inr rfl) hloop⟩ hnc
            · exact absurd (.whileLoop st d env c b st' st'' v .cont hc htr hb (Or.inr rfl) herr) hne
            · exact .whileLoop n st d env c b st' st'' v .cont hc htr hb (Or.inr rfl) hdiv
        · exact absurd (.whileBody st d env c b st' v hc htr herr) hne
        · exact .whileBody n st d env c b st' v hc htr hdiv
      · have hf : v.truthy = false := by
          cases h : v.truthy with | true => exact absurd h htr | false => rfl
        exact absurd ⟨st', .normal, .whileFalse st d env c b st' v hc hf⟩ hnc
    · exact absurd (.whileCond st d env c b herr) hne
    · exact .whileCond n st d env c b hdiv
  | forStmt init cnd step b =>
    cases halloc : st.store.allocFrame (some env) with
    | mk store' outer =>
      cases init with
      | none =>
        -- ExecInit.none, then the loop
        rcases flTri hFl ⟨store', st.out⟩ d outer cnd step b with
          ⟨st', status, hfl⟩ | herr | hdiv
        · exact absurd ⟨st', status,
            .forStart st d env none cnd step b store' outer ⟨store', st.out⟩ st' status
              halloc (.none ⟨store', st.out⟩ d outer) hfl⟩ hnc
        · exact absurd (.forLoop st d env none cnd step b store' outer ⟨store', st.out⟩
            halloc (.none ⟨store', st.out⟩ d outer) herr) hne
        · exact .forLoop n st d env none cnd step b store' outer ⟨store', st.out⟩
            halloc (.none ⟨store', st.out⟩ d outer) hdiv
      | some si =>
        -- The C swallows the init's status (`c/src/interp.c:308`): `ExecInit.some`
        -- accepts ANY completing status, so an abrupt init proceeds into the loop
        -- exactly like a `.normal` one.  No status case-split, no error route.
        rcases stmtTri hS ⟨store', st.out⟩ d outer si with ⟨st', status, hsi⟩ | herr | hdiv
        · rcases flTri hFl st' d outer cnd step b with ⟨st'', status', hfl⟩ | herr | hdiv
          · exact absurd ⟨st'', status',
              .forStart st d env (some si) cnd step b store' outer st' st'' status'
                halloc (.some ⟨store', st.out⟩ d outer si st' status hsi) hfl⟩ hnc
          · exact absurd (.forLoop st d env (some si) cnd step b store' outer st'
              halloc (.some ⟨store', st.out⟩ d outer si st' status hsi) herr) hne
          · exact .forLoop n st d env (some si) cnd step b store' outer st'
              halloc (.some ⟨store', st.out⟩ d outer si st' status hsi) hdiv
        · exact absurd (.forInit st d env si cnd step b store' outer halloc herr) hne
        · exact .forInit n st d env si cnd step b store' outer halloc hdiv
  | ret e =>
    cases e with
    | none => exact absurd ⟨st, .ret .null, .retNull st d env⟩ hnc
    | some e' =>
      rcases evalTri hE st d env e' with ⟨st', v, hrun⟩ | herr | hdiv
      · exact absurd ⟨st', .ret v, .ret st d env e' st' v hrun⟩ hnc
      · exact absurd (.ret st d env e' herr) hne
      · exact .ret n st d env e' hdiv
  | brk => exact absurd ⟨st, .brk, .brk st d env⟩ hnc
  | cont => exact absurd ⟨st, .cont, .cont st d env⟩ hnc

/-- For-loop progress at `n+1`. -/
theorem progressFl_succ (hE : ProgressE n) (hS : ProgressS n) (hFl : ProgressFl n)
    (st : St) (d : Nat) (env : Addr) (cnd : Option Expr) (step : Option Expr)
    (b : Stmt)
    (hnc : ¬ (∃ st' status, ForLoop st d env cnd step b st' status))
    (hne : ¬ ForLoopErr st d env cnd step b) :
    FlApprox (n + 1) st d env cnd step b := by
  -- First establish the condition: either it diverges/errors (done), or it passes
  -- (`ForCond st d env cnd st'` for some post-cond state `st'`).
  have hcond : (FlApprox (n + 1) st d env cnd step b) ∨
      (∃ st', ForCond st d env cnd st') := by
    cases cnd with
    | none => exact Or.inr ⟨st, .none st d env⟩
    | some c =>
      rcases evalTri hE st d env c with ⟨st', v, hc⟩ | herr | hdiv
      · by_cases htr : v.truthy = true
        · exact Or.inr ⟨st', .some st d env c st' v hc htr⟩
        · have hf : v.truthy = false := by
            cases h : v.truthy with | true => exact absurd h htr | false => rfl
          exact absurd ⟨st', .normal, .condFalse st d env c step b st' v hc hf⟩ hnc
      · exact absurd (.cond st d env c step b herr) hne
      · exact Or.inl (.cond n st d env c step b hdiv)
  rcases hcond with hdone | ⟨st', hfc⟩
  · exact hdone
  -- Body at the post-cond state.
  rcases stmtTri hS st' d env b with ⟨st'', status, hb⟩ | herr | hdiv
  · cases status with
    | brk => exact absurd ⟨st'', .normal, .bodyBreak st d env cnd step b st' st'' hfc hb⟩ hnc
    | ret rv => exact absurd ⟨st'', .ret rv, .bodyRet st d env cnd step b st' st'' rv hfc hb⟩ hnc
    | normal =>
      -- step, then recurse
      cases step with
      | none =>
        rcases flTri hFl st'' d env cnd none b with ⟨st''', status', hloop⟩ | herr | hdiv
        · exact absurd ⟨st''', status', .loop st d env cnd none b st' st'' st'' st''' .normal status' hfc hb (Or.inl rfl) (.none st'' d env) hloop⟩ hnc
        · exact absurd (.loop st d env cnd none b st' st'' st'' .normal hfc hb (Or.inl rfl) (.none st'' d env) herr) hne
        · exact .loop n st d env cnd none b st' st'' st'' .normal hfc hb (Or.inl rfl) (.none st'' d env) hdiv
      | some e =>
        rcases evalTri hE st'' d env e with ⟨st''', ev, hstep⟩ | herr | hdiv
        · rcases flTri hFl st''' d env cnd (some e) b with ⟨st4, status', hloop⟩ | herr | hdiv
          · exact absurd ⟨st4, status', .loop st d env cnd (some e) b st' st'' st''' st4 .normal status' hfc hb (Or.inl rfl) (.some st'' d env e st''' ev hstep) hloop⟩ hnc
          · exact absurd (.loop st d env cnd (some e) b st' st'' st''' .normal hfc hb (Or.inl rfl) (.some st'' d env e st''' ev hstep) herr) hne
          · exact .loop n st d env cnd (some e) b st' st'' st''' .normal hfc hb (Or.inl rfl) (.some st'' d env e st''' ev hstep) hdiv
        · exact absurd (.step st d env cnd e b st' st'' .normal hfc hb (Or.inl rfl) herr) hne
        · exact .step n st d env cnd e b st' st'' .normal hfc hb (Or.inl rfl) hdiv
    | cont =>
      cases step with
      | none =>
        rcases flTri hFl st'' d env cnd none b with ⟨st''', status', hloop⟩ | herr | hdiv
        · exact absurd ⟨st''', status', .loop st d env cnd none b st' st'' st'' st''' .cont status' hfc hb (Or.inr rfl) (.none st'' d env) hloop⟩ hnc
        · exact absurd (.loop st d env cnd none b st' st'' st'' .cont hfc hb (Or.inr rfl) (.none st'' d env) herr) hne
        · exact .loop n st d env cnd none b st' st'' st'' .cont hfc hb (Or.inr rfl) (.none st'' d env) hdiv
      | some e =>
        rcases evalTri hE st'' d env e with ⟨st''', ev, hstep⟩ | herr | hdiv
        · rcases flTri hFl st''' d env cnd (some e) b with ⟨st4, status', hloop⟩ | herr | hdiv
          · exact absurd ⟨st4, status', .loop st d env cnd (some e) b st' st'' st''' st4 .cont status' hfc hb (Or.inr rfl) (.some st'' d env e st''' ev hstep) hloop⟩ hnc
          · exact absurd (.loop st d env cnd (some e) b st' st'' st''' .cont hfc hb (Or.inr rfl) (.some st'' d env e st''' ev hstep) herr) hne
          · exact .loop n st d env cnd (some e) b st' st'' st''' .cont hfc hb (Or.inr rfl) (.some st'' d env e st''' ev hstep) hdiv
        · exact absurd (.step st d env cnd e b st' st'' .cont hfc hb (Or.inr rfl) herr) hne
        · exact .step n st d env cnd e b st' st'' .cont hfc hb (Or.inr rfl) hdiv
  · exact absurd (.body st d env cnd step b st' hfc herr) hne
  · exact .body n st d env cnd step b st' hfc hdiv

/-- **The progress bundle holds at every fuel.**  Structural induction on `n`.
Now UNCONDITIONAL: the two former arbitrary-config holes (dangling closure, abrupt
`for`-init) are discharged directly by the landed-def amendments
(`CallErr.badClosure`, the swallowing `ExecInit.some`). -/
theorem progress :
    ∀ n, Progress n := by
  intro n
  induction n with
  | zero =>
    exact ⟨fun st d env e _ _ => .zero st d env e,
           fun st d env es _ _ => .zero st d env es,
           fun st d fv vs _ _ => .zero st d fv vs,
           fun st d env s _ _ => .zero st d env s,
           fun st d env cnd step b _ _ => .zero st d env cnd step b,
           fun st d env ss _ _ => .zero st d env ss⟩
  | succ n ih =>
    obtain ⟨ihE, ihA, ihC, ihS, ihFl, ihSeq⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ProgressE (n+1)
      intro st d env e hnc hne
      exact progressE_succ ihE ihA ihC st d env e hnc hne
    · -- ProgressArgs (n+1)
      intro st d env es hnc hne
      exact progressArgs_succ ihE ihA st d env es hnc hne
    · -- ProgressC (n+1)
      intro st d fv vs hnc hne
      exact progressC_succ ihSeq st d fv vs hnc hne
    · -- ProgressS (n+1)
      intro st d env s hnc hne
      exact progressS_succ ihE ihS ihFl ihSeq st d env s hnc hne
    · -- ProgressFl (n+1)
      intro st d env cnd step b hnc hne
      exact progressFl_succ ihE ihS ihFl st d env cnd step b hnc hne
    · -- ProgressSeq (n+1)
      intro st d env ss hnc hne
      exact progressSeq_succ ihS ihSeq st d env ss hnc hne

/-! ## `StmtDispatchD`, closed (UNCONDITIONAL)

`StmtDispatchD` is `progress`'s `ProgressS` conjunct wrapped in `Classical.em`:
split on `∃ result`; then on `ExecErr`; the last branch is `∀ n, SApprox n` by
`progress` at every `n`. -/

/-- **`StmtDispatchD`, closed** — unconditional (both former arbitrary-config
holes are discharged inside `progress` by the landed-def amendments). -/
theorem stmtDispatchD_holds : StmtDispatchD := by
  intro st d env s
  by_cases hc : ∃ st' status, ExecS st d env s st' status
  · exact Or.inl hc
  by_cases he : ExecErr st d env s
  · exact Or.inr (Or.inl he)
  · refine Or.inr (Or.inr ?_)
    intro n
    exact (progress n).2.2.2.1 st d env s hc he

/-! ## `hroot`, closed (modulo the top-level-abrupt hole)

`hroot p : (∃ st' status, ExecSeq initSt 0 0 p st' status) → ∃ out, BigStep p out`
is FALSE as literally stated (an abrupt top-level status is an `ExecSeq` but not a
`BigStep`; see the module docstring).  What is TRUE — and what
`trichotomy_of_dispatch4` actually needs once we route the abrupt case to the
error disjunct — is a *dichotomy*: a top-level completion is either a `BigStep`
(`.normal`) or a `BigStepErr` (abrupt, via `topLevelAbruptErrs`).  We therefore
DON'T use `trichotomy_of_stmtDispatchD` (whose `hroot` forces the false shape);
we re-assemble the top level directly. -/

/-- A top-level completing sequence is a clean `BigStep` OR a `BigStepErr`,
routing the abrupt-status completions to the error disjunct via
`topLevelAbruptErrs` (the amended `BigStepErr`'s `TopAbrupt` disjunct). -/
theorem bigStep_or_err_of_execSeq (p : Program)
    {st' : St} {status : Status} (h : ExecSeq initSt 0 0 p st' status) :
    (∃ out, BigStep p out) ∨ BigStepErr p := by
  cases status with
  | normal => exact Or.inl ⟨st'.out, st', h, rfl⟩
  | brk => exact Or.inr (topLevelAbruptErrs p st' .brk (by intro h; cases h) h)
  | cont => exact Or.inr (topLevelAbruptErrs p st' .cont (by intro h; cases h) h)
  | ret v => exact Or.inr (topLevelAbruptErrs p st' (.ret v) (by intro h; cases h) h)

/-! ## The capstone

Re-assemble `Trichotomy` directly (not via `trichotomy_of_dispatch4`, whose
`hroot` slot forces the false shape), reusing `approx_of_nodeDispatch4` and
`nodeDispatch4_of_stmtDispatchD` for the divergence half. -/

/-- **`Trichotomy`, closed — UNCONDITIONAL.**  All three former
spec-completeness holes are discharged by the landed-def amendments (all three
were UNREACHABLE from `initSt`; the amendments merely make the arbitrary-config
quantifiers total):

* Hole 1 — top-level abrupt status → `BigStepErr` via the new `TopAbrupt`
  disjunct (`topLevelAbruptErrs`);
* Hole 2 — unresolvable closure address → `CallErr.badClosure`
  (`danglingClosureErrs`);
* Hole 3 — abrupt `for`-init is SWALLOWED by the generalized `ExecInit.some`
  (C-faithful; it PROGRESSES rather than errors), so it never blocks progress. -/
theorem trichotomy_unconditional : Trichotomy := by
  have hnode : NodeDispatch4 :=
    nodeDispatch4_of_stmtDispatchD stmtDispatchD_holds
  intro p
  by_cases hterm : ∃ st' status, ExecSeq initSt 0 0 p st' status
  · obtain ⟨st', status, hexec⟩ := hterm
    rcases bigStep_or_err_of_execSeq p hexec with hbs | herr
    · exact Or.inl hbs
    · exact Or.inr (Or.inl herr)
  by_cases herr : BigStepErr p
  · exact Or.inr (Or.inl herr)
  · exact Or.inr (Or.inr (fun n =>
      approx_of_nodeDispatch4 hnode n initSt 0 0 p hterm
        (fun hseqerr => herr (Or.inl hseqerr))))

/-! ## `htri`-shaped corollary for `interpSimClosed_of_families`

`interpSimClosed_of_families` (`Vsa/Sim/InterpSimFinal.lean`) consumes a
`htri : Trichotomy` argument by that exact name/type.  `trichotomy_unconditional`
IS a `Trichotomy`, so it plugs in directly with no residual premises. -/

/-- The `htri` argument for `interpSimClosed_of_families`, ready to plug in
unconditionally. -/
theorem htri_unconditional : Trichotomy :=
  trichotomy_unconditional

end Vsa.While
