import Vsa.Sim.StuckSimClose

/-!
# The aggregated M5 residual families — `DivFamily` / `ErrFamily`

The stuck-side (`InterpSim.stuck_sim`) obligation quantifies over all loaded
`(p, c)`.  Its two forward-simulation arms need their residuals ∀-closed over
`(p, c)`; this file packages them:

* **`DivFamily L`** — for every loaded `(p, c)`, a divergence correspondence
  `Corr` with its per-step progress residual `DivStep Corr` and the entry
  correspondence `Corr c initSt 0 0 p` (the `divergenceSim` interface).
* **`ErrFamily L`** — for every loaded `(p, c)`, `BigStepErr p` lands in
  `stuck_sim`'s disjunction at `c` (exactly `stuck_of_bigStepErrFull`'s output).
  `errFamily_of_sites` builds it from the **42 per-error-site residuals**, each
  ∀-closed over the config — this is where the M5 error bundle is precisely
  pinned.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.InterpSimBundle

open Vsa.While
open Vsa.Machine (Config Halts Diverges)
open Vsa.Refine (Layout Loaded)
open Vsa.Sim

local notation "SpecSt" => Vsa.While.St


/-- The per-program/config **divergence correspondence family**: for every loaded
`(p, c)`, a correspondence `Corr` with its per-step progress residual
`DivStep Corr` and the entry correspondence `Corr c initSt 0 0 p`.  This is the
∀-closed form `stuck_sim`'s divergence arm demands. -/
def DivFamily (L : Layout) : Prop :=
  ∀ (p : Program) (c : Config), Loaded L p c →
    ∃ Corr : Config → SpecSt → Nat → Addr → List Stmt → Prop,
      DivStep Corr ∧ Corr c initSt 0 0 p

/-- The **error arm** as a ∀-closed family: for every loaded `(p, c)`, a program
that hits a runtime error (`BigStepErr p`) lands in `stuck_sim`'s disjunction at
`c`.  This is exactly `stuck_of_bigStepErrFull`'s output, quantified over the
`(p, c)` that `stuck_sim` introduces. -/
def ErrFamily (L : Layout) : Prop :=
  ∀ (p : Program) (c : Config), Loaded L p c → BigStepErr p →
    Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0

/-- `ErrFamily` from the 42 per-error-site residuals (the M5 error bundle), each
∀-closed over the config `c`.  For each loaded `(p, c)` these are instantiated at
that `c` and fed to `stuck_of_bigStepErrFull`.  This is where the 42 error-site
residuals are precisely pinned. -/
theorem errFamily_of_sites (L : Layout)
    (hVarUndef : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String),
      st.store.get? env x = none → ErrHalts c)
    (hAssignE : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hAssignUnbound : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → st'.store.set? env x v = none → ErrHalts c)
    (hBinaryL : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hBinaryR : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' : SpecSt) (lv : Value),
      EvalE st d env l st' lv → EvalErr st' d env r → ErrHalts c → ErrHalts c)
    (hBinaryOp : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : SpecSt) (lv rv : Value),
      EvalE st d env l st' lv → EvalE st' d env r st'' rv →
      binOpSem st''.store op lv rv = none → ErrHalts c)
    (hOrL : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hOrR : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt)
      (lv : Value),
      EvalE st d env l st' lv → lv.truthy = false → EvalErr st' d env r →
      ErrHalts c → ErrHalts c)
    (hAndL : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr),
      EvalErr st d env l → ErrHalts c → ErrHalts c)
    (hAndR : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (l r : Expr) (st' : SpecSt)
      (lv : Value),
      EvalE st d env l st' lv → lv.truthy = true → EvalErr st' d env r →
      ErrHalts c → ErrHalts c)
    (hUnaryE : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (op : UnOp) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hNegType : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (st' : SpecSt)
      (v : Value),
      EvalE st d env e st' v → (∀ n : Int, v ≠ .int n) → ErrHalts c)
    (hCallF : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr),
      EvalErr st d env f → ErrHalts c → ErrHalts c)
    (hCallArgs : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' : SpecSt) (fv : Value),
      EvalE st d env f st' fv → EvalArgsErr st' d env args → ErrHalts c → ErrHalts c)
    (hCallC : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' : SpecSt) (fv : Value) (vs : List Value),
      EvalE st d env f st' fv → EvalArgs st' d env args st'' vs →
      CallErr st'' d fv vs → ErrHalts c → ErrHalts c)
    (hArgsHead : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hArgsTail : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' : SpecSt) (v : Value),
      EvalE st d env e st' v → EvalArgsErr st' d env es → ErrHalts c → ErrHalts c)
    (hNotCallable : ∀ (c : Config) (st : SpecSt) (d : Nat) (fv : Value) (vs : List Value),
      (∀ a, fv ≠ .closure a) → (∀ f, fv ≠ .native f) → ErrHalts c)
    (hArity : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length ≠ cd.params.length → ErrHalts c)
    (hDepth : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      ¬ d < maxCallDepth → ErrHalts c)
    (hBody : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeqErr ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body → ErrHalts c → ErrHalts c)
    (hEscape : ∀ (c : Config) (st : SpecSt) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : SpecSt) (status : Status),
      st.store.closures[a]? = some cd → vs.length = cd.params.length →
      d < maxCallDepth → st.store.allocFrame (some cd.env) = (store', frame) →
      ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
        st.out⟩ (d + 1) frame cd.body st' status →
      (status = .brk ∨ status = .cont) → ErrHalts c)
    (hAssertFail : ∀ (c : Config) (st : SpecSt) (d : Nat) (vs : List Value) (v m : Value),
      (vs = [v] ∨ vs = [v, m]) → v.truthy = false → ErrHalts c)
    (hAssertArity : ∀ (c : Config) (st : SpecSt) (d : Nat) (vs : List Value),
      (∀ v, vs ≠ [v]) → (∀ v m, vs ≠ [v, m]) → ErrHalts c)
    (hExpr : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hVarInit : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (x : String) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hBlock : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr),
      st.store.allocFrame (some env) = (store', inner) →
      ExecSeqErr ⟨store', st.out⟩ d inner ss → ErrHalts c → ErrHalts c)
    (hIfCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t : Stmt)
      (e : Option Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hIfThen : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t : Stmt)
      (e : Option Stmt) (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → ExecErr st' d env t →
      ErrHalts c → ErrHalts c)
    (hIfElse : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (t e : Stmt)
      (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = false → ExecErr st' d env e →
      ErrHalts c → ErrHalts c)
    (hWhileCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hWhileBody : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt)
      (st' : SpecSt) (v : Value),
      EvalE st d env cnd st' v → v.truthy = true → ExecErr st' d env b →
      ErrHalts c → ErrHalts c)
    (hWhileLoop : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (b : Stmt)
      (st' st'' : SpecSt) (v : Value) (status : Status),
      EvalE st d env cnd st' v → v.truthy = true → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecErr st'' d env (.whileStmt cnd b) →
      ErrHalts c → ErrHalts c)
    (hForInit : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (init : Stmt) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (store' : Store) (outer : Addr),
      st.store.allocFrame (some env) = (store', outer) →
      ExecErr ⟨store', st.out⟩ d outer init → ErrHalts c → ErrHalts c)
    (hForLoop : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' : SpecSt),
      st.store.allocFrame (some env) = (store', outer) →
      ExecInit ⟨store', st.out⟩ d outer init st' →
      ForLoopErr st' d outer cnd step b → ErrHalts c → ErrHalts c)
    (hRet : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (e : Expr),
      EvalErr st d env e → ErrHalts c → ErrHalts c)
    (hFlCond : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Expr) (step : Option Expr)
      (b : Stmt),
      EvalErr st d env cnd → ErrHalts c → ErrHalts c)
    (hFlBody : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' : SpecSt),
      ForCond st d env cnd st' → ExecErr st' d env b → ErrHalts c → ErrHalts c)
    (hFlStep : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr) (e : Expr)
      (b : Stmt) (st' st'' : SpecSt) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → EvalErr st'' d env e → ErrHalts c → ErrHalts c)
    (hFlLoop : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' : SpecSt) (status : Status),
      ForCond st d env cnd st' → ExecS st' d env b st'' status →
      (status = .normal ∨ status = .cont) → ExecStep st'' d env step st''' →
      ForLoopErr st''' d env cnd step b → ErrHalts c → ErrHalts c)
    (hSeqHead : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt),
      ExecErr st d env s → ErrHalts c → ErrHalts c)
    (hSeqTail : ∀ (c : Config) (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : SpecSt),
      ExecS st d env s st' .normal → ExecSeqErr st' d env ss → ErrHalts c → ErrHalts c) :
    ErrFamily L := by
  intro p c _ herr
  exact stuck_of_bigStepErrFull c p
    (hVarUndef c) (hAssignE c) (hAssignUnbound c) (hBinaryL c) (hBinaryR c) (hBinaryOp c)
    (hOrL c) (hOrR c) (hAndL c) (hAndR c) (hUnaryE c) (hNegType c) (hCallF c) (hCallArgs c)
    (hCallC c) (hArgsHead c) (hArgsTail c) (hNotCallable c) (hArity c) (hDepth c) (hBody c)
    (hEscape c) (hAssertFail c) (hAssertArity c) (hExpr c) (hVarInit c) (hBlock c) (hIfCond c)
    (hIfThen c) (hIfElse c) (hWhileCond c) (hWhileBody c) (hWhileLoop c) (hForInit c)
    (hForLoop c) (hRet c) (hFlCond c) (hFlBody c) (hFlStep c) (hFlLoop c) (hSeqHead c)
    (hSeqTail c) herr

end Vsa.Sim.InterpSimBundle
