import Vsa.Sim.DivergeSim
import Vsa.Refinement

/-!
# Layer 8 — the CLOSE skeleton (stuck side): `stuckSimClosed`

`DivergeSim.stuckSim` is the assembled `stuck_sim` composition: from the
`Trichotomy` obligation and the two *packaged* forward-simulation arms — the
error arm (`BigStepErr p → stuck_sim`) and the divergence arm
(`BigStepDiverges p → stuck_sim`) — a program with no clean `BigStep` lands in
`stuck_sim`'s disjunction. This file **supplies both arms** from their landed
discharges, exposing the exact aggregated M5 residual bundle:

* **error arm** ← `stuck_of_bigStepErrFull` (`ErrorSimFull`), conditional on the
  42 per-error-site residuals (`hVarUndef`…`hSeqTail`, each "this error node's
  compiled code reaches a `jal runtime_error` site ⇒ `Halts c out 70`");
* **divergence arm** ← `stuck_of_divergenceSim ∘ divergenceSim` (`DivergeSim`),
  conditional on the correspondence `Corr`, the single per-step progress
  residual `DivStep Corr` (`hDivStep`), and the entry correspondence
  `Corr c initSt 0 0 p` (`hentry`);
* **trichotomy** ← the `Trichotomy` obligation `htri` (constructed
  unconditionally in `Vsa/While/Trichotomy.lean` up to its own named residual).

`stuckSimClosed` concludes exactly `InterpSim.stuck_sim` for the fixed `p`/`c`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.StuckSimClose

open Vsa.While
open Vsa.Machine (Config Halts Diverges)
open Vsa.Refine (Layout Loaded InterpSim)
open Vsa.Sim

local notation "SpecSt" => Vsa.While.St

/-- **The close skeleton for `stuck_sim`.** For a fixed program `p` and machine
config `c`: given the trichotomy obligation, the divergence correspondence +
per-step residual + entry correspondence, and the 42 error-site residuals, a
program with no clean `BigStep` derivation diverges or exits nonzero — exactly
`InterpSim.stuck_sim`'s per-program conclusion. -/
theorem stuckSimClosed (p : Program) (c : Config)
    (htri : Trichotomy)
    (Corr : Config → SpecSt → Nat → Addr → List Stmt → Prop)
    (hDivStep : DivStep Corr)
    (hentry : Corr c initSt 0 0 p)
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
    (hno : ¬ ∃ out, BigStep p out) :
    Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0 :=
  stuckSim htri
    (fun herr =>
      stuck_of_bigStepErrFull c p
        hVarUndef hAssignE hAssignUnbound hBinaryL hBinaryR hBinaryOp hOrL hOrR hAndL
        hAndR hUnaryE hNegType hCallF hCallArgs hCallC hArgsHead hArgsTail hNotCallable
        hArity hDepth hBody hEscape hAssertFail hAssertArity hExpr hVarInit hBlock hIfCond
        hIfThen hIfElse hWhileCond hWhileBody hWhileLoop hForInit hForLoop hRet hFlCond
        hFlBody hFlStep hFlLoop hSeqHead hSeqTail herr)
    (fun hdiv => stuck_of_divergenceSim Corr hDivStep hentry hdiv)
    hno

end Vsa.Sim.StuckSimClose
