import Vsa.Compiler.SimAll
import Vsa.Compiler.Fail
import Vsa.While.CostExists

/-!
# Statements of the failure direction

`EStuck` … `FLStuck`: when an expression, argument list, call, statement,
statement list or `for` loop has no execution in the semantics, its code,
started from a related state under the hypotheses of the forward simulation,
fails within `n` steps (`Fail`: the error exit or `n` steps of running).
`StuckAt code T n` bundles the six statements at fuel `n`.

The forward simulation of executions that do exist comes from `sim_all`
through the cost companions (`spec_e` … `spec_q`).
-/

-- discipline: allow(R7-conj-tower-def) each `∃` is the witness of one semantic judgment or one cost output, not a post tower
namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- `e` has an evaluation. -/
def HasE (st : St) (d : Nat) (env : Addr) (e : Expr) : Prop := ∃ st' v, EvalE st d env e st' v

/-- `es` has an evaluation. -/
def HasA (st : St) (d : Nat) (env : Addr) (es : List Expr) : Prop := ∃ st' vs, EvalArgs st d env es st' vs

/-- Calling `fv` on `vs` has a result. -/
def HasC (st : St) (d : Nat) (fv : Value) (vs : List Value) : Prop := ∃ st' v, Vsa.While.Call st d fv vs st' v

/-- `s` has an execution. -/
def HasS (st : St) (d : Nat) (env : Addr) (s : Stmt) : Prop := ∃ st' t, ExecS st d env s st' t

/-- `ss` has an execution. -/
def HasQ (st : St) (d : Nat) (env : Addr) (ss : List Stmt) : Prop := ∃ st' t, ExecSeq st d env ss st' t

/-- The `for` loop from its condition has an execution. -/
def HasFL (st : St) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt) : Prop :=
  ∃ st' t, ForLoop st d env cnd step b st' t

/-- An expression without an evaluation fails. -/
def EStuck (code : List Ins) (T : List String) (n : Nat) (st : St) (d : Nat) (env : Addr) (e : Expr) : Prop :=
  ∀ (V : View) (Γ : List (List String)) (sp fs k pos : Nat) (A : AM),
    MS code T V st d env Γ sp fs A → A.pc = pcOf pos → WfE T Γ e →
    Seg code pos (gexpr T Γ k pos e) → PosOK (pos + (gexpr T Γ k pos e).length) →
    16 + 16 * (k + tE e) ≤ fs → ¬ HasE st d env e → Fail code n A

/-- An argument list without an evaluation fails. -/
def AStuck (code : List Ins) (T : List String) (n : Nat) (st : St) (d : Nat) (env : Addr) (es : List Expr) :
    Prop :=
  ∀ (V : View) (Γ : List (List String)) (sp fs k pos : Nat) (A : AM),
    MS code T V st d env Γ sp fs A → A.pc = pcOf pos → WfArgs T Γ es →
    Seg code pos (gargs T Γ k pos es) → PosOK (pos + (gargs T Γ k pos es).length) →
    16 + 16 * tArgs k es ≤ fs → 16 + 16 * (k + es.length) ≤ fs → ¬ HasA st d env es → Fail code n A

/-- A call without a result fails. -/
def CStuck (code : List Ins) (T : List String) (n : Nat) (st : St) (d : Nat) (fv : Value) (vs : List Value) :
    Prop :=
  ∀ (V : View) (env : Addr) (Γ : List (List String)) (sp fs k pos : Nat) (A : AM),
    MS code T V st d env Γ sp fs A → A.pc = pcOf pos → InTmp V.H A.mem V.h sp k fv →
    InTmps V.H A.mem V.h sp (k + 1) vs → vs.length ≤ maxArgs →
    Seg code pos (callCode k vs.length pos) → PosOK (pos + (callCode k vs.length pos).length) →
    16 + 16 * (k + 1 + vs.length) ≤ fs → ¬ HasC st d fv vs → Fail code n A

/-- A statement without an execution fails. -/
def SStuck (code : List Ins) (T : List String) (n : Nat) (st : St) (d : Nat) (env : Addr) (s : Stmt) : Prop :=
  ∀ (V : View) (C : GCtx) (sp fs pos : Nat) (A : AM),
    MS code T V st d env C.Γ sp fs A → A.pc = pcOf pos → WfS T C.Γ s → CtxOK C →
    Seg code pos (gstmt T C pos s) → PosOK (pos + (gstmt T C pos s).length) → 16 + 16 * tS s ≤ fs →
    ¬ HasS st d env s → Fail code n A

/-- A statement list without an execution fails. -/
def QStuck (code : List Ins) (T : List String) (n : Nat) (st : St) (d : Nat) (env : Addr) (ss : List Stmt) :
    Prop :=
  ∀ (V : View) (C : GCtx) (sp fs pos : Nat) (A : AM),
    MS code T V st d env C.Γ sp fs A → A.pc = pcOf pos → WfSeq T C.Γ ss → CtxOK C →
    Seg code pos (gseq T C pos ss) → PosOK (pos + (gseq T C pos ss).length) → 16 + 16 * tSeq ss ≤ fs →
    ¬ HasQ st d env ss → Fail code n A

/-- A `for` loop without an execution fails from its condition. -/
def FLStuck (code : List Ins) (T : List String) (n : Nat) (st : St) (d : Nat) (env : Addr) (cnd step : Option Expr)
    (b : Stmt) : Prop :=
  ∀ (V : View) (C : GCtx) (pos : Nat) (init : Option Stmt) (sp fs : Nat) (A : AM),
    ForOK code T C pos init cnd step b fs → MS code T V st d env (fC1 C init b).Γ sp fs A →
    A.pc = pcOf (fHd T C pos init b) → ¬ HasFL st d env cnd step b → Fail code n A

/-- The failure statements at fuel `n`. -/
structure StuckAt (code : List Ins) (T : List String) (n : Nat) : Prop where
  e : ∀ st d env e, EStuck code T n st d env e
  a : ∀ st d env es, AStuck code T n st d env es
  c : ∀ st d fv vs, CStuck code T n st d fv vs
  s : ∀ st d env s, SStuck code T n st d env s
  q : ∀ st d env ss, QStuck code T n st d env ss
  fl : ∀ st d env cnd step b, FLStuck code T n st d env cnd step b

theorem Fail.of_reaches {code : List Ins} {n : Nat} {A : AM} (h : Reaches code A (Fail code n)) :
    Fail code n A := by
  obtain ⟨B, r, hB⟩ := h
  exact Fail.of_star r hB

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

/-- The error exit fails. -/
theorem fail_err {n : Nat} {B : AM} (h : B.pc = pcOf errPos) : Fail code n B := by
  obtain ⟨B', r, -, -, hh⟩ := run_exit hR.fits (by decide : (70 : Nat) = 0 ∨ 70 = 70) hR.err h
  exact .inl ⟨B', r, hh⟩

/-- Reach the error exit or a failing state. -/
theorem Fail.of_err_or {n : Nat} {A : AM} {P : AM → Prop}
    (h : Reaches code A (fun B => B.pc = pcOf errPos ∧ P B ∨ Fail code n B)) : Fail code n A := by
  obtain ⟨B, r, hB⟩ := h
  rcases hB with ⟨h1, -⟩ | h2
  · exact Fail.of_star r (fail_err hR h1)
  · exact Fail.of_star r h2

theorem spec_e {st : St} {d : Nat} {env : Addr} {e : Expr} {st' : St} {v : Value}
    (D : EvalE st d env e st' v) : ∃ n, ESpec code T st d env e st' v n :=
  let ⟨n, C⟩ := EvalECost.exists D; ⟨n, (sim_all (T := T) hR).e C⟩

theorem spec_a {st : St} {d : Nat} {env : Addr} {es : List Expr} {st' : St} {vs : List Value}
    (D : EvalArgs st d env es st' vs) : ∃ n, ASpec code T st d env es st' vs n ∧ vs.length = es.length :=
  let ⟨n, C⟩ := EvalArgsCost.exists D; ⟨n, (sim_all (T := T) hR).a C, evalArgsCost_length C⟩

theorem spec_s {st : St} {d : Nat} {env : Addr} {s : Stmt} {st' : St} {t : Status}
    (D : ExecS st d env s st' t) : ∃ n, SSpec code T st d env s st' t n :=
  let ⟨n, C⟩ := ExecSCost.exists D; ⟨n, (sim_all (T := T) hR).s C⟩

theorem spec_q {st : St} {d : Nat} {env : Addr} {ss : List Stmt} {st' : St} {t : Status}
    (D : ExecSeq st d env ss st' t) : ∃ n, QSpec code T st d env ss st' t n :=
  let ⟨n, C⟩ := ExecSeqCost.exists D; ⟨n, (sim_all (T := T) hR).q C⟩

end

end Vsa.Compiler
