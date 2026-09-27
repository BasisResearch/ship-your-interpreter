import Vsa.Compiler.ForCode

/-!
# Forward simulation statements for the parts of a `for` statement

The initializer, condition, step and loop relations of the semantics run inside
a `for` statement's frame; their simulations name the enclosing statement's
code (`ForSegs`) for their positions.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

/-- The static facts of a `for` statement's code at `pos` under `C`. -/
structure ForOK (code : List Ins) (T : List String) (C : GCtx) (pos : Nat) (init : Option Stmt)
    (cnd step : Option Expr) (b : Stmt) (fs : Nat) : Prop where
  segs : ForSegs code T C pos init cnd step b
  pend : PosOK (fEx T C pos init cnd step b + 1)
  wi : WfOS T (fC1 C init b).Γ init
  wc : WfOE T (fC1 C init b).Γ cnd
  ws : WfOE T (fC1 C init b).Γ step
  wb : WfS T (fC1 C init b).Γ b
  ctx : CtxOK C
  tmp : 16 + 16 * tS (.forStmt init cnd step b) ≤ fs

/-- Forward simulation of a `for` initializer: it ends at the condition. -/
def XISpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (init : Option Stmt) (st' : St)
    (n : Nat) : Prop :=
  ∀ (V : View) (C : GCtx) (pos : Nat) (cnd step : Option Expr) (b : Stmt) (sp fs : Nat) (A : AM),
    ForOK code T C pos init cnd step b fs → MS code T V st d env (fC1 C init b).Γ sp fs A →
    A.pc = pcOf (pos + 4) →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V', SPost code T V st d env (fC1 C init b) sp fs (fHd T C pos init b) A n st' .normal V' B)

/-- Forward simulation of a passing `for` condition: it ends at the body. -/
def FCSpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (cnd : Option Expr) (st' : St)
    (n : Nat) : Prop :=
  ∀ (V : View) (C : GCtx) (pos : Nat) (init : Option Stmt) (step : Option Expr) (b : Stmt) (sp fs : Nat) (A : AM),
    ForOK code T C pos init cnd step b fs → MS code T V st d env (fC1 C init b).Γ sp fs A →
    A.pc = pcOf (fHd T C pos init b) →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V', SPost code T V st d env (fC1 C init b) sp fs (fPb T C pos init cnd b) A n st' .normal V' B)

/-- Forward simulation of a `for` step: it ends at the back jump. -/
def XSSpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (step : Option Expr) (st' : St)
    (n : Nat) : Prop :=
  ∀ (V : View) (C : GCtx) (pos : Nat) (init : Option Stmt) (cnd : Option Expr) (b : Stmt) (sp fs : Nat) (A : AM),
    ForOK code T C pos init cnd step b fs → MS code T V st d env (fC1 C init b).Γ sp fs A →
    A.pc = pcOf (fPs T C pos init cnd b) →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V', SPost code T V st d env (fC1 C init b) sp fs (fEx T C pos init cnd step b - 1) A n st' .normal V' B)

/-- Forward simulation of a `for` loop from its condition: it ends at the frame exit. -/
def FLSpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
    (st' : St) (t : Status) (n : Nat) : Prop :=
  ∀ (V : View) (C : GCtx) (pos : Nat) (init : Option Stmt) (sp fs : Nat) (A : AM),
    ForOK code T C pos init cnd step b fs → MS code T V st d env (fC1 C init b).Γ sp fs A →
    A.pc = pcOf (fHd T C pos init b) →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V', SPost code T V st d env (fC1 C init b) sp fs (fEx T C pos init cnd step b) A n st' t V' B)

end Vsa.Compiler
