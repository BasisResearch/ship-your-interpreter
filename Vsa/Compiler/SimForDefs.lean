import Vsa.Compiler.ForCode

namespace Vsa.Compiler

open Vsa.Sim Vsa.While

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

def XISpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (init : Option Stmt) (st' : St)
    (n : Nat) : Prop :=
  ∀ (V : View) (C : GCtx) (pos : Nat) (cnd step : Option Expr) (b : Stmt) (sp fs : Nat) (A : AM),
    ForOK code T C pos init cnd step b fs → MS code T V st d env (fC1 C init b).Γ sp fs A →
    A.pc = pcOf (pos + 4) →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V', SPost code T V st d env (fC1 C init b) sp fs (fHd T C pos init b) A n st' .normal V' B)

def FCSpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (cnd : Option Expr) (st' : St)
    (n : Nat) : Prop :=
  ∀ (V : View) (C : GCtx) (pos : Nat) (init : Option Stmt) (step : Option Expr) (b : Stmt) (sp fs : Nat) (A : AM),
    ForOK code T C pos init cnd step b fs → MS code T V st d env (fC1 C init b).Γ sp fs A →
    A.pc = pcOf (fHd T C pos init b) →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V', SPost code T V st d env (fC1 C init b) sp fs (fPb T C pos init cnd b) A n st' .normal V' B)

def XSSpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (step : Option Expr) (st' : St)
    (n : Nat) : Prop :=
  ∀ (V : View) (C : GCtx) (pos : Nat) (init : Option Stmt) (cnd : Option Expr) (b : Stmt) (sp fs : Nat) (A : AM),
    ForOK code T C pos init cnd step b fs → MS code T V st d env (fC1 C init b).Γ sp fs A →
    A.pc = pcOf (fPs T C pos init cnd b) →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V', SPost code T V st d env (fC1 C init b) sp fs (fEx T C pos init cnd step b - 1) A n st' .normal V' B)

def FLSpec (code : List Ins) (T : List String) (st : St) (d : Nat) (env : Addr) (cnd step : Option Expr) (b : Stmt)
    (st' : St) (t : Status) (n : Nat) : Prop :=
  ∀ (V : View) (C : GCtx) (pos : Nat) (init : Option Stmt) (sp fs : Nat) (A : AM),
    ForOK code T C pos init cnd step b fs → MS code T V st d env (fC1 C init b).Γ sp fs A →
    A.pc = pcOf (fHd T C pos init b) →
    Reaches code A (fun B => (B.pc = pcOf errPos ∧ ¬ Room V n) ∨
      ∃ V', SPost code T V st d env (fC1 C init b) sp fs (fEx T C pos init cnd step b) A n st' t V' B)

end Vsa.Compiler
