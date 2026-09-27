import VsaIris.Stack
import Vsa.While.StackNeed
import Vsa.Sim.LayoutInstance

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.While Vsa.Sim.LayoutInstance

def stackBudget (need d : Nat) : Nat :=
  need + (maxCallDepth - d) * perCallBudget + evalFrame + helperHeadroom

def evalNeed (e : Expr) (d : Nat) : Nat := stackBudget e.stackNeed d

def execNeed (s : Stmt) (d : Nat) : Nat := stackBudget s.stackNeed d

theorem execNeed_def (s : Stmt) (d : Nat) :
    execNeed s d = s.stackNeed + (maxCallDepth - d) * perCallBudget + evalFrame + helperHeadroom :=
    rfl

theorem stackBudget_child {nc np d f : Nat} (h : nc + f ≤ np) :
    stackBudget nc d + f ≤ stackBudget np d := by
  unfold stackBudget; omega

theorem stackBudget_call {nb np d : Nat} (hd : d < maxCallDepth) (hb : nb ≤ perCallBudget)
    (hp : evalFrame ≤ np) : stackBudget nb (d + 1) + evalFrame ≤ stackBudget np d := by
  unfold stackBudget
  have hk : maxCallDepth - d = (maxCallDepth - (d + 1)) + 1 := by omega
  rw [hk, Nat.succ_mul]
  omega

theorem evalNeed_child {e e' : Expr} {d f : Nat} (h : e'.stackNeed + f ≤ e.stackNeed) :
    evalNeed e' d + f ≤ evalNeed e d := stackBudget_child h

theorem execNeed_child {s s' : Stmt} {d f : Nat} (h : s'.stackNeed + f ≤ s.stackNeed) :
    execNeed s' d + f ≤ execNeed s d := stackBudget_child h

theorem evalNeed_of_stmt {e : Expr} {s : Stmt} {d f : Nat} (h : e.stackNeed + f ≤ s.stackNeed) :
    evalNeed e d + f ≤ execNeed s d := stackBudget_child h

theorem evalNeed_assign (x : String) (e : Expr) (d : Nat) :
    evalNeed e d + evalFrame ≤ evalNeed (.assign x e) d :=
  evalNeed_child (by simp only [Expr.stackNeed]; omega)

theorem evalNeed_unary (op : UnOp) (e : Expr) (d : Nat) :
    evalNeed e d + evalFrame ≤ evalNeed (.unary op e) d :=
  evalNeed_child (by simp only [Expr.stackNeed]; omega)

theorem evalNeed_binary_left (op : BinOp) (l r : Expr) (d : Nat) :
    evalNeed l d + evalFrame ≤ evalNeed (.binary op l r) d :=
  evalNeed_child (by simp only [Expr.stackNeed]; omega)

theorem evalNeed_binary_right (op : BinOp) (l r : Expr) (d : Nat) :
    evalNeed r d + evalFrame ≤ evalNeed (.binary op l r) d :=
  evalNeed_child (by simp only [Expr.stackNeed]; omega)

theorem evalNeed_logical_left (op : LogOp) (l r : Expr) (d : Nat) :
    evalNeed l d + evalFrame ≤ evalNeed (.logical op l r) d :=
  evalNeed_child (by simp only [Expr.stackNeed]; omega)

theorem evalNeed_logical_right (op : LogOp) (l r : Expr) (d : Nat) :
    evalNeed r d + evalFrame ≤ evalNeed (.logical op l r) d :=
  evalNeed_child (by simp only [Expr.stackNeed]; omega)

theorem evalNeed_call_fn (f : Expr) (args : List Expr) (d : Nat) :
    evalNeed f d + evalFrame ≤ evalNeed (.call f args) d :=
  evalNeed_child (by simp only [Expr.stackNeed]; omega)

theorem evalNeed_call_arg {a f : Expr} {args : List Expr} (ha : a ∈ args) (d : Nat) :
    evalNeed a d + evalFrame ≤ evalNeed (.call f args) d :=
  evalNeed_child (by
    have := Expr.stackNeedList_mem_le ha
    simp only [Expr.stackNeed]; omega)

theorem execNeed_expr (e : Expr) (d : Nat) :
    evalNeed e d + execFrame ≤ execNeed (.expr e) d :=
  evalNeed_of_stmt (by simp only [Stmt.stackNeed]; omega)

theorem execNeed_varDecl (x : String) (e : Expr) (d : Nat) :
    evalNeed e d + execFrame ≤ execNeed (.varDecl x (some e)) d :=
  evalNeed_of_stmt (by simp only [Stmt.stackNeed]; omega)

theorem execNeed_ret (e : Expr) (d : Nat) :
    evalNeed e d + execFrame ≤ execNeed (.ret (some e)) d :=
  evalNeed_of_stmt (by simp only [Stmt.stackNeed]; omega)

theorem execNeed_block {s : Stmt} {ss : List Stmt} (hs : s ∈ ss) (d : Nat) :
    execNeed s d + execFrame ≤ execNeed (.block ss) d :=
  execNeed_child (by
    have := Stmt.stackNeedList_mem_le hs
    simp only [Stmt.stackNeed]; omega)

theorem execNeed_if_cond (c : Expr) (t : Stmt) (e : Option Stmt) (d : Nat) :
    evalNeed c d + execFrame ≤ execNeed (.ifStmt c t e) d :=
  evalNeed_of_stmt (by cases e <;> simp only [Stmt.stackNeed] <;> omega)

theorem execNeed_if_then (c : Expr) (t : Stmt) (e : Option Stmt) (d : Nat) :
    execNeed t d + execFrame ≤ execNeed (.ifStmt c t e) d :=
  execNeed_child (by cases e <;> simp only [Stmt.stackNeed] <;> omega)

theorem execNeed_if_else (c : Expr) (t el : Stmt) (d : Nat) :
    execNeed el d + execFrame ≤ execNeed (.ifStmt c t (some el)) d :=
  execNeed_child (by simp only [Stmt.stackNeed]; omega)

theorem execNeed_while_cond (c : Expr) (b : Stmt) (d : Nat) :
    evalNeed c d + execFrame ≤ execNeed (.whileStmt c b) d :=
  evalNeed_of_stmt (by simp only [Stmt.stackNeed]; omega)

theorem execNeed_while_body (c : Expr) (b : Stmt) (d : Nat) :
    execNeed b d + execFrame ≤ execNeed (.whileStmt c b) d :=
  execNeed_child (by simp only [Stmt.stackNeed]; omega)

theorem execNeed_for_init {i : Stmt} {io : Option Stmt} (hi : io = some i)
    (c st : Option Expr) (b : Stmt) (d : Nat) :
    execNeed i d + execFrame ≤ execNeed (.forStmt io c st b) d :=
  execNeed_child (by
    subst hi; simp only [Stmt.stackNeed, Stmt.stackNeedOpt]; omega)

theorem execNeed_for_cond {c : Expr} {co : Option Expr} (hc : co = some c)
    (i : Option Stmt) (st : Option Expr) (b : Stmt) (d : Nat) :
    evalNeed c d + execFrame ≤ execNeed (.forStmt i co st b) d :=
  evalNeed_of_stmt (by
    subst hc; simp only [Stmt.stackNeed, Expr.stackNeedOpt]; omega)

theorem execNeed_for_step {st : Expr} {sto : Option Expr} (hs : sto = some st)
    (i : Option Stmt) (c : Option Expr) (b : Stmt) (d : Nat) :
    evalNeed st d + execFrame ≤ execNeed (.forStmt i c sto b) d :=
  evalNeed_of_stmt (by
    subst hs; simp only [Stmt.stackNeed, Expr.stackNeedOpt]; omega)

theorem execNeed_for_body (i : Option Stmt) (c st : Option Expr) (b : Stmt) (d : Nat) :
    execNeed b d + execFrame ≤ execNeed (.forStmt i c st b) d :=
  execNeed_child (by simp only [Stmt.stackNeed]; omega)

theorem execNeed_callBody {s : Stmt} {body : List Stmt} {f : Expr} {args : List Expr} {d : Nat}
    (hd : d < maxCallDepth) (hb : Stmt.stackNeedList body ≤ perCallBudget) (hs : s ∈ body) :
    execNeed s (d + 1) + evalFrame ≤ evalNeed (.call f args) d :=
  stackBudget_call hd (Nat.le_trans (Stmt.stackNeedList_mem_le hs) hb)
    (by simp only [Expr.stackNeed]; omega)

theorem Stmt.bodiesBound_of_mem {P : Nat} : ∀ {ss : List Stmt} {s : Stmt},
    Stmt.bodiesBoundList P ss = true → s ∈ ss → s.bodiesBound P = true
  | [], _, _, hs => absurd hs (by simp)
  | t :: ts, s, h, hs => by
    simp only [Stmt.bodiesBoundList, Bool.and_eq_true] at h
    cases List.mem_cons.mp hs with
    | inl he => exact he ▸ h.1
    | inr ht => exact Stmt.bodiesBound_of_mem h.2 ht

theorem execNeed_of_stackFits {p : Program} (h : ProgramStackFits p)
    {s : Stmt} (hs : s ∈ p) : stackSL.lo + execNeed s 0 ≤ spEntry - interpRunFrame := by
  have hle := Stmt.stackNeedList_mem_le hs
  have hn := h.need
  have hlo : stackSL.lo = 0x87800000 := rfl
  have hspv : spEntry = 0x87fffd00 := rfl
  have hfr : interpRunFrame = 176 := rfl
  have hhr : helperHeadroom = 2048 := rfl
  rw [execNeed_def, Nat.sub_zero]
  omega

theorem bodiesBound_of_stackFits {p : Program} (h : ProgramStackFits p)
    {s : Stmt} (hs : s ∈ p) : s.bodiesBound perCallBudget = true :=
  Stmt.bodiesBound_of_mem h.bodies hs

end VsaIris.Interp
