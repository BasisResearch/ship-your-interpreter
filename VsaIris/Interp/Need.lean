import VsaIris.Stack
import Vsa.While.StackNeed
import Vsa.Sim.LayoutInstance

/-!
# `evalNeed` / `execNeed`: the stack budget of a node (work package F3)

INTERP_DESIGN.md §2 F3. The stack a call to `eval_expr`/`exec_stmt` may use is
ItemZero's budget, verbatim from `EvalEntry.stackBudget`
(`Vsa/Sim/InterpEntry.lean:630`):

```
evalNeed e d = e.stackNeed + (maxCallDepth - d) * perCallBudget + evalFrame
```

xv6iris spells a budget as the sum, never as a round number
(`durable-notes.md`, "A stack-budget premise is arithmetic"), so everything
here is stated over `Expr.stackNeed`/`Stmt.stackNeed` and the two constants,
and there is ONE arithmetic lemma underneath: `stackBudget_child`, the Iris
route's `Vsa.Alloc.StackOK.child`. Every arm's own inequality is that lemma at
the node's definitional need (`node.stackNeed = frame + max over children`).

The second lemma is `stackBudget_call`: a closure body runs at depth `d + 1`,
and one whole call level fits `perCallBudget` (`Expr.bodiesBound` /
`StoreBodiesBound`), which is what makes the depth term pay for it.

The boundary bridge is S1's: `ProgramStackFits` (`Vsa/Sim/LayoutInstance.lean`,
the `Loaded` field Q1 added) gives the first `exec_stmt` call's `execNeed`
below `interp_run`'s frame, both as arithmetic and as the Iris carve
`stackScratch_boundary`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.While Vsa.Sim.LayoutInstance

/-! ## The budget -/

/-- The budget of a node with structural need `need`, at call depth `d`:
its own chain, every remaining call level, and the callee-`value_*` frame. -/
def stackBudget (need d : Nat) : Nat :=
  need + (maxCallDepth - d) * perCallBudget + evalFrame

/-- `eval_expr`'s budget, verbatim from `EvalEntry.stackBudget`. -/
def evalNeed (e : Expr) (d : Nat) : Nat := stackBudget e.stackNeed d

/-- `exec_stmt`'s budget, verbatim from `ExecEntry.stackBudget`. -/
def execNeed (s : Stmt) (d : Nat) : Nat := stackBudget s.stackNeed d

theorem evalNeed_def (e : Expr) (d : Nat) :
    evalNeed e d = e.stackNeed + (maxCallDepth - d) * perCallBudget + evalFrame := rfl

theorem execNeed_def (s : Stmt) (d : Nat) :
    execNeed s d = s.stackNeed + (maxCallDepth - d) * perCallBudget + evalFrame := rfl

/-! ## The two arithmetic lemmas -/

/-- **The child-frame step** (the Iris route's `Vsa.Alloc.StackOK.child`): if
the child's structural need plus the frame the parent spills fits the parent's
structural need, the child's budget plus that frame fits the parent's, at the
SAME call depth. For every structural node the premise is definitional. -/
theorem stackBudget_child {nc np d f : Nat} (h : nc + f ≤ np) :
    stackBudget nc d + f ≤ stackBudget np d := by
  unfold stackBudget; omega

/-- **The call step**: a closure body runs at depth `d + 1`, and one whole
call level fits `perCallBudget` (`Expr.bodiesBound`, `StoreBodiesBound`), so
the depth term pays for the body and the parent's own frame is free. -/
theorem stackBudget_call {nb np d : Nat} (hd : d < maxCallDepth) (hb : nb ≤ perCallBudget)
    (hp : evalFrame ≤ np) : stackBudget nb (d + 1) + evalFrame ≤ stackBudget np d := by
  unfold stackBudget
  have hk : maxCallDepth - d = (maxCallDepth - (d + 1)) + 1 := by omega
  rw [hk, Nat.succ_mul]
  omega

/-- The budget is monotone in the structural need. -/
theorem stackBudget_mono {n n' d : Nat} (h : n ≤ n') : stackBudget n d ≤ stackBudget n' d := by
  unfold stackBudget; omega

/-! ## The four bridges

A parent arm hands a child its budget at the same depth, after spilling `f`
bytes of frame. The four combinations of `eval`/`exec` parent and child are
one lemma each over `stackBudget_child`. -/

theorem evalNeed_child {e e' : Expr} {d f : Nat} (h : e'.stackNeed + f ≤ e.stackNeed) :
    evalNeed e' d + f ≤ evalNeed e d := stackBudget_child h

theorem execNeed_child {s s' : Stmt} {d f : Nat} (h : s'.stackNeed + f ≤ s.stackNeed) :
    execNeed s' d + f ≤ execNeed s d := stackBudget_child h

theorem evalNeed_of_stmt {e : Expr} {s : Stmt} {d f : Nat} (h : e.stackNeed + f ≤ s.stackNeed) :
    evalNeed e d + f ≤ execNeed s d := stackBudget_child h

theorem execNeed_of_expr {s : Stmt} {e : Expr} {d f : Nat} (h : s.stackNeed + f ≤ e.stackNeed) :
    execNeed s d + f ≤ evalNeed e d := stackBudget_child h

/-! ## The arms

One inequality per arm of the two recursors, each `..._child` at the node's
definitional need. `evalFrame`/`execFrame` are the frames `eval_expr` and
`exec_stmt` spill (`addi sp,sp,-1088` / `-176`). -/

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

/-- **The call arm**: the closure body's statements run at depth `d + 1`,
inside one `perCallBudget` level (`StoreBodiesBound`). -/
theorem execNeed_callBody {s : Stmt} {body : List Stmt} {f : Expr} {args : List Expr} {d : Nat}
    (hd : d < maxCallDepth) (hb : Stmt.stackNeedList body ≤ perCallBudget) (hs : s ∈ body) :
    execNeed s (d + 1) + evalFrame ≤ evalNeed (.call f args) d :=
  stackBudget_call hd (Nat.le_trans (Stmt.stackNeedList_mem_le hs) hb)
    (by simp only [Expr.stackNeed]; omega)

/-! ## `bodiesBound` through a list -/

theorem Stmt.bodiesBound_of_mem {P : Nat} : ∀ {ss : List Stmt} {s : Stmt},
    Stmt.bodiesBoundList P ss = true → s ∈ ss → s.bodiesBound P = true
  | [], _, _, hs => absurd hs (by simp)
  | t :: ts, s, h, hs => by
    simp only [Stmt.bodiesBoundList, Bool.and_eq_true] at h
    cases List.mem_cons.mp hs with
    | inl he => exact he ▸ h.1
    | inr ht => exact Stmt.bodiesBound_of_mem h.2 ht

/-! ## The boundary (S1's `ProgramStackFits`) -/

/-- **The first `exec_stmt` call's budget**, from `Loaded`'s stack
admissibility: every top-level statement's `execNeed` at depth 0 fits below
`interp_run`'s frame. This is `ProgramStackFits.execBudget`
(`Vsa/Sim/LayoutInstance.lean`) as arithmetic on `execNeed`. -/
theorem execNeed_of_stackFits {p : Program} (h : ProgramStackFits p)
    {s : Stmt} (hs : s ∈ p) : stackSL.lo + execNeed s 0 ≤ spEntry - interpRunFrame := by
  have hle := Stmt.stackNeedList_mem_le hs
  have hn := h.need
  have hlo : stackSL.lo = 0x87800000 := rfl
  have hspv : spEntry = 0x87fffd00 := rfl
  have hfr : interpRunFrame = 176 := rfl
  rw [execNeed_def, Nat.sub_zero]
  omega

/-- Every top-level statement's `.fn` literals fit the per-call budget. -/
theorem bodiesBound_of_stackFits {p : Program} (h : ProgramStackFits p)
    {s : Stmt} (hs : s ∈ p) : s.bodiesBound perCallBudget = true :=
  Stmt.bodiesBound_of_mem h.bodies hs

section Iris

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- **The boundary carve**: from the owned C stack below `interp_run`'s
post-spill `sp`, hand the first `exec_stmt` call its `execNeed` scratch and
keep the rest. The premise is `Loaded interpRunLayout`'s `stack_admissible`
field (Q1, S1), through `ProgramStackFits.execNeed_fits`. -/
theorem stackScratch_boundary {p : Program} (h : ProgramStackFits p) {s : Stmt} (hs : s ∈ p)
    {sp0 : BitVec 64} (hsp : sp0.toNat = spEntry - interpRunFrame) :
    blockOwn (GF := GF) stackSL.lo (sp0.toNat - stackSL.lo) ⊢
      blockOwn stackSL.lo (sp0.toNat - stackSL.lo - execNeed s 0) ∗
        stackScratch sp0 (execNeed s 0) := by
  have hfit := execNeed_of_stackFits h hs
  unfold stackScratch
  iapply blockOwn_split stackSL.lo (sp0.toNat - stackSL.lo)
    (sp0.toNat - stackSL.lo - execNeed s 0) (sp0.toNat - execNeed s 0) (execNeed s 0)
    (by omega) (by omega) (by omega)

end Iris

end VsaIris.Interp
