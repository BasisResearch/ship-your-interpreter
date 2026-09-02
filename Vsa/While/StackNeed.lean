import Vsa.While.Ast
import Vsa.While.Semantics
import Vsa.Alloc

/-!
# `StackNeed` — the recursion-sound stack-budget layer (ITEM ZERO phase B0)

The entry-condition layer's `stackOK` fields were CONSTANTS
(`EvalEntry`: 1088+1088, `ExecEntry`: 176+1088), but each `eval_expr`
recursion level consumes a real 1088-byte machine frame (and each
`exec_stmt` level 176 bytes), so a child's entry demand strictly exceeds
what a constant parent entry supplies — the root cause behind every
∀-closed `sp_headroom`-class residual oracle (falsity #13; ledger
`recursion-stack-budget-class`, 2026-09-01).

This module defines the structural byte-need functions the amended
entries are indexed by:

* `Expr.stackNeed` / `Stmt.stackNeed` — the frame bytes the arm chain for
  this node consumes at its OWN call level.  `.call`/`.fn` do NOT recurse
  into closure bodies structurally — a body executes at call depth `d+1`
  and is accounted by the uniform per-call-level budget `perCallBudget`
  via the `(maxCallDepth − d) * perCallBudget` term of the amended
  `stackOK` (design: `experiments/itemzero-design.md`).
* `Expr.bodiesBound` / `Stmt.bodiesBound` — every `.fn` literal's body
  (recursively) fits the per-call budget.
* `StoreBodiesBound` — every closure in the store has a fitting body
  (the store invariant; closure bodies originate from program `.fn`
  literals, so it is preserved by `define`/`allocFrame`/`allocClosure`).

Frame constants are the measured machine frames: `eval_expr` spills a
1088-byte frame (`addi sp,sp,-1088`), `exec_stmt` a 176-byte frame
(`ExecEntry.lean:24`).  `perCallBudget` caps ONE call level's total need;
with `maxCallDepth = 1000` and the linker stack `[0x87800000, 0x88000000)`
(8 MiB, `LayoutInstance.stackSL`), `1000 * 6144 = 6 MiB` leaves ~2 MiB for
the top-level program's own nesting.  Programs exceeding a budget are not
"properly loaded" (maxCallDepth-cap precedent).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

namespace Vsa.While

/-- `eval_expr`'s machine frame, bytes (`addi sp,sp,-1088`). -/
def evalFrame : Nat := 1088

/-- `exec_stmt`'s machine frame, bytes (`addi sp,sp,-176`). -/
def execFrame : Nat := 176

/-- The uniform per-call-level stack budget (bytes).  One closure call's
whole body chain (statement frames + expression frames, NOT nested calls)
must fit this; see the module doc for the sizing arithmetic. -/
def perCallBudget : Nat := 6144

mutual

/-- Structural stack need of evaluating `e` at one call level: own
`eval_expr` frame + the deepest child chain.  Call/fn bodies excluded
(accounted per call level by `perCallBudget`). -/
def Expr.stackNeed : Expr → Nat
  | .int _ => evalFrame
  | .str _ => evalFrame
  | .bool _ => evalFrame
  | .null => evalFrame
  | .var _ => evalFrame
  | .assign _ e => evalFrame + e.stackNeed
  | .binary _ l r => evalFrame + max l.stackNeed r.stackNeed
  | .logical _ l r => evalFrame + max l.stackNeed r.stackNeed
  | .unary _ e => evalFrame + e.stackNeed
  | .call f args => evalFrame + max f.stackNeed (Expr.stackNeedList args)
  | .fn _ _ _ => evalFrame

/-- Deepest need over an argument list (args evaluate sequentially at the
same sp). -/
def Expr.stackNeedList : List Expr → Nat
  | [] => 0
  | e :: es => max e.stackNeed (Expr.stackNeedList es)

end

/-- Need of an optional expression. -/
def Expr.stackNeedOpt : Option Expr → Nat
  | none => 0
  | some e => e.stackNeed

mutual

/-- Structural stack need of executing `s` at one call level: own
`exec_stmt` frame + the deepest inner chain (expressions evaluated from
the statement arm at the lowered sp). -/
def Stmt.stackNeed : Stmt → Nat
  | .expr e => execFrame + e.stackNeed
  | .varDecl _ none => execFrame
  | .varDecl _ (some e) => execFrame + e.stackNeed
  | .block ss => execFrame + Stmt.stackNeedList ss
  | .ifStmt c t none => execFrame + max c.stackNeed t.stackNeed
  | .ifStmt c t (some e) =>
      execFrame + max c.stackNeed (max t.stackNeed e.stackNeed)
  | .whileStmt c b => execFrame + max c.stackNeed b.stackNeed
  | .forStmt i c st b =>
      execFrame + max (Stmt.stackNeedOpt i)
        (max (Expr.stackNeedOpt c) (max (Expr.stackNeedOpt st) b.stackNeed))
  | .ret none => execFrame
  | .ret (some e) => execFrame + e.stackNeed
  | .brk => execFrame
  | .cont => execFrame

/-- Deepest need over a statement list (sequential, same sp). -/
def Stmt.stackNeedList : List Stmt → Nat
  | [] => 0
  | s :: ss => max s.stackNeed (Stmt.stackNeedList ss)

/-- Need of an optional inner statement. -/
def Stmt.stackNeedOpt : Option Stmt → Nat
  | none => 0
  | some s => s.stackNeed

end

mutual

/-- Every `.fn` literal reachable in `e` has a body whose statement chain
fits the per-call budget `P` (recursively, including fn literals inside
those bodies). -/
def Expr.bodiesBound (P : Nat) : Expr → Bool
  | .int _ | .str _ | .bool _ | .null | .var _ => true
  | .assign _ e => e.bodiesBound P
  | .binary _ l r => l.bodiesBound P && r.bodiesBound P
  | .logical _ l r => l.bodiesBound P && r.bodiesBound P
  | .unary _ e => e.bodiesBound P
  | .call f args => f.bodiesBound P && Expr.bodiesBoundList P args
  | .fn _ _ body =>
      decide (Stmt.stackNeedList body ≤ P) && Stmt.bodiesBoundList P body

def Expr.bodiesBoundList (P : Nat) : List Expr → Bool
  | [] => true
  | e :: es => e.bodiesBound P && Expr.bodiesBoundList P es

def Stmt.bodiesBound (P : Nat) : Stmt → Bool
  | .expr e => e.bodiesBound P
  | .varDecl _ none => true
  | .varDecl _ (some e) => e.bodiesBound P
  | .block ss => Stmt.bodiesBoundList P ss
  | .ifStmt c t none => c.bodiesBound P && t.bodiesBound P
  | .ifStmt c t (some e) => c.bodiesBound P && t.bodiesBound P && e.bodiesBound P
  | .whileStmt c b => c.bodiesBound P && b.bodiesBound P
  | .forStmt i c st b =>
      Stmt.bodiesBoundOpt P i && Expr.bodiesBoundOpt P c &&
      Expr.bodiesBoundOpt P st && b.bodiesBound P
  | .ret none => true
  | .ret (some e) => e.bodiesBound P
  | .brk => true
  | .cont => true

def Stmt.bodiesBoundList (P : Nat) : List Stmt → Bool
  | [] => true
  | s :: ss => s.bodiesBound P && Stmt.bodiesBoundList P ss

def Stmt.bodiesBoundOpt (P : Nat) : Option Stmt → Bool
  | none => true
  | some s => s.bodiesBound P

def Expr.bodiesBoundOpt (P : Nat) : Option Expr → Bool
  | none => true
  | some e => e.bodiesBound P

end

/-- The store invariant: every closure body fits the per-call budget and
carries only fitting bodies itself.  Closure bodies originate from `.fn`
literals of the (bounded) program, so `define`/`allocFrame` preserve this
and `EvalE.fn` extends it from the expression-side bound. -/
def StoreBodiesBound (store : Store) (P : Nat) : Prop :=
  ∀ (a : Nat) (cd : ClosureData), store.closures[a]? = some cd →
    Stmt.stackNeedList cd.body ≤ P ∧ Stmt.bodiesBoundList P cd.body = true

/-! ## Arithmetic kit -/

theorem Expr.stackNeed_ge (e : Expr) : evalFrame ≤ e.stackNeed := by
  cases e <;> first
    | exact Nat.le_refl _
    | exact Nat.le_add_right _ _

theorem Stmt.stackNeed_ge (s : Stmt) : execFrame ≤ s.stackNeed := by
  cases s <;> first
    | exact Nat.le_refl _
    | exact Nat.le_add_right _ _
    | (rename_i o; cases o <;> first
        | exact Nat.le_refl _
        | exact Nat.le_add_right _ _)
    | (rename_i o _; cases o <;> first
        | exact Nat.le_refl _
        | exact Nat.le_add_right _ _)

theorem Expr.stackNeedList_mem_le {e : Expr} {es : List Expr}
    (h : e ∈ es) : e.stackNeed ≤ Expr.stackNeedList es := by
  induction es with
  | nil => cases h
  | cons hd tl ih =>
    cases h with
    | head => exact Nat.le_max_left _ _
    | tail _ htl => exact Nat.le_trans (ih htl) (Nat.le_max_right _ _)

theorem Stmt.stackNeedList_mem_le {s : Stmt} {ss : List Stmt}
    (h : s ∈ ss) : s.stackNeed ≤ Stmt.stackNeedList ss := by
  induction ss with
  | nil => cases h
  | cons hd tl ih =>
    cases h with
    | head => exact Nat.le_max_left _ _
    | tail _ htl => exact Nat.le_trans (ih htl) (Nat.le_max_right _ _)

/-- The monotone bridge: the amended (larger) headroom supplies every
consumer of the old constant one. -/
theorem _root_.Vsa.Alloc.StackOK.mono {SL : Vsa.Alloc.StackLayout}
    {sp : BitVec 64} {h h' : Nat} (hle : h' ≤ h)
    (hok : Vsa.Alloc.StackOK SL sp h) : Vsa.Alloc.StackOK SL sp h' :=
  ⟨Nat.le_trans (Nat.add_le_add_left hle SL.lo) hok.1, hok.2.1, hok.2.2⟩

/-- **The child-frame budget step** (the B1 fan-out kit's ONE arithmetic
lemma): a parent's budgeted `StackOK` at `sp` yields a child's budgeted
`StackOK` at the frame-lowered `sp - f`, whenever the child headroom plus the
consumed frame fits the parent headroom (`hle`; for every structural node this
is definitional — node need = frame + max over children).  Every
recursive-arm sim / stage-pre supplier forwards its child budget through
this, never by per-site `BitVec.toNat_sub` re-derivation. -/
theorem _root_.Vsa.Alloc.StackOK.child {SL : Vsa.Alloc.StackLayout}
    {sp f : BitVec 64} {h h' : Nat}
    (hf16 : f.toNat % 16 = 0) (hle : h' + f.toNat ≤ h)
    (hok : Vsa.Alloc.StackOK SL sp h) : Vsa.Alloc.StackOK SL (sp - f) h' := by
  obtain ⟨h1, h2, h3⟩ := hok
  have hsub : (sp - f).toNat = sp.toNat - f.toNat := by
    rw [BitVec.toNat_sub]
    have := sp.isLt; have := f.isLt
    omega
  refine ⟨?_, ?_, ?_⟩ <;> rw [hsub] <;> omega

/-! The `bodiesBound` projection kit: named eliminations from a composite
node's `.fn`-bodies bound to its children's (the boolean `&&` towers are
never split positionally at use sites). -/

theorem Expr.bodiesBound_assign {P : Nat} {x : String} {e : Expr}
    (h : (Expr.assign x e).bodiesBound P = true) : e.bodiesBound P = true := h

theorem Expr.bodiesBound_unary {P : Nat} {op : UnOp} {e : Expr}
    (h : (Expr.unary op e).bodiesBound P = true) : e.bodiesBound P = true := h

theorem Expr.bodiesBound_binary {P : Nat} {op : BinOp} {l r : Expr}
    (h : (Expr.binary op l r).bodiesBound P = true) :
    l.bodiesBound P = true ∧ r.bodiesBound P = true := by
  simp only [Expr.bodiesBound, Bool.and_eq_true] at h; exact h

theorem Expr.bodiesBound_logical {P : Nat} {op : LogOp} {l r : Expr}
    (h : (Expr.logical op l r).bodiesBound P = true) :
    l.bodiesBound P = true ∧ r.bodiesBound P = true := by
  simp only [Expr.bodiesBound, Bool.and_eq_true] at h; exact h

theorem Expr.bodiesBound_call {P : Nat} {f : Expr} {args : List Expr}
    (h : (Expr.call f args).bodiesBound P = true) :
    f.bodiesBound P = true ∧ Expr.bodiesBoundList P args = true := by
  simp only [Expr.bodiesBound, Bool.and_eq_true] at h; exact h

theorem Stmt.bodiesBound_expr {P : Nat} {e : Expr}
    (h : (Stmt.expr e).bodiesBound P = true) : e.bodiesBound P = true := h

#print axioms Expr.stackNeed_ge
#print axioms Stmt.stackNeed_ge
#print axioms Vsa.Alloc.StackOK.mono
#print axioms Vsa.Alloc.StackOK.child

end Vsa.While
