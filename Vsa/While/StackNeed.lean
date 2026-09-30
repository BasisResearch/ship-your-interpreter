import Vsa.While.Ast
import Vsa.While.Semantics
import Vsa.Alloc

namespace Vsa.While

def evalFrame : Nat := 1088

def execFrame : Nat := 176

def perCallBudget : Nat := 6144

mutual

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

def Expr.stackNeedList : List Expr → Nat
  | [] => 0
  | e :: es => max e.stackNeed (Expr.stackNeedList es)

end

def Expr.stackNeedOpt : Option Expr → Nat
  | none => 0
  | some e => e.stackNeed

mutual

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

def Stmt.stackNeedList : List Stmt → Nat
  | [] => 0
  | s :: ss => max s.stackNeed (Stmt.stackNeedList ss)

def Stmt.stackNeedOpt : Option Stmt → Nat
  | none => 0
  | some s => s.stackNeed

end

mutual

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

def StoreBodiesBound (store : Store) (P : Nat) : Prop :=
  ∀ (a : Nat) (cd : ClosureData), store.closures[a]? = some cd →
    Stmt.stackNeedList cd.body ≤ P ∧ Stmt.bodiesBoundList P cd.body = true

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

theorem _root_.Vsa.Alloc.StackOK.mono {SL : Vsa.Alloc.StackLayout}
    {sp : BitVec 64} {h h' : Nat} (hle : h' ≤ h)
    (hok : Vsa.Alloc.StackOK SL sp h) : Vsa.Alloc.StackOK SL sp h' :=
  ⟨Nat.le_trans (Nat.add_le_add_left hle SL.lo) hok.1, hok.2.1, hok.2.2⟩

theorem Expr.bodiesBound_unary {P : Nat} {op : UnOp} {e : Expr}
    (h : (Expr.unary op e).bodiesBound P = true) : e.bodiesBound P = true := h

theorem Expr.bodiesBound_logical {P : Nat} {op : LogOp} {l r : Expr}
    (h : (Expr.logical op l r).bodiesBound P = true) :
    l.bodiesBound P = true ∧ r.bodiesBound P = true := by
  simp only [Expr.bodiesBound, Bool.and_eq_true] at h; exact h

theorem Expr.bodiesBound_call {P : Nat} {f : Expr} {args : List Expr}
    (h : (Expr.call f args).bodiesBound P = true) :
    f.bodiesBound P = true ∧ Expr.bodiesBoundList P args = true := by
  simp only [Expr.bodiesBound, Bool.and_eq_true] at h; exact h

end Vsa.While
