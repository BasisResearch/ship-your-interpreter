import Vsa.MemReprWithin

namespace Vsa.MemRepr
open Vsa.While

/-- One owned pointer cell and its represented target. -/
structure PointerReadWithin {α : Type} (m : Mem) (P : Nat → Prop)
    (R : Nat → α → Prop) (a p : Nat) (x : α) : Prop where
  read : read64 m a = some p
  covered : Covers P a 8
  target : R p x

/-- Common pointer-array view for statement, expression, and name arrays. -/
inductive PointerArrayWithin {α : Type} (m : Mem) (P : Nat → Prop)
    (R : Nat → α → Prop) : Nat → List α → Prop where
  | nil {a} : PointerArrayWithin m P R a []
  | cons {a p x xs} : PointerReadWithin m P R a p x →
      PointerArrayWithin m P R (a + 8) xs → PointerArrayWithin m P R a (x :: xs)

/-- Indexed access retains ownership of the cell and its selected target. -/
theorem PointerArrayWithin.get {α : Type} {m : Mem} {P : Nat → Prop}
    {R : Nat → α → Prop} {a : Nat} {xs : List α} (h : PointerArrayWithin m P R a xs)
    (i : Nat) (hi : i < xs.length) :
    ∃ p, PointerReadWithin m P R (a + 8 * i) p xs[i] := by
  induction h generalizing i with
  | nil => simp at hi
  | @cons a p x xs cell tail ih =>
    cases i with
    | zero => exact ⟨p, by simpa using cell⟩
    | succ i =>
      obtain ⟨q, hq⟩ := ih i (by simpa using hi)
      exact ⟨q, by simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq⟩

local macro "pointer_array_view" h:ident xs:ident a:ident n:ident : tactic =>
  `(tactic| (induction ($xs) generalizing $a $n with
    | nil => cases ($h); exact .nil
    | cons x xs ih =>
      cases ($h)
      exact .cons ⟨by assumption, by assumption, by assumption⟩ (ih (by assumption))))

/-- Statement arrays expose the common owned pointer-array view. -/
theorem StmtArrayReprWithin.pointers {m : Mem} {P : Nat → Prop} {a n : Nat}
    {ss : List Stmt} (h : StmtArrayReprWithin m P a n ss) :
    PointerArrayWithin m P (StmtReprWithin m P) a ss := by
  pointer_array_view h ss a n

/-- Expression arrays expose the common owned pointer-array view. -/
theorem ExprArrayReprWithin.pointers {m : Mem} {P : Nat → Prop} {a n : Nat}
    {es : List Expr} (h : ExprArrayReprWithin m P a n es) :
    PointerArrayWithin m P (ExprReprWithin m P) a es := by
  pointer_array_view h es a n

/-- Parameter arrays expose the common owned pointer-array view. -/
theorem ParamsReprWithin.pointers {m : Mem} {P : Nat → Prop} {a n : Nat}
    {ps : List String} (h : ParamsReprWithin m P a n ps) :
    PointerArrayWithin m P (CStringWithin m P) a ps := by
  pointer_array_view h ps a n

#print axioms PointerArrayWithin.get
#print axioms StmtArrayReprWithin.pointers
#print axioms ExprArrayReprWithin.pointers
#print axioms ParamsReprWithin.pointers
end Vsa.MemRepr
