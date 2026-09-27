import Vsa.While.StackNeed

/-!
# Preservation of bounded closure bodies

Execution preserves `StoreBodiesBound`.  The proof follows the nine-way
mutual semantics recursor because expression evaluation, calls, statements,
and loop auxiliaries can invoke one another.
-/

namespace Vsa.While

private theorem Stmt.bodiesBound_if_then {P : Nat} {c : Expr} {t : Stmt}
    {e : Option Stmt} (h : (Stmt.ifStmt c t e).bodiesBound P = true) :
    t.bodiesBound P = true := by
  cases e <;> simp only [Stmt.bodiesBound, Bool.and_eq_true] at h
  · exact h.2
  · exact h.1.2

private theorem StoreBodiesBound.ifTrue {P : Nat} {s s' : Store}
    {c : Expr} {t : Stmt} {e : Option Stmt}
    (hc : c.bodiesBound P = true → StoreBodiesBound s' P)
    (ht : t.bodiesBound P = true → StoreBodiesBound s' P → StoreBodiesBound s P)
    (h : (Stmt.ifStmt c t e).bodiesBound P = true) : StoreBodiesBound s P :=
  ht (Stmt.bodiesBound_if_then h) (hc (by
    cases e <;> simp_all [Stmt.bodiesBound]))

end Vsa.While
