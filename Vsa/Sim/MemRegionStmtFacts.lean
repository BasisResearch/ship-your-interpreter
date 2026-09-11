import Vsa.Sim.MemRegion

open Vsa.MemRepr Vsa.While

namespace Vsa.Sim

/-- The represented else pointer selects a child in the same region. -/
theorem stmtIn_if_else {m : Mem} {lo hi a p : Nat} {c : Expr} {t e : Stmt}
    (h : StmtIn m lo hi a (.ifStmt c t (some e)))
    (hp : read64 m (a + 24) = some p) : StmtIn m lo hi p e := by
  obtain ⟨_, _, _, _, child⟩ := h
  exact child p hp

/-- The represented for-loop body pointer selects a child in the same region. -/
theorem stmtIn_for_body {m : Mem} {lo hi a p : Nat}
    {oi : Option Stmt} {oc os : Option Expr} {body : Stmt}
    (h : StmtIn m lo hi a (.forStmt oi oc os body))
    (hp : read64 m (a + 32) = some p) : StmtIn m lo hi p body := by
  obtain ⟨_, _, _, _, child⟩ := h
  exact child p hp

#print axioms stmtIn_if_else
#print axioms stmtIn_for_body

end Vsa.Sim
