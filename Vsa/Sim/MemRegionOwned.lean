import Vsa.MemReprWithin
import Vsa.Sim.MemRegion

namespace Vsa.MemRepr
open Vsa.Sim Vsa.While

local macro "transport_region_owned" rec:ident m:ident next:ident lo:ident hi:ident
    repr:ident reads:ident : tactic =>
  `(tactic| (
    apply $rec
      (motive_1 := fun a e _ => ExprIn $m $lo $hi a e → ExprIn $next $lo $hi a e)
      (motive_2 := fun a _ es _ => ExprsIn $m $lo $hi a es → ExprsIn $next $lo $hi a es)
      (motive_3 := fun a _ xs _ => ParamsIn $m $lo $hi a xs → ParamsIn $next $lo $hi a xs)
      (motive_4 := fun a s _ => StmtIn $m $lo $hi a s → StmtIn $next $lo $hi a s)
      (motive_5 := fun a s _ => OptStmtIn $m $lo $hi a s → OptStmtIn $next $lo $hi a s)
      (motive_6 := fun a e _ => OptExprIn $m $lo $hi a e → OptExprIn $next $lo $hi a e)
      (motive_7 := fun a _ ss _ => StmtsIn $m $lo $hi a ss → StmtsIn $next $lo $hi a ss)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ $repr
    all_goals
      intros
      simp_all [ExprIn, ExprsIn, ParamsIn, StmtIn, OptStmtIn, OptExprIn, StmtsIn, ($reads)]
  ))

/-- Hereditary expression bounds survive agreement on the represented reads. -/
theorem ExprReprWithin.transport_region {m m' : Mem} {P : Nat → Prop}
    {lo hi a : Nat} {e : Expr} (repr : ExprReprWithin m P a e)
    (agree : ∀ k, P k → m[k]? = m'[k]?) :
    ExprIn m lo hi a e → ExprIn m' lo hi a e := by
  have reads (p : Nat) (covered : Covers P p 8) : read64 m' p = read64 m p :=
    (covered.read64_eq agree).symm
  transport_region_owned ExprReprWithin.rec m m' lo hi repr reads

/-- Hereditary statement bounds survive agreement on the represented reads. -/
theorem StmtReprWithin.transport_region {m m' : Mem} {P : Nat → Prop}
    {lo hi a : Nat} {s : Stmt} (repr : StmtReprWithin m P a s)
    (agree : ∀ k, P k → m[k]? = m'[k]?) :
    StmtIn m lo hi a s → StmtIn m' lo hi a s := by
  have reads (p : Nat) (covered : Covers P p 8) : read64 m' p = read64 m p :=
    (covered.read64_eq agree).symm
  transport_region_owned StmtReprWithin.rec m m' lo hi repr reads

#print axioms ExprReprWithin.transport_region
#print axioms StmtReprWithin.transport_region
end Vsa.MemRepr
