import Vsa.Sim.LogicalFallthroughEntry
import Vsa.Sim.rows.TermRouting

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-- Truthy AND composes the two actual child executions. -/
theorem ScaffoldRows.field_hAndTrue (st' st'' : Vsa.While.St)
    (el er : Expr) (vl vr : Value) : Rows.AndTrueResid st' st'' el er vl vr := by
  intro st d env hEl hv hEr hIHl hIHr g N A SL phiF phiC sp r sret aEnv aExpr m0 c hc
  obtain ⟨aLeft, aRight, hx⟩ := hc.logicalFallthroughExtras st'' vr hEl
  exact evalAndTrueSim g N A SL phiF phiC st st' st'' d env el er vl vr
    sp r sret aEnv aExpr aLeft aRight m0 hv hEl hIHl hIHr
    (.andTrue st d env el er st' st'' vl vr hEl hv hEr) c ⟨hc, hx⟩

/-- Falsy OR composes the two actual child executions. -/
theorem ScaffoldRows.field_hOrFalse (st' st'' : Vsa.While.St)
    (el er : Expr) (vl vr : Value) : Rows.OrFalseResid st' st'' el er vl vr := by
  intro st d env hEl hv hEr hIHl hIHr g N A SL phiF phiC sp r sret aEnv aExpr m0 c hc
  obtain ⟨aLeft, aRight, hx⟩ := hc.logicalFallthroughExtras st'' vr hEl
  exact evalOrFalseSim g N A SL phiF phiC st st' st'' d env el er vl vr
    sp r sret aEnv aExpr aLeft aRight m0 hv hEl hIHl hIHr
    (.orFalse st d env el er st' st'' vl vr hEl hv hEr) c ⟨hc, hx⟩

#print axioms ScaffoldRows.field_hAndTrue
#print axioms ScaffoldRows.field_hOrFalse
end Vsa.Sim
