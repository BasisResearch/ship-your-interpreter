import Vsa.Sim.LogicalShortEntry
import Vsa.Sim.rows.TermRouting

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-- A falsy left result supplies the complete short-circuit AND execution. -/
theorem ScaffoldRows.field_hAndFalse (el er : Expr) (vl : Value) :
    Rows.AndFalseResid el er vl := by
  intro st d env st' hE hv hIH g N A SL phiF phiC sp r sret aEnv aExpr m0 c hc
  obtain ⟨aLeft, hx⟩ := hc.logicalShortExtras vl
  exact evalAndSim g N A SL phiF phiC st st' d env el er vl sp r sret aEnv aExpr
    aLeft m0 hv hIH (.andFalse st d env el er st' vl hE hv) c ⟨hc, hx⟩

/-- A truthy left result supplies the complete short-circuit OR execution. -/
theorem ScaffoldRows.field_hOrTrue (el er : Expr) (vl : Value) :
    Rows.OrTrueResid el er vl := by
  intro st d env st' hE hv hIH g N A SL phiF phiC sp r sret aEnv aExpr m0 c hc
  obtain ⟨aLeft, hx⟩ := hc.logicalShortExtras vl
  exact evalOrTrueSim g N A SL phiF phiC st st' d env el er vl sp r sret aEnv aExpr
    aLeft m0 hv hIH (.orTrue st d env el er st' vl hE hv) c ⟨hc, hx⟩

#print axioms ScaffoldRows.field_hAndFalse
#print axioms ScaffoldRows.field_hOrTrue
end Vsa.Sim
