import Vsa.Sim.EvalNotSim
import Vsa.Sim.rows.TermRouting

open LeanRV64DExecutable Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc

namespace Vsa.Sim

/-- Logical-not uses the actual child execution and retained entry code support. -/
theorem ScaffoldRows.field_hNot (esub : Expr) (vsub : Value) :
    Rows.NotResid esub vsub := by
  intro st d env st' hE hIH g N A SL phiF phiC sp r sret aEnv aExpr m0 c hc
  obtain ⟨aOperand, hx⟩ := hc.notExtras
  exact evalNotSim g N A SL phiF phiC st st' d env esub vsub sp r sret aEnv aExpr
    aOperand m0 hIH (.not st d env esub st' vsub hE) c ⟨hc, hx⟩

#print axioms ScaffoldRows.field_hNot
end Vsa.Sim
