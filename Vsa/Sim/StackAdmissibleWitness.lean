import Vsa.Sim.LayoutInstance
import Vsa.While.Programs
import Vsa.While.Validation

/-!
# Satisfiability of `ProgramStackFits` at the validation programs

The Q1 boundary field `InterpRunReadyFacts.stack_admissible` is not vacuous:
every `c/tests/*.wl` program (`Vsa.While.Programs`) and the small recursion
witness of `Vsa.While.Validation` fits the stack. Each proof is one kernel
`decide` of the checker `programStackFits` over the concrete AST. The control
program's instance is `NativeNameAudit.Control.readyFacts`.
-/

namespace Vsa.Sim.LayoutInstance

open Vsa.While Vsa.While.Programs

theorem whileWl_stackFits : ProgramStackFits whileWl := .of_check (by decide)
theorem arithmeticWl_stackFits : ProgramStackFits arithmeticWl := .of_check (by decide)
theorem forWl_stackFits : ProgramStackFits forWl := .of_check (by decide)
theorem functionsWl_stackFits : ProgramStackFits functionsWl := .of_check (by decide)
theorem recursionWl_stackFits : ProgramStackFits recursionWl := .of_check (by decide)
theorem scopeWl_stackFits : ProgramStackFits scopeWl := .of_check (by decide)
theorem stringsWl_stackFits : ProgramStackFits stringsWl := .of_check (by decide)
theorem recursionSmall_stackFits : ProgramStackFits Validation.recursionSmall := .of_check (by decide)

/-- Every program of the validation list fits. -/
theorem all_stackFits : ∀ q ∈ Programs.all, ProgramStackFits q.2 := by
  intro q hq
  exact .of_check (by revert q; decide)

#print axioms whileWl_stackFits
#print axioms all_stackFits
#print axioms recursionSmall_stackFits

end Vsa.Sim.LayoutInstance
