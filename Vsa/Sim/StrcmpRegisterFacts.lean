import Vsa.Sim.StrcmpSpec

open LeanRV64DExecutable

namespace Vsa.Sim

/-- A register preserved by strcmp differs from the argument register x11. -/
theorem NotWrittenStrcmp.x11 {R : Register} (h : NotWrittenStrcmp R) :
    (Register.x11 == R) = false := by
  obtain ⟨_, _, _, _, x11, _⟩ := h
  exact x11

#print axioms NotWrittenStrcmp.x11

end Vsa.Sim
