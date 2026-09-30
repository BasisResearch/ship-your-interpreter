import Vsa.While.StackNeed
import Vsa.Sim.Code.Eval_expr
import Vsa.Sim.MemRegion
import Vsa.Sim.BlockDecode

open LeanRV64DExecutable Vsa
open Register
open Vsa.Alloc
open Lean Elab Tactic
open Lean.Parser.Tactic

namespace Vsa.Sim

theorem abiPreserved_ne {R X : Register} (hR : AbiPreserved R = true)
    (hX : AbiPreserved X = false) : (X == R) = false := by
  rcases hXR : (X == R) with _ | _
  · rfl
  · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)

end Vsa.Sim
