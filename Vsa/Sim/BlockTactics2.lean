import Vsa.Sim.InterpEntry
import Vsa.Sim.BlockDecode
import Vsa.Sim.BlockTactics
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch04Part07
import Vsa.Sim.DecodeTable.Batch09Part03
import Vsa.Sim.DecodeTable.Batch09Part05
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part24
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch09Part31
import Vsa.Sim.DecodeTable.Batch10Part09
import Vsa.Sim.DecodeTable.Batch11Part11
import Vsa.Sim.DecodeTable.Batch11Part21
import Vsa.Sim.DecodeTable.Batch13Part26
import Vsa.Sim.DecodeTable.Batch15Part07
import Vsa.Sim.RamReadPins

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
