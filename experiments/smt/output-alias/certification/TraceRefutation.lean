import Vsa.Sim.OutputAliasLoaded
import Vsa.Sim.EndToEnd

/-! Conditional refutation of the historical physical boundary.

Every result below requires an actual `Halts snapshotConfig "\n\n" 0`
proof. This file supplies no machine trace and does not discharge that premise.
The Loaded witness and the one-newline source behavior are already closed.
-/

namespace Vsa.Sim.OutputAliasLoaded

open Vsa.Machine Vsa.Refine Vsa.While
open Vsa.Sim.LayoutInstance
open Vsa.While.LoadedOutputAlias

/-- The hypothesized two-newline halt excludes the specified one-newline halt. -/
theorem snapshot_not_source_halt_of_alias_halt
    (hm : Halts snapshotConfig "\n\n" 0) :
    ¬ Halts snapshotConfig "\n" 0 := by
  intro hs
  exact (by decide : "\n\n" ≠ "\n") (hm.deterministic hs).1

/-- Conditional failure of the historical layout's universal forward simulation. -/
theorem not_interpSim_of_alias_halt
    (hm : Halts snapshotConfig "\n\n" 0) :
    ¬ InterpSim BeforeAstOwnership.interpRunLayout := by
  intro H
  exact snapshot_not_source_halt_of_alias_halt hm
    (H.term_sim program snapshotConfig "\n" snapshot_loaded program_bigStep)

/-- Conditional impossibility of supplying the exact end-to-end work record. -/
theorem not_remainingWork_of_alias_halt
    (hm : Halts snapshotConfig "\n\n" 0) :
    (EndToEnd.RemainingWork BeforeAstOwnership.interpRunLayout → False) := by
  intro W
  exact not_interpSim_of_alias_halt hm (EndToEnd.interpSim_ofWork W)

/-- Negates the behavioral correspondence under the historical boundary. -/
theorem not_behavioralCorrespondence_of_alias_halt
    (hm : Halts snapshotConfig "\n\n" 0) :
    ¬ (∀ p c, Loaded BeforeAstOwnership.interpRunLayout p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out)) := by
  intro H
  exact snapshot_not_source_halt_of_alias_halt hm
    (((H program snapshotConfig snapshot_loaded).1 "\n").mp program_bigStep)

#print axioms snapshot_not_source_halt_of_alias_halt
#print axioms not_interpSim_of_alias_halt
#print axioms not_remainingWork_of_alias_halt
#print axioms not_behavioralCorrespondence_of_alias_halt

end Vsa.Sim.OutputAliasLoaded
