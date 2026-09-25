import Vsa.Refinement
import Vsa.Sim.OutputAliasRun

/-! The historical physical boundary admits an incompatible execution. The admitted source
program prints one newline; its complete machine execution prints two. -/

open Vsa.Machine Vsa.Refine Vsa.While
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
#print axioms not_behavioralCorrespondence_of_alias_halt

open Vsa.Sim.LayoutInstance

theorem snapshot_not_interpSim : ¬ InterpSim BeforeAstOwnership.interpRunLayout :=
  not_interpSim_of_alias_halt snapshot_halts_twoLF

theorem snapshot_not_behavioralCorrespondence :
    ¬ (∀ p c, Loaded BeforeAstOwnership.interpRunLayout p c →
      (∀ out, BigStep p out ↔ Halts c out 0) ∧
      (Diverges c → ¬ ∃ out, BigStep p out)) :=
  not_behavioralCorrespondence_of_alias_halt snapshot_halts_twoLF

#print axioms snapshot_not_interpSim
#print axioms snapshot_not_behavioralCorrespondence

end Vsa.Sim.OutputAliasLoaded
