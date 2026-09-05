import Vsa.Sim.ApproxArmResidGapAssembly

/-!
# Exact divergence-family supplier

`DivWork` replaces the aggregate `hDivCorr : DivCorrFamily L` field with the
three inputs used by the landed divergence assembly. No false fixed-PC or
vacuous correspondence is introduced.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (Config)
open Vsa.Refine (Layout)
open Vsa.While (Addr Stmt)

namespace Vsa.Sim

/-- The exact remaining inputs for the divergence correspondence family. -/
structure DivWork (L : Layout) where
  /-- Reflection of the active scope and remaining statement list at the
  interpreter loop head. -/
  Reflect : Config → Addr → List Stmt → Prop
  /-- Loaded-program drive to the reflected loop head. -/
  entry : Vsa.Sim.DivCorrClose.DivEntryDrive Reflect L
  /-- Normal statement iteration and loop-head re-entry. -/
  iter : Vsa.Sim.IterSeamAssembly.IterSeamResid Reflect
  /-- The complete 29-field approximate-dispatch staging assembly. -/
  arms : ArmStages Reflect

/-- Close `hDivCorr` exactly from `DivWork`. -/
theorem divCorrFamily_ofWork (L : Layout) (W : DivWork L) :
    Vsa.Sim.DivFamily.DivCorrFamily L :=
  divCorrFamily_of_armStages W.Reflect L W.entry W.iter W.arms

#print axioms divCorrFamily_ofWork

end Vsa.Sim
