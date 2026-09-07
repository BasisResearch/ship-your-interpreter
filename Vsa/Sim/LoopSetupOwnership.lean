import Vsa.Sim.LoopSetupData
import Vsa.Sim.InitialOwnershipPreservation

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While

namespace Vsa.Sim

/-- A reached setup endpoint with the original ownership ledger and represented state. -/
structure OwnedSetupFacts (inp : BitVec 64) (before after : Config) (endPC : BitVec 64)
    (stmts count : Nat) (p : Program) (N : NativeAddrs) (A : Arena)
    (phiF phiC : Addr → Nat) (D : RuntimeOwnership.InitialOwnershipData) : Prop extends
    ReadySegFacts inp before before after endPC,
    ReadyRuntimeFacts after stmts count p N A phiF phiC D where
  initial : RuntimeOwnership.InitialOwned before.σ.mem A LayoutInstance.stackSL
    phiF phiC stmts count D

/-- Either actual count-test branch preserves the represented program and initial store. -/
theorem readyCountTest_owned
    {c : Config} {stmts count : Nat} {inp : BitVec 64} {p : Program}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A phiF phiC aLeft)
    (hp : ProgramRepr c.σ.mem stmts count p) (taken : Bool)
    (hbranch : decide (count = 0) = taken) :
    ∃ after D, OwnedSetupFacts inp c after
      (if taken then 0x80004514#64 else 0x80004438#64) stmts count p N A phiF phiC D := by
  obtain ⟨D, O⟩ := F.ownership
  obtain ⟨after, J⟩ := (readyCountTest_closed F taken hbranch).facts
  exact ⟨after, D, J, J.preservation.toReadyPrefixFacts.runtime_owned F hp O, O⟩

/-- The empty entry case is discharged in the interpreter initial-route bundle.
The nonempty loop-head drive remains its separate supplier. -/
theorem interpInitRouteInputs_of_loaded
    (hDrive : DriveToLoopHead LayoutInstance.interpRunLayout) :
    InterpInitRouteInputs LayoutInstance.interpRunLayout :=
  interpInitRouteInputs_of_driveToLoopHead LayoutInstance.interpRunLayout
    entryEmptySpan_of_loaded hDrive

#print axioms readyCountTest_owned
#print axioms interpInitRouteInputs_of_loaded

end Vsa.Sim
