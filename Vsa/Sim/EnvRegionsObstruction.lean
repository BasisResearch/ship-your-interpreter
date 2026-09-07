import Vsa.Sim.EnvNewSpec

namespace Vsa.Sim

/-- Fresh-result geometry cannot be required for every natural pointer. -/
theorem envRegions_not_total (SL : Vsa.Alloc.StackLayout)
    (privFoot : Nat → Prop) (entry_sp : Nat) :
    ¬ (∀ p : Nat, EnvRegions SL privFoot entry_sp p) := by
  intro h
  have hzero := (h 0).frame_lo
  omega

#print axioms envRegions_not_total
end Vsa.Sim
