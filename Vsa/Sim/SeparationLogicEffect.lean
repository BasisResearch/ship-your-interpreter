import Vsa.Sim.SeparationLogicFrame
import Vsa.Sim.SegmentEffect

open Vsa.MemRepr Vsa.Machine

namespace Vsa.Sim

/-- An assertion survives any effect preserving its resource support. -/
theorem StableUnder.assertion {effect : FrameEffect}
    (P : SeparationLogic.Assertion) (r : SeparationLogic.Resource)
    (hs : ∀ k, r.support k → effect.mem k) :
    StableUnder effect (fun c => P c.σ.mem r) :=
  fun _ _ hp hf => P.stable (fun k hk => (hf.mem k (hs k hk)).symm) hp

/-- Local write exclusion supplies assertion stability through a resource split. -/
theorem StableUnder.separated {effect : FrameEffect}
    {left right whole : SeparationLogic.Resource}
    (hs : SeparationLogic.Split left right whole)
    (R : SeparationLogic.Assertion)
    (hw : ∀ k, ¬ left.write k → effect.mem k) :
    StableUnder effect (fun c => R c.σ.mem right) :=
  .assertion R right (fun k hk => hw k (hs.compatible.frame_readable hk))

namespace SeparationLogic

/-- Run once and carry every disjoint assertion to that same endpoint. -/
theorem FramedTriple.frame {effect : FrameEffect} {P Q : Config → Prop}
    {left right whole : Resource} (hs : Split left right whole)
    (h : Vsa.Sim.FramedTriple effect P Q) (R : Assertion)
    (hw : ∀ k, ¬ left.write k → effect.mem k) :
    Vsa.Sim.FramedTriple effect
      (fun c => P c ∧ R c.σ.mem right)
      (fun c => Q c ∧ R c.σ.mem right) :=
  h.carryStable (StableUnder.separated hs R hw)

end SeparationLogic

#print axioms StableUnder.assertion
#print axioms StableUnder.separated
#print axioms SeparationLogic.FramedTriple.frame

end Vsa.Sim
