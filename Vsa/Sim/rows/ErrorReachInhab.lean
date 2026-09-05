import Vsa.Sim.rows.ErrorRouting

/-!
# Site-agnostic error reachability

This module retains only the valid, site-agnostic bridge from a machine segment
to `ReachJal`. The former `hNegType` example was retired because it named
`0x800034e4`, the assignment-unbound site, rather than `hNegType`'s actual
`0x80003b9c` site. Concrete semantic routes live in the leaf-only,
cause-indexed `ErrorRouting` interface.
-/

open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- A segment ending at a concrete error `jal`, applied to its actual entry
predicate, supplies the corresponding reachability witness. -/
theorem reachJal_of_armBranch (S : ErrShared)
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    {ArmBranchPre : Config → Prop}
    (seg : Triple ArmBranchPre
      (JalErrPre S.g S.inp S.m0 pcJal b0 b1 b2 b3))
    (c : Config) (harm : ArmBranchPre c) :
    ReachJal S.g S.inp S.m0 pcJal b0 b1 b2 b3 c :=
  seg c harm

#print axioms reachJal_of_armBranch

end Vsa.Sim
