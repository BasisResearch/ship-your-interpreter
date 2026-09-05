import Vsa.Sim.rows.ErrorReachInhab

/-!
# Site-agnostic reach-to-error span composition

Only the generic span combinators survive here. The former constructor-specific
examples depended on the refuted fixed-route table.
-/

open Vsa.Machine (Config)
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- Compose a real arm span with its concrete `jal runtime_error` suffix. -/
theorem reachJal_of_span (S : ErrShared)
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    {SpanPre BlockPre : Config → Prop}
    (spanToBlock : Triple SpanPre BlockPre)
    (segToJal : Triple BlockPre
      (JalErrPre S.g S.inp S.m0 pcJal b0 b1 b2 b3))
    (c : Config) (hspan : SpanPre c) :
    ReachJal S.g S.inp S.m0 pcJal b0 b1 b2 b3 c :=
  (Triple.seq spanToBlock segToJal) c hspan

/-- The direct arm bridge is the identity-span instance. -/
theorem reachJal_of_armBranch_eq_span (S : ErrShared)
    (pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    {BlockPre : Config → Prop}
    (segToJal : Triple BlockPre
      (JalErrPre S.g S.inp S.m0 pcJal b0 b1 b2 b3))
    (c : Config) (hblock : BlockPre c) :
    reachJal_of_span S pcJal b0 b1 b2 b3 (Triple.rfl (P := BlockPre))
        segToJal c hblock =
      reachJal_of_armBranch S pcJal b0 b1 b2 b3 segToJal c hblock := by
  rfl

#print axioms reachJal_of_span
#print axioms reachJal_of_armBranch_eq_span

end Vsa.Sim
