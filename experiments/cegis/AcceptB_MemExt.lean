import Vsa.Sim.rows.BinArmBridge
/-! CEGIS acceptance (b): the PRE-48f `BinArmExtras.mem_ext` conjunct, isolated
(mirrors experiments/fleet/obstructions/BinArmExtrasMemExtOverquant.lean, the
d7a5c91^ form).  The landed 48f cure was DELETION — the block output
`blockA_k`/`blockA_binaryArm` already produces `MemExtends m0 ment` intrinsically
(`_hpresM`), so this conjunct is REDUNDANT and was dropped.  The cure generator's
top-3 for `AcceptMemExtPre` must include a conjunct-DELETION transform (block
output supplies it). -/
open Vsa.MemRepr Vsa.Alloc Vsa.Sim Vsa.While
open LeanRV64DExecutable Sail Register

namespace CegisAcceptB

/-- PRE-48f shape: `mem_ext` packed as a top-level conjunct.  The first conjunct
is a genuinely-block-supplied fact (an inhabitable placeholder `True`); the
SECOND is the over-quantified `∀ m, agree-off-W → MemExtends m0 m` that 48f
dropped.  A whole-statement refutation targets the second. -/
def AcceptMemExtPre : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    True ∧
    (∀ m : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m[a]? = m0[a]?) →
      MemExtends m0 m)

end CegisAcceptB
