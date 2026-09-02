import Vsa.Sim.rows.AssemblySkeleton
/-! CEGIS acceptance (a): the PRE-47i `NegResid` field-shape class, reconstructed
hermetically (git 2865529 form): a bare stack-headroom pin under ∀-`sp` with no
entry linkage.  The landed 47i cure was ENTRY-CONDITIONING — insert `EvalEntry`
(or a `StackOK` entry ground) as a leading hypothesis so the `sp=0` witness no
longer bites.  The cure generator's top-3 candidates for `AcceptNegPre` must
include an entry-conditioning transform. -/
open Vsa.Alloc (StackLayout StackOK)

namespace CegisAcceptA

/-- PRE-47i shape: `∀ SL sp, SL.lo + 3264 ≤ sp.toNat` (the `sproom` headroom
conjunct, ghost-∀ over the entry `sp`).  False at `sp = 0`. -/
def AcceptNegPre : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64), SL.lo + 3264 ≤ sp.toNat

end CegisAcceptA
