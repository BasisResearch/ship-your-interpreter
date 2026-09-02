import Vsa.Sim.rows.BinArmBridge
/-! CEGIS acceptance (c): the ∀-mcall PAIR — the presence half of the
NegResid/NotResid over-quant pair (17773c4^ form,
experiments/fleet/obstructions/UnaryLogicPresenceOverquant.lean).  `∀ mcall,
agree-off-[SL.lo,sp) → ∀ a, ∃ b, mcall[a]? = some b` demands TOTAL population of
every off-stack-agreeing memory — refuted by `mcall = ∅` at an in-window `a`.
The honest repair (wave 47i) is an ∃-STRUCTURED / AGREE-ON variant: bound the
demand to the actual read footprint and demand agreement ON that window (so the
adversary is excluded).  The cure generator's top-3 for `AcceptMcallPre` must
include a guard-repair (agree-on-W' / footprint-bounded ∃) transform. -/
open Vsa.MemRepr Vsa.Alloc Vsa.Sim Vsa.While
open LeanRV64DExecutable Sail Register

namespace CegisAcceptC

/-- PRE-47i presence-totality half: over-quantified ∀-mcall total presence. -/
def AcceptMcallPre : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 : Mem),
    ∀ mcall : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
      ∀ a : Nat, ∃ b, mcall[a]? = some b

end CegisAcceptC
