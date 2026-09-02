import Vsa.Sim.EvalSimCommon
open Vsa.MemRepr Vsa.Alloc Vsa.Sim

/-!
Live cegis-cure interlock target: the int/eq arm extras as an explicit ∧-tower
(so the candidate enumerator forms conjunct-deletion candidates).  Running
`cegis_cure.py --demands "∃ w, mcall[x13slot]? = some w"` MUST drop the
x13-deletion candidate via the INTERLOCK filter (blockB_binary spills a3), while
the per-statement Z3/semantic filters would pass it (a weaker Prop has no
countermodel of its own).  Analysis only; NOT part of the build.
-/

namespace LiveExtras

def ExtrasTower : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64) (m0 mcall : Mem) (slotAddr x13slot : Nat),
    SL.lo + 4352 ≤ sp.toNat ∧
    (∃ b, m0[slotAddr]? = some b) ∧
    (∀ a : Nat, sp.toNat - 1120 ≤ a → a < sp.toNat → (∃ b, mcall[a]? = some b)) ∧
    (∃ w, mcall[x13slot]? = some w)

end LiveExtras
