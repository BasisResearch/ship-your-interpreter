import Vsa.Alloc
open Vsa.Alloc (StackLayout)
namespace SmtAcc
def HeadroomBad : Prop :=
  ∀ (SL : StackLayout) (sp : BitVec 64), SL.lo + 3264 ≤ sp.toNat
end SmtAcc


namespace SmtReplay
set_option maxHeartbeats 1000000 in
theorem refuted : ¬ SmtAcc.HeadroomBad := by
  intro H
  have h := H ⟨18446744073709548352, 0⟩ (18446744073709551615#64)
  simp only [SmtAcc.HeadroomBad] at h
  revert h
  decide
#print axioms refuted
end SmtReplay
