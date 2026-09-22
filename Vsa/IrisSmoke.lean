import Iris.ProofMode
import Iris.Examples.ClosedProofs
import Vsa.Machine

/-! Toolchain smoke test: Iris and the machine relation coexist on one
toolchain. States one IProp entailment that mentions `Machine.Halts`. -/

open Iris Iris.BI

namespace Vsa.IrisSmoke

theorem sep_comm_halts {PROP : Type _} [BI PROP] (P : PROP)
    (c : Vsa.Machine.Config) (out : String) :
    P ∗ ⌜Vsa.Machine.Halts c out 0⌝ ⊢ ⌜Vsa.Machine.Halts c out 0⌝ ∗ P := by
  iintro ⟨HP, HH⟩
  isplitl [HH]
  · iexact HH
  · iexact HP

/-- The same entailment at a concrete `IProp`. -/
theorem sep_comm_halts_iprop (P : IProp Iris.Examples.ClosedProofs.GF)
    (c : Vsa.Machine.Config) (out : String) :
    P ∗ ⌜Vsa.Machine.Halts c out 0⌝ ⊢ ⌜Vsa.Machine.Halts c out 0⌝ ∗ P :=
  sep_comm_halts P c out

#print axioms sep_comm_halts_iprop

end Vsa.IrisSmoke
