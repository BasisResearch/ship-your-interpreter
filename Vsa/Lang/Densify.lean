import Vsa.Lang.Basic
import Vsa.Densify

/-! # The dense-memory form of the refinement conclusion

Headlines state loading on `fillZero c` (absent RAM bytes read as zero);
halting and divergence are invariant under `fillZero`. -/

namespace Vsa.Lang.Lang

open Vsa.Machine Vsa.Densify

variable {L : Lang} {p : L.Prog} {c : Config}

theorem Refines.of_fillZero (R : L.Refines p (fillZero c)) : L.Refines p c where
  halts e out ho := (R.halts e out ho).trans (halts_fillZero c out e).symm
  diverges hd := R.diverges ((diverges_fillZero c).1 hd)

theorem RefinesTotal.of_fillZero [L.Total] (R : L.RefinesTotal p (fillZero c)) :
    L.RefinesTotal p c where
  halts e out ho := (R.halts e out ho).trans (halts_fillZero c out e).symm
  diverges := R.diverges.trans (diverges_fillZero c).symm

end Vsa.Lang.Lang

namespace Vsa.Lang

open Vsa.Machine Vsa.Densify

/-- `OutSim.refinement` at the dense view of the configuration. -/
theorem OutSim.refinement_fillZero {P : Type} {S : P → String → Prop}
    {Loaded : P → Config → Prop} (H : OutSim S Loaded) :
    ∀ p c, Loaded p (fillZero c) →
      (∀ out, S p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, S p out) := by
  intro p c hL
  obtain ⟨h1, h2⟩ := H.refinement p (fillZero c) hL
  exact ⟨fun out => (h1 out).trans (halts_fillZero c out 0).symm,
    fun hd => h2 ((diverges_fillZero c).1 hd)⟩

end Vsa.Lang
