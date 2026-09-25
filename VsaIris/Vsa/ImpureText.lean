import VsaIris.Vsa.BinImg
import VsaIris.Interp.EnvCode
import VsaIris.Vsa.AllocCode

/-!
# The helpers' code lists from the binary's image

`envText` (`env.c`'s helpers) and `allocText` (the allocator) are the code
bytes their runs fetch plus `_impure_ptr`, which they load. Every entry is a
`.text` byte of the fixed image or a byte of `_impure_ptr` (one kernel
`decide` per list), so `binImg ∗ impureRO` gives both lists' `textOwn`, next
to `world`'s exclusive `Stdio.stdioOwn`.
-/

namespace VsaIris.Newlib

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris.Interp VsaIris.Stdio VsaIris.Sym

/-- A code-list entry is a `.text` byte of the image or a byte of `_impure_ptr`. -/
def TextOrImpure (p : Nat × BitVec 8) : Prop :=
  (textDom p.1 ∧ textByte p.1 = p.2) ∨ (impureW p.1 ∧ impureByte p.1 = p.2)

instance (p : Nat × BitVec 8) : Decidable (TextOrImpure p) := by
  unfold TextOrImpure; infer_instance

/-- The check, as a boolean fold (the kernel evaluates it without nesting
decidability proofs). -/
def textOrImpureAll (l : List (Nat × BitVec 8)) : Bool := l.all fun p => decide (TextOrImpure p)

theorem of_textOrImpureAll {l : List (Nat × BitVec 8)} (h : textOrImpureAll l = true) :
    ∀ p ∈ l, TextOrImpure p := by
  intro p hp
  unfold textOrImpureAll at h
  exact of_decide_eq_true (List.all_eq_true.mp h p hp)

theorem envText_ok : ∀ p ∈ envText, TextOrImpure p :=
  of_textOrImpureAll (by decide +kernel)

theorem allocText_ok : ∀ p ∈ allocText, TextOrImpure p :=
  of_textOrImpureAll (by decide +kernel)

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- A code list of `.text` and `_impure_ptr` bytes, from the image and `impureRO`. -/
theorem textOwn_of_textOrImpure :
    ∀ {l : List (Nat × BitVec 8)}, (∀ p ∈ l, TextOrImpure p) →
      binImg (GF := GF) ∗ impureRO ⊢ textOwn l
  | [], _ => by
    unfold textOwn
    iintro _
    simp only [sepL_nil]
    iempintro
  | p :: l, h => by
    have ih := textOwn_of_textOrImpure (l := l) (fun q hq => h q (.tail _ hq))
    unfold textOwn at ih ⊢
    simp only [sepL_cons]
    iintro #H
    isplitl []
    · unfold binImg impureRO roImg
      icases H with ⟨⟨#Ht, -⟩, #Hi⟩
      rcases h p (.head _) with ⟨hd, hb⟩ | ⟨hd, hb⟩
      · rw [← hb]; iapply Ht $$ %p.1 %hd
      · rw [← hb]; iapply Hi $$ %p.1 %hd
    · iapply ih $$ H

/-- **`env.c`'s code list** from the image and `_impure_ptr`. -/
theorem textOwn_envText : binImg (GF := GF) ∗ impureRO ⊢ textOwn envText :=
  textOwn_of_textOrImpure envText_ok

/-- **The allocator's code list** from the image and `_impure_ptr`. -/
theorem textOwn_allocText : binImg (GF := GF) ∗ impureRO ⊢ textOwn allocText :=
  textOwn_of_textOrImpure allocText_ok

end

end VsaIris.Newlib
