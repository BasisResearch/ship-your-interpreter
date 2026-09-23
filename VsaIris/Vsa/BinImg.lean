import VsaIris.Interp.Repr
import VsaIris.Call
import Vsa.Sim.Code.FixedImage

/-!
# The binary's code image, persistent

`.text` and `.rodata` of the fixed ELF (`Vsa.Sim.Code.FixedTextLoaded`,
`FixedRodataLoaded`, which `InterpRunPhysicalFacts` supplies at the boundary)
as read-only points-to: `binImg`. A proof takes the bytes of the code it runs
from it with `instrAt_of_binImg`, whose side condition is one `decide` over
the image.
-/

namespace VsaIris.Newlib

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris.Interp

def textDom (a : Nat) : Prop := 0x80000000 ≤ a ∧ a < 0x80018be0
def rodataDom (a : Nat) : Prop := 0x80018be0 ≤ a ∧ a < 0x8001acf0

instance (a : Nat) : Decidable (textDom a) := by unfold textDom; infer_instance
instance (a : Nat) : Decidable (rodataDom a) := by unfold rodataDom; infer_instance

def textByte (a : Nat) : BitVec 8 := Vsa.Sim.Code.fixedTextByte (a - 0x80000000)
def rodataByte (a : Nat) : BitVec 8 := Vsa.Sim.Code.fixedRodataByte (a - 0x80018be0)

/-- The code bytes the binary fetches are present. -/
def CodeLive (live : Nat → Prop) : Prop := ∀ a, textDom a → live a

/-- `code` is the image's `.text` at `i`: decided per site. -/
def TextAt (i : Nat) (code : List (BitVec 8)) : Prop :=
  ∀ p ∈ code.zipIdx, textDom (i + p.2) ∧ textByte (i + p.2) = p.1

instance (i : Nat) (code : List (BitVec 8)) : Decidable (TextAt i code) := by
  unfold TextAt; infer_instance

/-- Code taken from the image is present in every state of a `CodeLive` run. -/
theorem TextAt.live {live : Nat → Prop} (hl : CodeLive live) {i : Nat} {code : List (BitVec 8)}
    (h : TextAt i code) : ∀ p ∈ codeFoot i code, live p.1 := by
  intro p hp
  unfold codeFoot at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hl _ (h q hq).1

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The binary's `.text` and `.rodata`, persistent. -/
def binImg : IProp GF := iprop(roImg textDom textByte ∗ roImg rodataDom rodataByte)

instance : Persistent (binImg (GF := GF)) := by unfold binImg; infer_instance

theorem roImg_sepL (S : Nat → Prop) (img : Nat → BitVec 8) :
    ∀ l : List (BitVec 8 × Nat) , ∀ (f : Nat → Nat), (∀ p ∈ l, S (f p.2) ∧ img (f p.2) = p.1) →
      roImg (GF := GF) S img ⊢ sepL l (fun p => f p.2 ↦ₘ□ p.1)
  | [], _, _ => by iintro _; simp only [sepL_nil]; iempintro
  | q :: l, f, h => by
    simp only [sepL_cons]
    iintro #H
    isplitl
    · obtain ⟨hs, he⟩ := h q List.mem_cons_self
      unfold roImg
      rw [← he]
      iapply H $$ %(f q.2) %hs
    · iapply roImg_sepL S img l f (fun p hp => h p (List.mem_cons_of_mem _ hp)) $$ H

/-- **Code from the image.** -/
theorem instrAt_of_binImg {i : Nat} {code : List (BitVec 8)} (h : TextAt i code) :
    binImg (GF := GF) ⊢ instrAt i code := by
  unfold binImg instrAt
  iintro ⟨#H, -⟩
  iapply roImg_sepL textDom textByte code.zipIdx (fun k => i + k) h $$ H

end

end VsaIris.Newlib
