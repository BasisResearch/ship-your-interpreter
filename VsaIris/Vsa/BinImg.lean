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

/-- The code bytes the binary fetches are present. -/
def CodeLive (live : Nat → Prop) : Prop := ∀ a, textDom a → live a

/-- `code` is the image's `.text` at `i`: decided per site. -/
def TextAt (i : Nat) (code : List (BitVec 8)) : Prop :=
  ∀ p ∈ code.zipIdx, textDom (i + p.2) ∧ textByte (i + p.2) = p.1

instance (i : Nat) (code : List (BitVec 8)) : Decidable (TextAt i code) := by
  unfold TextAt; infer_instance

theorem codeFoot_mem {i : Nat} {code : List (BitVec 8)} {b : BitVec 8} {k : Nat}
    (h : (b, k) ∈ code.zipIdx) : (i + k, Iris.DFrac.discard, b) ∈ codeFoot i code :=
  List.mem_map_of_mem (f := fun p => (i + p.2, Iris.DFrac.discard, p.1)) h

/-- The code bytes of a footprint, by index (`code_present` gives the
footprint form). -/
theorem loaded_of_foot {m : Std.ExtHashMap Nat (BitVec 8)} {i : Nat} {code : List (BitVec 8)}
    (h : ∀ p ∈ codeFoot i code, m[p.1]? = some p.2.2) :
    ∀ k, k < code.length → m[i + k]? = some (code.getD k 0) := by
  intro k hk
  have hm : (code[k], k) ∈ code.zipIdx := by
    rw [List.mem_iff_getElem]
    exact ⟨k, by simpa using hk, by simp⟩
  have := h _ (codeFoot_mem (i := i) hm)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  exact this

/-- Code taken from the image is present in every state of a `CodeLive` run. -/
theorem TextAt.live {live : Nat → Prop} (hl : CodeLive live) {i : Nat} {code : List (BitVec 8)}
    (h : TextAt i code) : ∀ p ∈ codeFoot i code, live p.1 := by
  intro p hp
  unfold codeFoot at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  exact hl _ (h q hq).1

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

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

theorem roImg_congr {S : Nat → Prop} {f g : Nat → BitVec 8} (h : ∀ a, S a → f a = g a) :
    roImg (GF := GF) S f ⊢ roImg S g := by
  unfold roImg
  iintro #H
  imodintro
  iintro %k %hk
  rw [← h k hk]
  iapply H $$ %k %hk

theorem binImg_rodata : binImg (GF := GF) ⊢ roImg rodataDom rodataByte := by
  unfold binImg; iintro ⟨-, #H⟩; iexact H

/-- Read-only bytes of a view as a segment's read footprint. -/
theorem roImg_foot (S : Nat → Prop) (img : Nat → BitVec 8) :
    ∀ l : List Nat, (∀ a ∈ l, S a) →
      roImg (GF := GF) S img ⊢
        sepL (l.map (fun a => (a, Iris.DFrac.discard, img a))) (fun p => p.1 ↦ₘ{p.2.1} p.2.2)
  | [], _ => by iintro _; simp only [List.map_nil, sepL_nil]; iempintro
  | a :: l, h => by
    simp only [List.map_cons, sepL_cons]
    iintro #H
    isplitl
    · unfold roImg
      iapply H $$ %a %(h a List.mem_cons_self)
    · iapply roImg_foot S img l (fun b hb => h b (List.mem_cons_of_mem _ hb)) $$ H

/-- **Code from the image.** -/
theorem instrAt_of_binImg {i : Nat} {code : List (BitVec 8)} (h : TextAt i code) :
    binImg (GF := GF) ⊢ instrAt i code := by
  unfold binImg instrAt
  iintro ⟨#H, -⟩
  iapply roImg_sepL textDom textByte code.zipIdx (fun k => i + k) h $$ H

/-- One image byte, read-only. -/
theorem binImg_byte {a : Nat} {b : BitVec 8}
    (h : (textDom a ∧ textByte a = b) ∨ (rodataDom a ∧ rodataByte a = b)) :
    binImg (GF := GF) ⊢ a ↦ₘ□ b := by
  unfold binImg roImg
  iintro ⟨#Ht, #Hr⟩
  rcases h with ⟨hd, rfl⟩ | ⟨hd, rfl⟩
  · iapply Ht $$ %a %hd
  · iapply Hr $$ %a %hd

/-- A list of image bytes, read-only. -/
theorem binImg_sepL :
    ∀ l : List (Nat × BitVec 8),
      (∀ p ∈ l, (textDom p.1 ∧ textByte p.1 = p.2) ∨ (rodataDom p.1 ∧ rodataByte p.1 = p.2)) →
      binImg (GF := GF) ⊢ sepL l (fun p => p.1 ↦ₘ□ p.2)
  | [], _ => by iintro _; simp only [sepL_nil]; iempintro
  | q :: l, h => by
    simp only [sepL_cons]
    iintro #H
    isplitl
    · iapply binImg_byte (h q List.mem_cons_self) $$ H
    · iapply binImg_sepL l (fun p hp => h p (List.mem_cons_of_mem _ hp)) $$ H

end

end VsaIris.Newlib
