import VsaIris.Vsa.Strlen

/-!
# `strlen` in Iris, for either WP

INTERP_DESIGN.md §9, package H3. The whole function is one bounded
owned-footprint run (`Strlen.strlenRun`), so the Iris layer is ONE
`wp_localRunW` application (`VsaIris/LocalRun.lean`, the loop rule; xv6iris
`ProofMemset.v:1-9`, "bounded loop, not iLöb"). The spec is stated for an
abstract `Wp : MachWP`, so it serves both `term_sim` (total) and `stuck_sim`
(partial).

Ownership follows INTERP_DESIGN.md §3: the code and the string's bytes (the
characters and the NUL) are PERSISTENT, and the at most seven bytes past the
NUL that the word loop over-reads — they belong to the caller's heap block —
are owned and handed back unchanged.
-/

namespace VsaIris.Inst.Strlen

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config MState)
open Vsa.Sim Vsa.MemRepr

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- The eight registers `strlen` touches, at the entry. -/
def entryRegs (P r v11 v12 v13 v14 v15 : BitVec 64) : Nat → BitVec 64 := fun k =>
  if k = VsaIris.PC then 0x80006cf0#64
  else if k = 1 then r
  else if k = 10 then P
  else if k = 11 then v11
  else if k = 12 then v12
  else if k = 13 then v13
  else if k = 14 then v14
  else v15

theorem clobbered_five (a b c d e : BitVec 64) :
    (11 : Nat) ↦ᵣ a ∗ (12 : Nat) ↦ᵣ b ∗ (13 : Nat) ↦ᵣ c ∗ (14 : Nat) ↦ᵣ d ∗ (15 : Nat) ↦ᵣ e
    ⊢ clobbered (GF := GF) [11, 12, 13, 14, 15] := by
  unfold clobbered
  simp only [sepL_cons, sepL_nil]
  iintro ⟨H11, H12, H13, H14, H15⟩
  isplitl [H11]

  · iexists a; iexact H11
  isplitl [H12]
  · iexists b; iexact H12
  isplitl [H13]
  · iexists c; iexact H13
  isplitl [H14]
  · iexists d; iexact H14
  isplitl [H15]
  · iexists e; iexact H15
  · iempintro

theorem postRegs_split (rv : Nat → BitVec 64) :
    sepL (GF := GF) strlenRs (fun k => k ↦ᵣ rv k) ⊢
      iprop(VsaIris.PC ↦ᵣ rv VsaIris.PC ∗ (1 : Nat) ↦ᵣ rv 1 ∗ (10 : Nat) ↦ᵣ rv 10 ∗
        (11 : Nat) ↦ᵣ rv 11 ∗ (12 : Nat) ↦ᵣ rv 12 ∗ (13 : Nat) ↦ᵣ rv 13 ∗
        (14 : Nat) ↦ᵣ rv 14 ∗ (15 : Nat) ↦ᵣ rv 15) := by
  unfold strlenRs strlenRegs
  simp only [sepL_cons, sepL_nil]
  iintro ⟨A, B, C, D, E, F, G, H, -⟩
  iframe A B C D E F G H

theorem reg_cast {k : Nat} {a b : BitVec 64} (h : a = b) :
    k ↦ᵣ a ⊢@{IProp GF} k ↦ᵣ b := by rw [h]

theorem entryRegs_sepL (P r v11 v12 v13 v14 v15 : BitVec 64) :
    sepL (GF := GF) strlenRs (fun k => k ↦ᵣ entryRegs P r v11 v12 v13 v14 v15 k) =
      iprop(VsaIris.PC ↦ᵣ 0x80006cf0#64 ∗ (1 : Nat) ↦ᵣ r ∗ (10 : Nat) ↦ᵣ P ∗ (11 : Nat) ↦ᵣ v11 ∗
        (12 : Nat) ↦ᵣ v12 ∗ (13 : Nat) ↦ᵣ v13 ∗ (14 : Nat) ↦ᵣ v14 ∗ (15 : Nat) ↦ᵣ v15 ∗ emp) :=
  rfl

theorem sepL_mono_mem {α} : ∀ (l : List α) (f g : α → IProp GF), (∀ a ∈ l, f a ⊢ g a) →
    sepL l f ⊢ sepL l g
  | [], _, _, _ => .rfl
  | x :: xs, f, g, h => by
    rw [sepL_cons, sepL_cons]
    iintro ⟨Hx, Hxs⟩
    isplitl [Hx]
    · iapply h x List.mem_cons_self $$ Hx
    · iapply sepL_mono_mem xs f g (fun a ha => h a (.tail _ ha)) $$ Hxs

theorem ownSet_congr {S : Nat → Prop} {f g : Nat → IProp GF} (h : ∀ a, S a → f a = g a) :
    ownSet S f ⊢ ownSet S g := by
  unfold ownSet
  iintro ⟨%l, %⟨hnd, hmem⟩, Hl⟩
  iexists l
  isplitr
  · ipureintro; exact ⟨hnd, hmem⟩
  iapply sepL_mono_mem l f g (fun a ha => by rw [h a ((hmem a).1 ha)]) $$ Hl

end Spec

end VsaIris.Inst.Strlen
