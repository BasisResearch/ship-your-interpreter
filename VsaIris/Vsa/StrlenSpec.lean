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

/-- **`strlen(p)` in continuation style, for either WP.** Entered at
`0x80006cf0` with the return address `r` and the string pointer `P`: the
continuation receives the PC at `r`, the length in `a0`, `ra` restored, the
five caller-saved registers at some values, and the owned slack bytes
unchanged. Everything else the caller owns is framed by the continuation.

`Ctx` names the side conditions: the read region's RAM/HTIF geometry, the
string's bytes (`StrBytes`: nonzero ASCII up to `len`, NUL at `len`), the
caller's return alignment, and liveness of everything the run reads. -/
theorem strlen_specW {Φ : Nat × String → IProp GF} (live : Nat → Prop)
    (Wp : MachWP (GF := GF) (vsaModel live)) {P r : BitVec 64} {len : Nat}
    {bv : Nat → BitVec 8} (ctx : Ctx live P r len bv) (v11 v12 v13 v14 v15 : BitVec 64) :
    instrAt codeBase strlenCode ∗ sepL (strText P.toNat len bv) (fun q => q.1 ↦ₘ□ q.2) ∗
      VsaIris.PC ↦ᵣ 0x80006cf0#64 ∗ (1 : Nat) ↦ᵣ r ∗ (10 : Nat) ↦ᵣ P ∗ (11 : Nat) ↦ᵣ v11 ∗
      (12 : Nat) ↦ᵣ v12 ∗ (13 : Nat) ↦ᵣ v13 ∗ (14 : Nat) ↦ᵣ v14 ∗ (15 : Nat) ↦ᵣ v15 ∗
      ownSet (slackSet P.toNat len) (fun a => a ↦ₘ bv a) ∗
      (VsaIris.PC ↦ᵣ r -∗ (1 : Nat) ↦ᵣ r -∗ (10 : Nat) ↦ᵣ BitVec.ofNat 64 len -∗
        clobbered [11, 12, 13, 14, 15] -∗
        ownSet (slackSet P.toNat len) (fun a => a ↦ₘ bv a) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hcode, #Hstr, Hpc, Hra, Ha0, H11, H12, H13, H14, H15, HS, Hk⟩
  iapply wp_localRunW Wp (ro := []) (text := strlenText P.toNat len bv)
    (rs := strlenRs) (S := slackSet P.toNat len) (Q := strlenQ r P.toNat len bv)
    (len + 28) (entryRegs P r v11 v12 v13 v14 v15) bv
    (strlenRun ctx (fun _ _ => rfl) ⟨rfl, rfl, rfl⟩)
  isplitl [Hcode Hstr]
  · unfold roOwn strlenText
    simp only [sepL_nil]
    isplitr
    · iempintro
    iapply (sepL_append _ _ _).2
    isplitl [Hcode]
    · rw [← instrAt_text]
      iexact Hcode
    · iexact Hstr
  isplitl [Hpc Hra Ha0 H11 H12 H13 H14 H15]
  · rw [entryRegs_sepL]
    iframe Hpc Hra Ha0 H11 H12 H13 H14 H15
  isplitl [HS]
  · iexact HS
  unfold runKontW
  iintro %rv' %mv' %hQ Hregs HS'
  ihave ⟨Hpc, Hra, Ha0, H11, H12, H13, H14, H15⟩ := postRegs_split rv' $$ Hregs
  ihave Hpc := reg_cast hQ.1 $$ Hpc
  ihave Hra := reg_cast hQ.2.1 $$ Hra
  ihave Ha0 := reg_cast hQ.2.2.1 $$ Ha0
  ihave HC := clobbered_five (GF := GF) (rv' 11) (rv' 12) (rv' 13) (rv' 14) (rv' 15)
    $$ [H11 H12 H13 H14 H15]
  · iframe H11 H12 H13 H14 H15
  ihave HS2 := ownSet_congr (fun a ha => by rw [hQ.2.2.2 a ha]) $$ HS'
  iapply Hk $$ Hpc Hra Ha0 HC HS2


/-- The total instance (`term_sim`'s direction). -/
theorem strlen_spec {Φ : Nat × String → IProp GF} (live : Nat → Prop)
    {P r : BitVec 64} {len : Nat} {bv : Nat → BitVec 8} (ctx : Ctx live P r len bv)
    (v11 v12 v13 v14 v15 : BitVec 64) :
    instrAt codeBase strlenCode ∗ sepL (strText P.toNat len bv) (fun q => q.1 ↦ₘ□ q.2) ∗
      VsaIris.PC ↦ᵣ 0x80006cf0#64 ∗ (1 : Nat) ↦ᵣ r ∗ (10 : Nat) ↦ᵣ P ∗ (11 : Nat) ↦ᵣ v11 ∗
      (12 : Nat) ↦ᵣ v12 ∗ (13 : Nat) ↦ᵣ v13 ∗ (14 : Nat) ↦ᵣ v14 ∗ (15 : Nat) ↦ᵣ v15 ∗
      ownSet (slackSet P.toNat len) (fun a => a ↦ₘ bv a) ∗
      (VsaIris.PC ↦ᵣ r -∗ (1 : Nat) ↦ᵣ r -∗ (10 : Nat) ↦ᵣ BitVec.ofNat 64 len -∗
        clobbered [11, 12, 13, 14, 15] -∗
        ownSet (slackSet P.toNat len) (fun a => a ↦ₘ bv a) -∗ mTWP (vsaModel live) Φ)
    ⊢ mTWP (vsaModel live) Φ :=
  strlen_specW live (twpW _) ctx v11 v12 v13 v14 v15

/-- The partial instance (`stuck_sim`'s direction), from the same proof. -/
theorem strlen_specP {Φ : Nat × String → IProp GF} (live : Nat → Prop)
    {P r : BitVec 64} {len : Nat} {bv : Nat → BitVec 8} (ctx : Ctx live P r len bv)
    (v11 v12 v13 v14 v15 : BitVec 64) :
    instrAt codeBase strlenCode ∗ sepL (strText P.toNat len bv) (fun q => q.1 ↦ₘ□ q.2) ∗
      VsaIris.PC ↦ᵣ 0x80006cf0#64 ∗ (1 : Nat) ↦ᵣ r ∗ (10 : Nat) ↦ᵣ P ∗ (11 : Nat) ↦ᵣ v11 ∗
      (12 : Nat) ↦ᵣ v12 ∗ (13 : Nat) ↦ᵣ v13 ∗ (14 : Nat) ↦ᵣ v14 ∗ (15 : Nat) ↦ᵣ v15 ∗
      ownSet (slackSet P.toNat len) (fun a => a ↦ₘ bv a) ∗
      (VsaIris.PC ↦ᵣ r -∗ (1 : Nat) ↦ᵣ r -∗ (10 : Nat) ↦ᵣ BitVec.ofNat 64 len -∗
        clobbered [11, 12, 13, 14, 15] -∗
        ownSet (slackSet P.toNat len) (fun a => a ↦ₘ bv a) -∗ mWP (vsaModel live) Φ)
    ⊢ mWP (vsaModel live) Φ :=
  strlen_specW live (wpW _) ctx v11 v12 v13 v14 v15

end Spec

#print axioms strlen_specW
#print axioms strlen_spec
#print axioms strlen_specP
#print axioms strlenRun

end VsaIris.Inst.Strlen
