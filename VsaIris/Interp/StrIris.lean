import VsaIris.Interp.StrSteps
import VsaIris.Interp.SpecEnv
import VsaIris.Vsa.BinImg

/-!
# The string leaves' runs in the Iris logic

Shared plumbing between the `SW` runs (`StrRun.lean`) and the function
specs: the code from `binImg`, a persistent string's bytes as the run's data,
the run rule at a symbolic state (`wp_sw`), and the register marshalling of
`fnSpecW`'s `clobbered` lists into the owned list `sRegs`.
-/

namespace VsaIris.Interp.StrLeaf

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Inst.Strlen VsaIris.Newlib
open Vsa.Sim Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]
variable {live : Nat → Prop}

/-- A C string image gives the string's byte facts (as `ProofStringify`). -/
theorem strBytes_of_img {img : Nat → BitVec 8} {q : Nat} {x : String}
    (h : VsaIris.Interp.CStrImg img q x) : StrBytes q x.toList.length img where
  nonzero k hk := by
    obtain ⟨e, h1, h2⟩ := h.1 k hk
    rw [e]; intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
    simp at this; omega
  nul := h.2

/-- A string's window as `strlen`'s read geometry. -/
theorem regions_of_win {P : BitVec 64} {len : Nat} (h : VsaIris.Interp.StrWin P.toNat len) :
    ReadRegions P len := by
  have hlo := h.lo; have hhi := h.hi; have ht := h.htif
  refine ⟨hlo, hhi, by omega, ?_⟩
  have : tohostAddr = VsaIris.Interp.htifLo := rfl
  rcases ht with ht | ht
  · left; omega
  · right; omega

theorem pc_reg (v : BitVec 64) : VsaIris.PC ↦ᵣ v ⊣⊢@{IProp GF} (32 : Nat) ↦ᵣ v := .rfl
theorem ra_reg (v : BitVec 64) : VsaIris.ra ↦ᵣ v ⊣⊢@{IProp GF} (1 : Nat) ↦ᵣ v := .rfl

/-- The code of both leaves is live. -/
theorem strCode_live (hcl : CodeLive live) : ∀ p ∈ strCode, live p.1 := by
  intro p hp
  rcases List.mem_append.mp hp with hp | hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hcl _ (strlenCode_text q hq).1
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hcl _ (strcpyCode_text q hq).1

/-- The code of both leaves, from the binary's image. -/
theorem strCode_of_binImg : binImg (GF := GF) ⊢ sepL strCode (fun q => q.1 ↦ₘ□ q.2) := by
  iintro #H
  ihave #H1 := instrAt_of_binImg strlenCode_text $$ H
  ihave #H2 := instrAt_of_binImg strcpyCode_text $$ H
  unfold strCode
  iapply (sepL_append _ _ _).2
  rw [← instrAt_text, ← instrAt_text]
  iframe H1 H2

/-- Read-only bytes of an image as a list of persistent points-to. -/
theorem roImg_list (S : Nat → Prop) (img : Nat → BitVec 8) :
    ∀ l : List (Nat × BitVec 8), (∀ q ∈ l, S q.1 ∧ img q.1 = q.2) →
      VsaIris.Interp.roImg (GF := GF) S img ⊢ sepL l (fun q => q.1 ↦ₘ□ q.2)
  | [], _ => by iintro _; simp only [sepL_nil]; iempintro
  | q :: l, h => by
    simp only [sepL_cons]
    iintro #H
    isplitl
    · obtain ⟨hs, he⟩ := h q List.mem_cons_self
      unfold VsaIris.Interp.roImg
      rw [← he]
      iapply H $$ %q.1 %hs
    · iapply roImg_list S img l (fun p hp => h p (List.mem_cons_of_mem _ hp)) $$ H

theorem roImg_strText (p len : Nat) (img : Nat → BitVec 8) :
    VsaIris.Interp.roImg (GF := GF) (InExt (p, len + 1)) img ⊢
      sepL (strText p len img) (fun q => q.1 ↦ₘ□ q.2) :=
  roImg_list _ img _ fun q hq => by
    unfold strText at hq
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
    have := List.mem_range.mp hk
    exact ⟨⟨by simp, by simp; omega⟩, rfl⟩

/-- No bytes. -/
theorem ownSet_none (Φ : Nat → IProp GF) : ⊢ ownSet (fun _ => False) Φ := by
  unfold ownSet
  iexists []
  isplitr
  · ipureintro; exact ⟨List.nodup_nil, fun a => by simp⟩
  · simp only [sepL_nil]; iempintro

/-- **A string leaf's run at a symbolic state**, for either WP. -/
theorem wp_sw (Wp : MachWP (GF := GF) (vsaModel live)) {D : List (Nat × BitVec 8)}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {Φ : Nat × String → IProp GF}
    (h : SW live D S Q pc R Mt) (rv : Nat → BitVec 64) (hpc : rv 32 = pc)
    (hR : ∀ k ∈ sRegs, k ≠ 32 → rv k = R k) :
    roOwn (GF := GF) [] (strCode ++ D) ∗ sepL sRegs (fun k => k ↦ᵣ rv k) ∗
      ownSet S (fun a => a ↦ₘ imgM Mt a) ∗ runKontW Wp Φ sRegs S Q ⊢ Wp.W Φ := by
  obtain ⟨n, hn⟩ := h
  exact wp_localRunW Wp n rv (imgM Mt) (hn rv (imgM Mt) ⟨hpc, hR, fun _ _ => rfl⟩)

/-! ## Registers -/

/-- The argument registers `fnSpecW`'s clobber lists leave to the leaf. -/
abbrev leafTemps : List Nat := [11, 12, 13, 14, 15, 16]
abbrev retRest : List Nat := [5, 6, 7, 17, 28, 29, 30, 31]

theorem retClob_perm : VsaIris.Interp.retClob.Perm (leafTemps ++ retRest) := by decide
theorem argClob12_perm : (12 :: VsaIris.Interp.argClob).Perm ([12, 13, 14, 15, 16] ++ retRest) := by
  decide

theorem clobbered_split {l a b : List Nat} (h : l.Perm (a ++ b)) :
    clobbered (GF := GF) l ⊣⊢ clobbered a ∗ clobbered b := by
  unfold clobbered
  exact (sepL_perm _ h).trans (sepL_append _ _ _)

/-- The register file of a leaf's entry. -/
def entryRv (e r a0 a1 : BitVec 64) (f : Nat → BitVec 64) (k : Nat) : BitVec 64 :=
  if k = 32 then e else if k = 1 then r else if k = 10 then a0 else if k = 11 then a1 else f k

theorem sRegs_in (e r a0 a1 : BitVec 64) (f : Nat → BitVec 64) :
    (32 : Nat) ↦ᵣ e ∗ (1 : Nat) ↦ᵣ r ∗ (10 : Nat) ↦ᵣ a0 ∗ (11 : Nat) ↦ᵣ a1 ∗
      sepL [12, 13, 14, 15, 16] (fun k => k ↦ᵣ f k) ⊢@{IProp GF}
      sepL sRegs (fun k => k ↦ᵣ entryRv e r a0 a1 f k) := by
  simp only [sepL_cons, sepL_nil, entryRv, ↓reduceIte, Nat.reduceEqDiff]
  iintro ⟨H32, H1, H10, H11, H12, H13, H14, H15, H16, _⟩
  iframe H32 H1 H10 H11 H12 H13 H14 H15 H16

theorem sRegs_out (rv : Nat → BitVec 64) :
    sepL sRegs (fun k => k ↦ᵣ rv k) ⊢@{IProp GF}
      (32 : Nat) ↦ᵣ rv 32 ∗ (1 : Nat) ↦ᵣ rv 1 ∗ (10 : Nat) ↦ᵣ rv 10 ∗
        sepL leafTemps (fun k => k ↦ᵣ rv k) := by
  simp only [sepL_cons, sepL_nil]
  iintro ⟨H32, H1, H10, H11, H12, H13, H14, H15, H16, _⟩
  iframe H32 H1 H10 H11 H12 H13 H14 H15 H16

theorem reg_eq {k : Nat} {a b : BitVec 64} (h : a = b) : k ↦ᵣ a ⊢@{IProp GF} k ↦ᵣ b := by
  rw [h]

end

end VsaIris.Interp.StrLeaf
