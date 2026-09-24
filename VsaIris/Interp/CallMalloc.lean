import VsaIris.Interp.CallRegs
import VsaIris.Interp.HeapCall

/-!
# `malloc` from a run, in either regime (lane H2)

`ms_callMalloc` is `ms_callRegs` against H1's `mallocRho_spec`: the run's
`a0` (the request), `sp`, the allocator's clobbered and saved registers go to
`malloc`; `sp` and the saved ones come back at their values, `a0` holds the
result, whose outcome is `mallocRes` (NULL only uncounted).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.VsaHeap
open Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The registers a `malloc` call takes: `a0`, `sp`, the clobbered and the
saved ones. -/
abbrev mallocL : List Nat := 10 :: 2 :: (vsaClob ++ vsaSaved)

/-- **`malloc(R 10)` from a run** (`jal malloc` at `i`), regime `ρ`, charged
`c`: the run continues at `i + 4` with the callee-saved registers and `sp`
kept, the result in `a0` and its outcome. -/
theorem ms_callMalloc (A : AllocSpecs live) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code mallocEntryBV)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) (ρ : Regime) (H : List (Nat × Nat)) (c : Nat)
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem}
    (hc : vsaChg (R 10).toNat c) (hsp : SpOKA (R 2)) :
    textOwn allocText ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗
      stackScratch (R 2) allocHeadroom ∗ heapRes vsaLayoutP vsaRoomB (ρ.plus c) H ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗
        stackScratch (R 2) allocHeadroom -∗ mallocRes ρ H (R 10).toNat (R' 10) -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hat, #Hcode, Hms, Hst, Hh, Hk⟩
  ihave #Hgp := codeRes_gp $$ Hcode
  ihave #Hspec := mallocRho_spec A Wp ρ H (R 10) (R 2) c hc (vsaSaved.map fun k => (k, R k))
    (by simp [vsaSaved]) $$ Hat
  iapply (ms_callRegs Wp hexec hcode (L := mallocL) (K := [20, 21, 22, 23, 24, 25, 26, 27])
    (by decide)
    (P := fun r => iprop(⌜SpOKA (R 2) ∧ r.toNat % 4 = 0⌝ ∗ a0 ↦ᵣ R 10 ∗ sp ↦ᵣ R 2 ∗ gp ↦ᵣ□ gpV ∗
      clobbered vsaClob ∗ savedOwn (vsaSaved.map fun k => (k, R k)) ∗
      stackScratch (R 2) allocHeadroom ∗ heapRes vsaLayoutP vsaRoomB (ρ.plus c) H))
    (Q := fun _ => iprop(∃ q, a0 ↦ᵣ q ∗ sp ↦ᵣ R 2 ∗ clobbered vsaClob ∗
      savedOwn (vsaSaved.map fun k => (k, R k)) ∗ stackScratch (R 2) allocHeadroom ∗
      mallocRes ρ H (R 10).toNat q))
    (X := iprop(gp ↦ᵣ□ Newlib.gpV ∗ stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB (ρ.plus c) H))
    (Y := fun f => iprop(⌜f 2 = R 2 ∧ ∀ k ∈ vsaSaved, f k = R k⌝ ∗
      stackScratch (R 2) allocHeadroom ∗ mallocRes ρ H (R 10).toNat (f 10)))
    (R := R) (S := S) (Mt := Mt) ?hP ?hQ)
  case hP =>
    simp only [mallocL, sepL_cons]
    iintro ⟨⟨H10, H2, Hcs⟩, #Hgp', Hst, Hh⟩
    ihave ⟨Hcl, Hsv⟩ := (sepL_append _ _ _).1 $$ Hcs
    unfold VsaIris.a0 VsaIris.sp savedOwn
    rw [show Newlib.gpV = MallocFast.gpV from rfl]
    iframe H10 H2 Hgp' Hst Hh
    isplitl []
    · ipureintro; exact ⟨hsp, hi4⟩
    isplitl [Hcl]
    · iapply clobbered_of_fn vsaClob R $$ Hcl
    · rw [VsaIris.sepL_map]; iexact Hsv
  case hQ =>
    unfold VsaIris.a0 VsaIris.sp savedOwn
    iintro ⟨%q, H10, H2, Hcl, Hsv, Hst, Hres⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn vsaClob (by decide) $$ Hcl
    iexists (fun y => if y = 10 then q else if y = 2 then R 2 else if y ∈ vsaSaved then R y else g y)
    simp only [mallocL, sepL_cons]
    rw [VsaIris.sepL_map] at *
    have eCl : sepL (GF := GF) vsaClob (fun y => y ↦ᵣ (if y = 10 then q else if y = 2 then R 2
        else if y ∈ vsaSaved then R y else g y)) = sepL vsaClob (fun y => y ↦ᵣ g y) :=
      sepL_congr fun y hy => by
        obtain ⟨h10, h2, hs⟩ := (show ∀ y ∈ vsaClob, y ≠ 10 ∧ y ≠ 2 ∧ y ∉ vsaSaved by decide) y hy
        simp [h10, h2, hs]
    have eSv : sepL (GF := GF) vsaSaved (fun y => y ↦ᵣ (if y = 10 then q else if y = 2 then R 2
        else if y ∈ vsaSaved then R y else g y)) = sepL vsaSaved (fun y => y ↦ᵣ R y) :=
      sepL_congr fun y hy => by
        obtain ⟨h10, h2⟩ := (show ∀ y ∈ vsaSaved, y ≠ 10 ∧ y ≠ 2 by decide) y hy
        simp [h10, h2, hy]
    simp only [ite_true, show (2 : Nat) ≠ 10 from by decide, ite_false]
    isplitl [H10 H2 Hcl Hsv]
    · iframe H10 H2
      iapply (sepL_append _ _ _).2
      rw [eCl, eSv]
      iframe Hcl Hsv
    iframe Hst Hres
    ipureintro
    refine ⟨trivial, fun k hk => ?_⟩
    obtain ⟨h10, h2⟩ := (show ∀ y ∈ vsaSaved, y ≠ 10 ∧ y ≠ 2 by decide) k hk
    simp [h10, h2, hk]
  iframe Hspec Hcode Hms Hgp Hst Hh
  iintro %f ⟨%⟨hf2, hfs⟩, Hst, Hres⟩ Hms
  have hkeep : ∀ x ∈ fRegs, x ∉ callerSaved →
      (fun x => if x ∈ mallocL then f x else R x) x = R x := by
    intro x hx hc
    by_cases hL : x ∈ mallocL
    · simp only [hL, ite_true]
      by_cases h2 : x = 2
      · subst h2; exact hf2
      · have hs : x ∈ vsaSaved :=
          (show ∀ y ∈ mallocL, y ∉ callerSaved → y ≠ 2 → y ∈ vsaSaved by decide) x hL hc h2
        exact hfs x hs
    · simp [hL]
  have e10 : (fun x => if x ∈ mallocL then f x else R x) 10 = f 10 := by
    simp only [show (10 : Nat) ∈ mallocL from by decide, ite_true]
  rw [← e10] at *
  iapply Hk $$ %(fun x => if x ∈ mallocL then f x else R x) %hkeep Hst Hres Hms

end

end VsaIris.Interp
