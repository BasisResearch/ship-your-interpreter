import VsaIris.Interp.CallMalloc

/-!
# `free` from a run, in either regime (lane E2)

`freeRho_spec` is H4's two `free` specs (`AllocSpecs.freeCounted`/`.uncounted`)
as one spec over `heapRes ρ`: the live block `(q, n)` at the head of the live
list goes back with its bytes, the credits stay. `ms_callFree` is
`ms_callRegs` against it, the twin of `ms_callMalloc`.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.VsaHeap
open Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- **`free(q)` in regime `ρ`**: the block `(q, n)` leaves the live list. -/
theorem freeRho_spec (A : AllocSpecs live) (Wp : MachWP (GF := GF) (vsaModel live))
    (ρ : Regime) (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64)
    (saved : List (Nat × BitVec 64)) (hsv : saved.map Prod.fst = vsaSaved) :
    textOwn (GF := GF) allocText ⊢ fnSpecW Wp freeEntryBV
      (fun r => iprop(⌜SpOKA s ∧ r.toNat % 4 = 0⌝ ∗ a0 ↦ᵣ q ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpV ∗
        clobbered vsaClob ∗ savedOwn saved ∗ stackScratch s allocHeadroom ∗
        heapRes vsaLayoutP vsaRoomB ρ ((q.toNat, n) :: H) ∗ blockOwn q.toNat n))
      (fun _ => iprop(sp ↦ᵣ s ∗ (∃ v, a0 ↦ᵣ v) ∗ clobbered vsaClob ∗ savedOwn saved ∗
        stackScratch s allocHeadroom ∗ heapRes vsaLayoutP vsaRoomB ρ H)) := by
  cases ρ with
  | counted k =>
    iintro #Ht
    ihave #Hs := A.freeCounted.free Wp H q n s k saved hsv $$ Ht
    unfold freeRoomSpec
    simp only [heapRes]
    iexact Hs
  | uncounted =>
    iintro #Ht
    ihave #Hs := A.uncounted.free Wp H q n s saved hsv $$ Ht
    unfold freeSpec
    simp only [heapRes]
    iexact Hs

/-- The registers a `free` call takes: those of a `malloc` call. -/
abbrev freeL : List Nat := mallocL

/-- **`free(R 10)` from a run** (`jal free` at `i`), regime `ρ`: the run
continues at `i + 4` with the callee-saved registers and `sp` kept and the
block `(R 10, n)` returned to the allocator. -/
theorem ms_callFree (A : AllocSpecs live) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code freeEntryBV)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) (ρ : Regime) (H : List (Nat × Nat)) (n : Nat)
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem} (hsp : SpOKA (R 2)) :
    textOwn allocText ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗
      stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB ρ (((R 10).toNat, n) :: H) ∗ blockOwn (R 10).toNat n ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗
        stackScratch (R 2) allocHeadroom -∗ heapRes vsaLayoutP vsaRoomB ρ H -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hat, #Hcode, Hms, Hst, Hh, Hb, Hk⟩
  ihave #Hgp := codeRes_gp $$ Hcode
  ihave #Hspec := freeRho_spec A Wp ρ H (R 10) n (R 2) (vsaSaved.map fun k => (k, R k))
    (by simp [vsaSaved]) $$ Hat
  iapply (ms_callRegs Wp hexec hcode (L := freeL) (K := [20, 21, 22, 23, 24, 25, 26, 27])
    (by decide)
    (P := fun r => iprop(⌜SpOKA (R 2) ∧ r.toNat % 4 = 0⌝ ∗ a0 ↦ᵣ R 10 ∗ sp ↦ᵣ R 2 ∗
      gp ↦ᵣ□ gpV ∗ clobbered vsaClob ∗ savedOwn (vsaSaved.map fun k => (k, R k)) ∗
      stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB ρ (((R 10).toNat, n) :: H) ∗ blockOwn (R 10).toNat n))
    (Q := fun _ => iprop(sp ↦ᵣ R 2 ∗ (∃ v, a0 ↦ᵣ v) ∗ clobbered vsaClob ∗
      savedOwn (vsaSaved.map fun k => (k, R k)) ∗ stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB ρ H))
    (X := iprop(gp ↦ᵣ□ Newlib.gpV ∗ stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB ρ (((R 10).toNat, n) :: H) ∗ blockOwn (R 10).toNat n))
    (Y := fun f => iprop(⌜f 2 = R 2 ∧ ∀ k ∈ vsaSaved, f k = R k⌝ ∗
      stackScratch (R 2) allocHeadroom ∗ heapRes vsaLayoutP vsaRoomB ρ H))
    (R := R) (S := S) (Mt := Mt) ?hP ?hQ)
  case hP =>
    simp only [freeL, mallocL, sepL_cons]
    iintro ⟨⟨H10, H2, Hcs⟩, #Hgp', Hst, Hh, Hb⟩
    ihave ⟨Hcl, Hsv⟩ := (sepL_append _ _ _).1 $$ Hcs
    unfold VsaIris.a0 VsaIris.sp savedOwn
    rw [show Newlib.gpV = MallocFast.gpV from rfl]
    iframe H10 H2 Hgp' Hst Hh Hb
    isplitl []
    · ipureintro; exact ⟨hsp, hi4⟩
    isplitl [Hcl]
    · iapply clobbered_of_fn vsaClob R $$ Hcl
    · rw [VsaIris.sepL_map]; iexact Hsv
  case hQ =>
    unfold VsaIris.a0 VsaIris.sp savedOwn
    iintro ⟨H2, ⟨%q, H10⟩, Hcl, Hsv, Hst, Hres⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn vsaClob (by decide) $$ Hcl
    iexists (fun y => if y = 10 then q else if y = 2 then R 2 else if y ∈ vsaSaved then R y else g y)
    simp only [freeL, mallocL, sepL_cons]
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
  iframe Hspec Hcode Hms Hgp Hst Hh Hb
  iintro %f ⟨%⟨hf2, hfs⟩, Hst, Hres⟩ Hms
  have hkeep : ∀ x ∈ fRegs, x ∉ callerSaved →
      (fun x => if x ∈ freeL then f x else R x) x = R x := by
    intro x hx hc
    by_cases hL : x ∈ freeL
    · simp only [hL, ite_true]
      by_cases h2 : x = 2
      · subst h2; exact hf2
      · have hs : x ∈ vsaSaved :=
          (show ∀ y ∈ freeL, y ∉ callerSaved → y ≠ 2 → y ∈ vsaSaved by decide) x hL hc h2
        exact hfs x hs
    · simp [hL]
  iapply Hk $$ %(fun x => if x ∈ freeL then f x else R x) %hkeep Hst Hres Hms

end

end VsaIris.Interp
