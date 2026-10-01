import VsaIris.Interp.CallMalloc

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.VsaHeap
open Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

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

abbrev freeL : List Nat := mallocL

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
  case hP => exact allocRegs_pre hsp hi4
  case hQ =>
    iintro ⟨H2, ⟨%q, H10⟩, Hcl, Hsv, HE⟩
    iapply allocRegs_post q (fun _ => iprop(stackScratch (R 2) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB ρ H)) $$ H10 H2 Hcl Hsv HE
  iframe Hspec Hcode Hms Hgp Hst Hh Hb
  iintro %f ⟨%⟨hf2, hfs⟩, Hst, Hres⟩ Hms
  iapply Hk $$ %(fun x => if x ∈ freeL then f x else R x) %(allocRegs_keep hf2 hfs) Hst Hres Hms

end

end VsaIris.Interp
