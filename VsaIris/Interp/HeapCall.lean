import VsaIris.Interp.SpecEnv

/-!
# `malloc` in either regime

The interpreter's allocating sites call `malloc` from a `heapRes ρ H` (INTERP_DESIGN
§3): counted (total mode; `c` credits buy the block, never NULL) or uncounted
(partial mode; NULL is possible). `mallocRho_spec` is one spec for both, whose
result `mallocRes` is the pair of outcomes with NULL only uncounted. It is
built from H4's two specs (`AllocSpecs.counted`/`.uncounted`) by consequence, so
a site proves its continuation once for both regimes.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym

section Heap

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- `malloc(n)`'s outcome in regime `ρ`: NULL with the heap unchanged (only
uncounted), or a fresh 16-aligned block with the heap extended. -/
def mallocRes (ρ : Regime) (H : List (Nat × Nat)) (n : Nat) (p : BitVec 64) : IProp GF :=
  iprop((⌜p = 0#64 ∧ ρ = .uncounted⌝ ∗ heapRes vsaLayoutP vsaRoomB ρ H) ∨
    (⌜FreshBlock vsaLayoutP H p.toNat n ∧ p.toNat % 16 = 0⌝ ∗
      heapRes vsaLayoutP vsaRoomB ρ ((p.toNat, n) :: H) ∗ blockOwn p.toNat n))

/-- **`malloc` in regime `ρ`**, charged `c` credits when counted. -/
theorem mallocRho_spec (A : AllocSpecs live) (Wp : MachWP (GF := GF) (vsaModel live))
    (ρ : Regime) (H : List (Nat × Nat)) (n s : BitVec 64) (c : Nat) (hc : vsaChg n.toNat c)
    (saved : List (Nat × BitVec 64)) (hsv : saved.map Prod.fst = vsaSaved) :
    textOwn (GF := GF) allocText ⊢ fnSpecW Wp mallocEntryBV
      (fun r => iprop(⌜SpOKA s ∧ r.toNat % 4 = 0⌝ ∗ a0 ↦ᵣ n ∗ sp ↦ᵣ s ∗ gp ↦ᵣ□ gpV ∗
        clobbered vsaClob ∗ savedOwn saved ∗ stackScratch s allocHeadroom ∗
        heapRes vsaLayoutP vsaRoomB (ρ.plus c) H))
      (fun _ => iprop(∃ p, a0 ↦ᵣ p ∗ sp ↦ᵣ s ∗ clobbered vsaClob ∗ savedOwn saved ∗
        stackScratch s allocHeadroom ∗ mallocRes ρ H n.toNat p)) := by
  cases ρ with
  | counted k =>
    iintro #Ht
    ihave #Hs := A.counted.malloc Wp H n s k c saved hsv $$ Ht
    unfold mallocChgSpec fnSpecW
    imodintro
    iintro %r %Φ Hpc Hra ⟨%⟨hsp, hr⟩, Ha0, Hsp, #Hgp, Hcl, Hsv, Hstk, Hh⟩ Hk
    simp only [Regime.plus_counted, heapRes]
    iapply Hs $$ %r %Φ Hpc Hra [Ha0 Hsp Hcl Hsv Hstk Hh]
    · isplitr
      · ipureintro; exact ⟨hsp, hr, hc⟩
      iframe Ha0 Hsp Hgp Hcl Hsv Hstk Hh
    iintro Hpc Hra ⟨%p, Ha0, Hsp, Hcl, Hsv, Hstk, %hf, Hh, Hb⟩
    iapply Hk $$ Hpc Hra
    iexists p
    iframe Ha0 Hsp Hcl Hsv Hstk
    unfold mallocRes
    simp only [heapRes]
    iright
    iframe Hh Hb
    ipureintro; exact hf
  | uncounted =>
    iintro #Ht
    ihave #Hs := A.uncounted.malloc Wp H n s saved hsv $$ Ht
    unfold mallocSpec fnSpecW
    imodintro
    iintro %r %Φ Hpc Hra ⟨%⟨hsp, hr⟩, Ha0, Hsp, #Hgp, Hcl, Hsv, Hstk, Hh⟩ Hk
    simp only [Regime.plus_uncounted, heapRes]
    iapply Hs $$ %r %Φ Hpc Hra [Ha0 Hsp Hcl Hsv Hstk Hh]
    · isplitr
      · ipureintro; exact ⟨hsp, hr⟩
      iframe Ha0 Hsp Hgp Hcl Hsv Hstk Hh
    iintro Hpc Hra ⟨%p, Ha0, Hsp, Hcl, Hsv, Hstk, Hpost⟩
    iapply Hk $$ Hpc Hra
    iexists p
    iframe Ha0 Hsp Hcl Hsv Hstk
    unfold mallocRes mallocPost
    simp only [heapRes]
    icases Hpost with (⟨%h0, Hh⟩ | ⟨%hf, Hh, Hb⟩)
    · ileft
      iframe Hh
      ipureintro; exact ⟨h0, trivial⟩
    · iright
      iframe Hh Hb
      ipureintro; exact hf

end Heap

end VsaIris.Interp
