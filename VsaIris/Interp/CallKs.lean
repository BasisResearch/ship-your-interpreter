import VsaIris.Interp.EnvScan

/-!
# A `jal` from a span's register file, generically

`wp_call_ks`: the registers `ra :: Ks` go to the callee, whose spec `P`/`Q`
the caller adapts from/to `regsOf Ks` (`hpre`, `hpost`); every other register
of the file comes back unchanged, `ra` at the return address. The
per-callee wrappers (`strlen`, `memcpy`, `realloc`) are instances.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Sym

section Call

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {live : Nat → Prop}

/-- **`jal` from a span**, for any callee spec. -/
theorem wp_call_ks (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64} {P Q : BitVec 64 → IProp GF}
    (hexec : JalExec (vsaModel live) i code entry) (Ks : List Nat)
    (hnd : (VsaIris.ra :: Ks).Nodup) (hsub : ∀ k ∈ VsaIris.ra :: Ks, k ∈ gprs)
    {R : Nat → BitVec 64} {A : IProp GF} {B : (Nat → BitVec 64) → IProp GF}
    (hpre : regsOf Ks R ∗ A ⊢ P (BitVec.ofNat 64 (i + 4)))
    (hpost : Q (BitVec.ofNat 64 (i + 4)) ⊢ ∃ Rc, regsOf Ks Rc ∗ B Rc) :
    instrAt i code ∗ fnSpecW Wp entry P Q ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 i ∗ regsOf gprs R ∗ A ∗
      (∀ (Rc R' : Nat → BitVec 64), ⌜R' 1 = BitVec.ofNat 64 (i + 4) ∧ (∀ k ∈ Ks, R' k = Rc k) ∧
          ∀ k, k ∉ VsaIris.ra :: Ks → R' k = R k⌝ -∗
        VsaIris.PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ regsOf gprs R' -∗ B Rc -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, #Hs, Hpc, HR, HA, Hk⟩
  ihave ⟨Hks, Hrest⟩ := regsOf_extract gprs (VsaIris.ra :: Ks) gprs_nodup hnd hsub R $$ HR
  rw [regsOf_cons]
  icases Hks with ⟨Hra, HKs⟩
  iapply wp_callW Wp hexec
  isplitl []
  · iexact Hi
  isplitl []
  · iexact Hs
  isplitl [Hpc]
  · iexact Hpc
  isplitl [Hra]
  · iexact Hra
  isplitl [HKs HA]
  · iapply hpre; iframe HKs HA
  iintro Hpc Hra HQ
  ihave ⟨%Rc, HKs, HB⟩ := hpost $$ HQ
  have hra : VsaIris.ra ∉ Ks := (List.nodup_cons.1 hnd).1
  classical
  have e : ∀ k ∈ Ks, (fun k => if k = VsaIris.ra then BitVec.ofNat 64 (i + 4) else Rc k) k = Rc k :=
    fun k hk => by
      have : k ≠ VsaIris.ra := fun h => hra (h ▸ hk)
      simp [this]
  ihave HR := Hrest $$ %(fun k => if k = VsaIris.ra then BitVec.ofNat 64 (i + 4) else Rc k)
    [Hra HKs]
  · rw [regsOf_cons, regsOf_congr e]
    isplitl [Hra]
    · simp only [ite_true]; iexact Hra
    iexact HKs
  iapply Hk $$ %Rc %_ %⟨?_, fun k hk => ?_, fun k hk => ?_⟩ Hpc HR HB
  · simp [VsaIris.ra]
  · have h1 : k ∈ VsaIris.ra :: Ks := List.mem_cons_of_mem _ hk
    have h2 : k ≠ VsaIris.ra := fun h => hra (h ▸ hk)
    simp [h1, h2]
  · simp [hk]

end Call

end VsaIris.Interp
