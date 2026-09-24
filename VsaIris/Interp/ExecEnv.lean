import VsaIris.Interp.ExecArm
import VsaIris.Interp.CallRegs
import VsaIris.Interp.SpecEnv

/-!
# `env_new` / `env_define` from an exec arm (lane E5)

The block and `for` arms call `env_new(env)`, the `var` arms
`env_define(env, name, &v)`. H1's specs (`SpecEnv.lean`) are stated over the
callee's register list; `ms_callRegs` (H2) cuts the arm's register file. The
counted regime cannot run out of memory, so the specs' abort branch is
vacuous there (`fnSpecW_of_abort_false`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open Vsa.MemRepr Vsa.While Vsa.RuntimeRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop} {N : NativeAddrs}

/-- A frame's `Env*` is never NULL (`FrameLayout.e_ne`). -/
theorem storeRepr_frameAt_ne {s : Store} {B : List (Nat × Nat)} {fa e : Nat} :
    storeRepr (GF := GF) N s B ∗ frameAt fa e ⊢ ⌜e ≠ 0⌝ := by
  iintro ⟨Hs, #He⟩
  ihave ⟨⟨Hs, -⟩, %hlt⟩ := keep_pure (storeRepr_frameAt N (s := s) (B := B) (fa := fa) (e := e))
    $$ [Hs]
  · iframe Hs He
  unfold storeRepr
  icases Hs with ⟨%mf, %mc, %Bs, -, -, %hp, Hfr, -⟩
  have hf : s.frames.toList[fa]? = some s.frames[fa] := by
    rw [Array.getElem?_toList]; exact Array.getElem?_eq_getElem hlt
  ihave ⟨%bl, -, Hfa, -⟩ := framesOwn_open N fa 0 s.frames.toList Bs _ hf $$ Hfr
  unfold frameOwn frameBody
  icases Hfa with ⟨%Gm, -, #He', %img, %hlay, -⟩
  simp only [Nat.zero_add] at *
  ihave %heq := frameAt_agree fa e Gm.e $$ [He He']
  · iframe He He'
  ipureintro
  rw [heq]; exact hlay.e_ne

omit I in
/-- **A function spec whose abort cannot happen is an ordinary one.** -/
theorem fnSpecW_of_abort_false {M : MachineModel} (Wp : MachWP (GF := GF) M) (entry : BitVec 64)
    (P Q : BitVec 64 → IProp GF) (A : IProp GF) (hA : A ⊢ False) :
    fnSpecAbort Wp entry P Q A ⊢ fnSpecW Wp entry P Q := by
  unfold fnSpecAbort fnSpecW
  iintro #H
  imodintro
  iintro %r %Φ Hpc Hra HP Hk
  iapply H $$ %r %Φ Hpc Hra HP
  isplit
  · iexact Hk
  · iintro HA
    iexfalso
    iapply hA $$ HA

/-- The registers an `env_new` call takes: `a0`, `sp`, the clobbered and the
saved ones (`s0`-`s6`). -/
abbrev envNewL : List Nat := 10 :: 2 :: (retClob ++ newSaved)

/-- **`env_new(R 10)` from a run, counted regime** (`jal env_new` at `i`):
the run continues at `i + 4` with every register but `a0` and the clobbered
ones kept, the new frame's `Env*` in `a0` bound to the next frame address, the
store extended (`Store.allocFrame`), `envBytes` credits spent. -/
theorem ms_callEnvNew (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)}
    (hexec : JalExec (vsaModel live) i code envNewPC)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) {k : Nat} {st : Store} {po : Option Addr}
    {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem}
    (hsp : EnvSp (R 2) envNewNeed) :
    envNewSpec Wp N ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗
      stackScratch (R 2) envNewNeed ∗ parentAt po (R 10).toNat ∗
      heapStore N (.counted (k + envBytes)) st ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ (10 :: retClob) → R' x = R x⌝ -∗
        stackScratch (R 2) envNewNeed -∗ heapStore N (.counted k) (st.allocFrame po).1 -∗
        frameAt st.frames.size (R' 10).toNat -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold envNewSpec
  iintro ⟨#Hen, #Hcode, Hms, Hst, #Hpar, Hh, Hk⟩
  ihave #Hgp := codeRes_gp $$ Hcode
  ihave #Hspec := Hen $$ %(.counted k) %st %po %(R 10) %(R 2) %(newSaved.map fun k => (k, R k))
    %(by simp [newSaved])
  ihave #Hspec := fnSpecW_of_abort_false Wp _ _ _ _ (by
    iintro ⟨%h, -⟩; cases h) $$ Hspec
  iapply (ms_callRegs Wp hexec hcode (L := envNewL) (K := [23, 24, 25, 26, 27]) (by decide)
    (P := fun r => iprop(⌜r.toNat % 4 = 0 ∧ EnvSp (R 2) envNewNeed⌝ ∗ (10 : Nat) ↦ᵣ R 10 ∗
      sp ↦ᵣ R 2 ∗ gp ↦ᵣ□ gpV ∗ clobbered retClob ∗ savedOwn (newSaved.map fun k => (k, R k)) ∗
      stackScratch (R 2) envNewNeed ∗ parentAt po (R 10).toNat ∗
      heapStore N ((Regime.counted k).plus envBytes) st))
    (Q := fun _ => iprop(∃ e : BitVec 64, (10 : Nat) ↦ᵣ e ∗ sp ↦ᵣ R 2 ∗ clobbered retClob ∗
      savedOwn (newSaved.map fun k => (k, R k)) ∗ stackScratch (R 2) envNewNeed ∗
      heapStore N (.counted k) (st.allocFrame po).1 ∗ frameAt st.frames.size e.toNat))
    (X := iprop(gp ↦ᵣ□ Newlib.gpV ∗ stackScratch (R 2) envNewNeed ∗ parentAt po (R 10).toNat ∗
      heapStore N (.counted (k + envBytes)) st))
    (Y := fun f => iprop(⌜f 2 = R 2 ∧ ∀ k ∈ newSaved, f k = R k⌝ ∗
      stackScratch (R 2) envNewNeed ∗ heapStore N (.counted k) (st.allocFrame po).1 ∗
      frameAt st.frames.size (f 10).toNat))
    (R := R) (S := S) (Mt := Mt) ?hP ?hQ)
  case hP =>
    simp only [envNewL, sepL_cons]
    iintro ⟨⟨H10, H2, Hcs⟩, #Hgp', Hst, #Hpar', Hh⟩
    ihave ⟨Hcl, Hsv⟩ := (sepL_append _ _ _).1 $$ Hcs
    unfold VsaIris.sp savedOwn
    rw [show Newlib.gpV = MallocFast.gpV from rfl, Regime.plus_counted]
    iframe H10 H2 Hgp' Hst Hpar' Hh
    isplitl []
    · ipureintro; exact ⟨hi4, hsp⟩
    isplitl [Hcl]
    · iapply clobbered_of_fn retClob R $$ Hcl
    · rw [VsaIris.sepL_map]; iexact Hsv
  case hQ =>
    unfold VsaIris.sp savedOwn
    iintro ⟨%q, H10, H2, Hcl, Hsv, Hst, Hh, #Hfr⟩
    ihave ⟨%g, Hcl⟩ := clobbered_fn retClob (by decide) $$ Hcl
    iexists (fun y => if y = 10 then q else if y = 2 then R 2 else if y ∈ newSaved then R y else g y)
    simp only [envNewL, sepL_cons]
    rw [VsaIris.sepL_map] at *
    have eCl : sepL (GF := GF) retClob (fun y => y ↦ᵣ (if y = 10 then q else if y = 2 then R 2
        else if y ∈ newSaved then R y else g y)) = sepL retClob (fun y => y ↦ᵣ g y) :=
      sepL_congr fun y hy => by
        obtain ⟨h10, h2, hs⟩ := (show ∀ y ∈ retClob, y ≠ 10 ∧ y ≠ 2 ∧ y ∉ newSaved by decide) y hy
        simp [h10, h2, hs]
    have eSv : sepL (GF := GF) newSaved (fun y => y ↦ᵣ (if y = 10 then q else if y = 2 then R 2
        else if y ∈ newSaved then R y else g y)) = sepL newSaved (fun y => y ↦ᵣ R y) :=
      sepL_congr fun y hy => by
        obtain ⟨h10, h2⟩ := (show ∀ y ∈ newSaved, y ≠ 10 ∧ y ≠ 2 by decide) y hy
        simp [h10, h2, hy]
    simp only [ite_true, show (2 : Nat) ≠ 10 from by decide, ite_false]
    isplitl [H10 H2 Hcl Hsv]
    · iframe H10 H2
      iapply (sepL_append _ _ _).2
      rw [eCl, eSv]
      iframe Hcl Hsv
    iframe Hst Hh Hfr
    ipureintro
    refine ⟨trivial, fun k hk => ?_⟩
    obtain ⟨h10, h2⟩ := (show ∀ y ∈ newSaved, y ≠ 10 ∧ y ≠ 2 by decide) k hk
    simp [h10, h2, hk]
  iframe Hspec Hcode Hms Hgp Hst Hpar Hh
  iintro %f ⟨%⟨hf2, hfs⟩, Hst, Hh, #Hfr⟩ Hms
  have hkeep : ∀ x ∈ fRegs, x ∉ (10 :: retClob) →
      (fun x => if x ∈ envNewL then f x else R x) x = R x := by
    intro x hx hc
    by_cases hL : x ∈ envNewL
    · simp only [hL, ite_true]
      by_cases h2 : x = 2
      · subst h2; exact hf2
      · have hs : x ∈ newSaved :=
          (show ∀ y ∈ envNewL, y ∉ (10 :: retClob) → y ≠ 2 → y ∈ newSaved by decide) x hL hc h2
        exact hfs x hs
    · simp [hL]
  have e10 : (fun x => if x ∈ envNewL then f x else R x) 10 = f 10 := by
    simp only [show (10 : Nat) ∈ envNewL from by decide, ite_true]
  rw [← e10] at *
  iapply Hk $$ %(fun x => if x ∈ envNewL then f x else R x) %hkeep Hst Hh Hfr Hms

end

end VsaIris.Interp
