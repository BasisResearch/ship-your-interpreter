import VsaIris.Interp.HelperRun
import VsaIris.Vsa.Newlib
import VsaIris.Interp.SpecValue

/-!
# Calling newlib from a symbolic run (lane H2)

H5's newlib statements (`Newlib.lean`, `NewlibOut.lean`) use the calling
convention `argsAt vs ∗ callFrame s need calleeSaved cs`: the argument
registers, `sp` with its stack, the callee-saved registers at their values,
the temporaries, `gp`, the image. A symbolic run's state is lane G's `ms`
(one register valuation `regFile R`). The two are one resource cut
differently (`regFile_newlib`), so a newlib call from a run is one rule:

* `ms_tailNewlib`: a tail call (`j entry`, `ra` still the caller's): the
  callee returns to the run's own caller;
* `ms_callNewlib`: a call (`jal entry`): the run continues at `i + 4`.

Both keep the callee-saved registers at the run's values and hand back the
argument and temporary registers at new values.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

theorem fRegs_perm :
    fRegs.Perm (2 :: (Newlib.calleeSaved ++ (tmpRegs ++ argRegs))) := by
  decide

/-- **The body's registers in H5's convention**: `sp`, the callee-saved
registers, the temporaries, the arguments. -/
theorem regFile_newlib (R : Nat → BitVec 64) :
    regFile (GF := GF) R ⊣⊢ iprop(sp ↦ᵣ R 2 ∗ sepL Newlib.calleeSaved (fun r => r ↦ᵣ R r) ∗
      sepL tmpRegs (fun r => r ↦ᵣ R r) ∗ sepL argRegs (fun r => r ↦ᵣ R r)) := by
  unfold regFile
  refine (sepL_perm _ fRegs_perm).trans ?_
  rw [sepL_cons]
  refine sep_congr_right ?_
  refine (sepL_append _ _ _).trans (sep_congr_right (sepL_append _ _ _))

/-- The argument registers at the run's values give `argsAt`. -/
theorem argsAt_of_regs (R : Nat → BitVec 64) :
    ∀ (vs : List (BitVec 64)), vs.length ≤ 8 → (∀ i (h : i < vs.length), R (10 + i) = vs[i]) →
      sepL (GF := GF) argRegs (fun r => r ↦ᵣ R r) ⊢ argsAt vs := by
  intro vs hlen hvs
  unfold argsAt
  have key : ∀ (k : Nat) (ws : List (BitVec 64)), k + ws.length ≤ 8 →
      (∀ i (h : i < ws.length), R (10 + k + i) = ws[i]) →
      sepL (GF := GF) (argRegs.drop k) (fun r => r ↦ᵣ R r) ⊢
        iprop(sepL (ws.zipIdx k) (fun p => (10 + p.2) ↦ᵣ p.1) ∗
          clobbered (argRegs.drop (k + ws.length))) := by
    intro k ws
    induction ws generalizing k with
    | nil =>
      intro _ _
      simp only [List.zipIdx_nil, sepL_nil, List.length_nil, Nat.add_zero]
      iintro H; isplitr
      · iempintro
      · iapply clobbered_of_fn _ R $$ H
    | cons w ws ih =>
      intro hk hws
      have hk8 : k < 8 := by simp at hk; omega
      have hdrop : argRegs.drop k = (10 + k) :: argRegs.drop (k + 1) := by
        revert hk8; generalize k = j; intro hj
        rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega
      rw [hdrop, sepL_cons, List.zipIdx_cons, sepL_cons]
      have hw : R (10 + k) = w := by
        have := hws 0 (by simp)
        rw [List.getElem_cons_zero] at this; simpa using this
      iintro ⟨H0, H⟩
      rw [hw]
      iframe H0
      have := ih (k + 1) (by simp at hk ⊢; omega) (fun i hi => by
        have := hws (i + 1) (by simp; omega)
        simpa [Nat.add_assoc, Nat.add_comm 1 i] using this)
      simp only [List.length_cons, show k + (ws.length + 1) = k + 1 + ws.length by omega]
      iapply this $$ H
  have := key 0 vs (by omega) (fun i h => by simpa using hvs i h)
  simpa using this

/-- The stack geometry of a run gives H5's `SpIn`. -/
theorem spIn_of_stackGeom {s : BitVec 64} {n need : Nat} (h : StackGeom s n) (hle : need ≤ n) :
    SpIn s need := by
  have h1 := h.le; have h2 := h.lo; have h3 := h.hi; have h4 := h.al
  unfold Vsa.Sim.LayoutInstance.stackSL at h2 h3
  simp only at h2 h3
  exact ⟨by unfold Vsa.Sim.tohostAddr; omega, by omega, h4⟩

variable {live : Nat → Prop}

/-- The registers after a newlib call: the arguments and temporaries at new
values, `sp` and the callee-saved registers as before. -/
theorem regFile_after (R : Nat → BitVec 64) (s : BitVec 64) (hs : R 2 = s) :
    iprop(clobbered (GF := GF) argRegs ∗ clobbered tmpRegs ∗ sp ↦ᵣ s ∗
      sepL Newlib.calleeSaved (fun r => r ↦ᵣ R r)) ⊢
      ∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = R x⌝ := by
  iintro ⟨Hargs, Htmp, Hsp, Hcs⟩
  ihave ⟨%fa, Hargs⟩ := clobbered_fn argRegs (by decide) $$ Hargs
  ihave ⟨%ft, Htmp⟩ := clobbered_fn tmpRegs (by decide) $$ Htmp
  let rv' : Nat → BitVec 64 := fun x =>
    if x ∈ argRegs then fa x else if x ∈ tmpRegs then ft x else if x = 2 then s else R x
  iexists rv'
  isplitl
  · iapply (regFile_newlib rv').2
    have e2 : rv' 2 = s := by simp [rv', argRegs, tmpRegs]
    have ecs : sepL (GF := GF) Newlib.calleeSaved (fun r => r ↦ᵣ rv' r) =
        sepL Newlib.calleeSaved (fun r => r ↦ᵣ R r) :=
      sepL_congr fun r hr => by
        have h1 : r ∉ argRegs := (show ∀ r ∈ Newlib.calleeSaved, r ∉ argRegs by decide) r hr
        have h2 : r ∉ tmpRegs := (show ∀ r ∈ Newlib.calleeSaved, r ∉ tmpRegs by decide) r hr
        have h3 : r ≠ 2 := (show ∀ r ∈ Newlib.calleeSaved, r ≠ 2 by decide) r hr
        simp [rv', h1, h2, h3]
    have et : sepL (GF := GF) tmpRegs (fun r => r ↦ᵣ rv' r) = sepL tmpRegs (fun r => r ↦ᵣ ft r) :=
      sepL_congr fun r hr => by
        have h1 : r ∉ argRegs := (show ∀ r ∈ tmpRegs, r ∉ argRegs by decide) r hr
        simp [rv', h1, hr]
    have ea : sepL (GF := GF) argRegs (fun r => r ↦ᵣ rv' r) = sepL argRegs (fun r => r ↦ᵣ fa r) :=
      sepL_congr fun r hr => by simp [rv', hr]
    rw [e2, ecs, et, ea]
    iframe Hsp Hcs Htmp Hargs
  · ipureintro
    intro x hx hc
    have h1 : x ∉ argRegs := fun h => hc ((show ∀ r ∈ argRegs, r ∈ callerSaved by decide) x h)
    have h2 : x ∉ tmpRegs := fun h => hc ((show ∀ r ∈ tmpRegs, r ∈ callerSaved by decide) x h)
    by_cases h3 : x = 2
    · subst h3; simp [rv', argRegs, tmpRegs, hs]
    · simp [rv', h1, h2, h3]

/-- **A newlib tail call from a run.** The run jumped (`j`) to `entry` with
`ra = R 1`, the caller's return address: the callee returns there, with the
callee-saved registers and `sp` kept. The spec is any `fnSpecW` whose
precondition H5's calling convention supplies (`hP`) and whose
postcondition gives it back (`hQ`); the run owns `n ≥ need` bytes of stack. -/
theorem ms_tailNewlib (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {entry : BitVec 64} {P Q : BitVec 64 → IProp GF} {vs : List (BitVec 64)} {X Y : IProp GF}
    {s : BitVec 64} {need n : Nat} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem}
    (hlen : vs.length ≤ 8) (hvs : ∀ i (h : i < vs.length), R (10 + i) = vs[i]) (hs : R 2 = s)
    (hn : n ≤ s.toNat) (hneed : need ≤ n)
    (hP : ∀ r, iprop(argsAt vs ∗ X ∗ callFrame s need Newlib.calleeSaved R) ⊢ P r)
    (hQ : ∀ r, Q r ⊢ iprop(clobbered argRegs ∗ Y ∗ callFrame s need Newlib.calleeSaved R)) :
    fnSpecW Wp entry P Q ∗ ms entry R S Mt ∗ X ∗ stackScratch s n ∗ gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗
      (PC ↦ᵣ R 1 -∗ ra ↦ᵣ R 1 -∗
        (∃ rv', regFile rv' ∗ ⌜∀ x ∈ fRegs, x ∉ callerSaved → rv' x = R x⌝) -∗ Y -∗
        ownSet S (fun a => a ↦ₘ imgM Mt a) -∗ stackScratch s n -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold ms fnSpecW
  iintro ⟨#Hspec, ⟨Hpc, Hra, Hregs, HS⟩, HX, Hst, #Hgp, #Himg, Hk⟩
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hn hneed $$ Hst
  ihave ⟨Hsp, Hcs, Htmp, Hargs⟩ := (regFile_newlib R).1 $$ Hregs
  ihave Hargs := argsAt_of_regs R vs hlen hvs $$ Hargs
  ihave Htmp := clobbered_of_fn _ R $$ Htmp
  rw [hs]
  iapply Hspec $$ %(R 1) %Φ Hpc Hra [Hargs HX Hsp Hcs Htmp Hst]
  · iapply hP
    unfold callFrame
    iframe Hargs HX Hsp Hcs Hst Hgp Himg Htmp
  iintro Hpc Hra HQ
  ihave ⟨Hargs, HY, Hcf⟩ := hQ (R 1) $$ HQ
  unfold callFrame
  icases Hcf with ⟨Hsp, Hst, Hcs, Htmp, -, -⟩
  ihave Hst := stackScratch_widen hn hneed $$ [Hslack Hst]
  · iframe Hslack Hst
  ihave Hregs := regFile_after R s hs $$ [Hargs Htmp Hsp Hcs]
  · iframe Hargs Htmp Hsp Hcs
  iapply Hk $$ Hpc Hra Hregs HY HS Hst

/-- **A newlib call from a run** (`jal entry` at `i`): the run continues at
`i + 4` with the callee-saved registers and `sp` kept. -/
theorem ms_callNewlib (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    {P Q : BitVec 64 → IProp GF} {vs : List (BitVec 64)} {X Y : IProp GF}
    {s : BitVec 64} {need n : Nat} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem}
    (hlen : vs.length ≤ 8) (hvs : ∀ i (h : i < vs.length), R (10 + i) = vs[i]) (hs : R 2 = s)
    (hn : n ≤ s.toNat) (hneed : need ≤ n)
    (hP : ∀ r, iprop(argsAt vs ∗ X ∗ callFrame s need Newlib.calleeSaved R) ⊢ P r)
    (hQ : ∀ r, Q r ⊢ iprop(clobbered argRegs ∗ Y ∗ callFrame s need Newlib.calleeSaved R)) :
    fnSpecW Wp entry P Q ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ X ∗ stackScratch s n ∗
      gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗ Y -∗
        ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗
        stackScratch s n -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  unfold ms
  iintro ⟨#Hspec, #Hcode, ⟨Hpc, Hra, Hregs, HS⟩, HX, Hst, #Hgp, #Himg, Hk⟩
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hn hneed $$ Hst
  ihave ⟨Hsp, Hcs, Htmp, Hargs⟩ := (regFile_newlib R).1 $$ Hregs
  ihave Hargs := argsAt_of_regs R vs hlen hvs $$ Hargs
  ihave Htmp := clobbered_of_fn _ R $$ Htmp
  rw [hs]
  iapply wp_callW Wp hexec
  iframe Hi Hspec Hpc Hra
  isplitl [Hargs HX Hsp Hcs Htmp Hst]
  · iapply hP
    unfold callFrame
    iframe Hargs HX Hsp Hcs Hst Hgp Himg Htmp
  iintro Hpc Hra HQ
  ihave ⟨Hargs, HY, Hcf⟩ := hQ _ $$ HQ
  unfold callFrame
  icases Hcf with ⟨Hsp, Hst, Hcs, Htmp, -, -⟩
  ihave Hst := stackScratch_widen hn hneed $$ [Hslack Hst]
  · iframe Hslack Hst
  ihave ⟨%R', Hregs, %hk⟩ := regFile_after R s hs $$ [Hargs Htmp Hsp Hcs]
  · iframe Hargs Htmp Hsp Hcs
  iapply Hk $$ %R' %hk HY [Hpc Hra Hregs HS] Hst
  rw [regFile_upd_ra]
  simp only [upd_same]
  iframe Hpc Hra Hregs HS

/-- **A newlib call that may abort, from a run** (`jal entry` at `i`,
`fnSpecAbort`): the return branch is `ms_callNewlib`'s; on abort, the
continuation receives the abort resource, the run's owned bytes, and the stack
below `s` the call did not take. Both branches come from the caller's one
context (`∧`). -/
theorem ms_callNewlibAbort (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} {entry : BitVec 64}
    (hexec : JalExec (vsaModel live) i code entry)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ interpText)
    {P Q : BitVec 64 → IProp GF} {A : IProp GF} {vs : List (BitVec 64)} {X Y : IProp GF}
    {s : BitVec 64} {need n : Nat} {R : Nat → BitVec 64} {S : Nat → Prop} {Mt : Mem}
    (hlen : vs.length ≤ 8) (hvs : ∀ i (h : i < vs.length), R (10 + i) = vs[i]) (hs : R 2 = s)
    (hn : n ≤ s.toNat) (hneed : need ≤ n)
    (hP : ∀ r, iprop(argsAt vs ∗ X ∗ callFrame s need Newlib.calleeSaved R) ⊢ P r)
    (hQ : ∀ r, Q r ⊢ iprop(clobbered argRegs ∗ Y ∗ callFrame s need Newlib.calleeSaved R)) :
    fnSpecAbort Wp entry P Q A ∗ codeRes ∗ ms (BitVec.ofNat 64 i) R S Mt ∗ X ∗ stackScratch s n ∗
      gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗
      ((∀ R' : Nat → BitVec 64, ⌜∀ x ∈ fRegs, x ∉ callerSaved → R' x = R x⌝ -∗ Y -∗
          ms (BitVec.ofNat 64 (i + 4)) (upd R' 1 (BitVec.ofNat 64 (i + 4))) S Mt -∗
          stackScratch s n -∗ Wp.W Φ) ∧
        (A -∗ blockOwn (s.toNat - n) (n - need) -∗ ownSet S (fun a => a ↦ₘ imgM Mt a) -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  unfold ms
  iintro ⟨#Hspec, #Hcode, ⟨Hpc, Hra, Hregs, HS⟩, HX, Hst, #Hgp, #Himg, Hk⟩
  ihave #Hi := instrAt_of_codeRes hcode $$ Hcode
  ihave ⟨Hslack, Hst⟩ := stackScratch_narrow hn hneed $$ Hst
  ihave ⟨Hsp, Hcs, Htmp, Hargs⟩ := (regFile_newlib R).1 $$ Hregs
  ihave Hargs := argsAt_of_regs R vs hlen hvs $$ Hargs
  ihave Htmp := clobbered_of_fn _ R $$ Htmp
  rw [hs]
  iapply wp_callAbort Wp hexec
  iframe Hi Hspec Hpc Hra
  isplitl [Hargs HX Hsp Hcs Htmp Hst]
  · iapply hP
    unfold callFrame
    iframe Hargs HX Hsp Hcs Hst Hgp Himg Htmp
  isplit
  · iintro Hpc Hra HQ
    ihave Hk := and_elim_l $$ Hk
    ihave ⟨Hargs, HY, Hcf⟩ := hQ _ $$ HQ
    unfold callFrame
    icases Hcf with ⟨Hsp, Hst, Hcs, Htmp, -, -⟩
    ihave Hst := stackScratch_widen hn hneed $$ [Hslack Hst]
    · iframe Hslack Hst
    ihave ⟨%R', Hregs, %hk⟩ := regFile_after R s hs $$ [Hargs Htmp Hsp Hcs]
    · iframe Hargs Htmp Hsp Hcs
    iapply Hk $$ %R' %hk HY [Hpc Hra Hregs HS] Hst
    rw [regFile_upd_ra]
    simp only [upd_same]
    iframe Hpc Hra Hregs HS
  · iintro HA
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ HA Hslack HS

/-- A tracked part of a run's owned bytes, out of its state. -/
theorem ms_split {pc : BitVec 64} {R : Nat → BitVec 64} {S T : Nat → Prop} {M : Mem}
    (hd : ∀ a, S a → ¬ T a) :
    ms (GF := GF) pc R (fun a => S a ∨ T a) M ⊢
      ms pc R S M ∗ ownSet T (fun a => a ↦ₘ imgM M a) := by
  unfold ms
  iintro ⟨Hpc, Hra, Hregs, HS⟩
  ihave ⟨H1, H2⟩ := ownSet_split_tracked S T M hd $$ HS
  iframe Hpc Hra Hregs H1 H2

/-- And back in, at one tracking memory agreeing with both. -/
theorem ms_join {pc : BitVec 64} {R : Nat → BitVec 64} {S T : Nat → Prop} {M1 M2 : Mem} :
    ms (GF := GF) pc R S M1 ∗ ownSet T (fun a => a ↦ₘ imgM M2 a) ⊢
      ∃ M, ms pc R (fun a => S a ∨ T a) M ∗
        ⌜(∀ a, S a → imgM M a = imgM M1 a) ∧ (∀ a, T a → imgM M a = imgM M2 a) ∧
          ∀ a, S a → ¬ T a⌝ := by
  unfold ms
  iintro ⟨⟨Hpc, Hra, Hregs, HS⟩, HT⟩
  ihave ⟨%M, H, %h⟩ := ownSet_join_tracked S T M1 M2 $$ [HS HT]
  · iframe HS HT
  iexists M
  iframe Hpc Hra Hregs H
  ipureintro; exact h

/-- A C string of the fixed `.rodata` is a persistent string. -/
theorem strAt_rodata {p : Nat} {x : String}
    (hdom : ∀ i, i < x.toList.length + 1 → rodataDom (p + i)) (hc : CStrImg rodataByte p x)
    (hw : StrWin p x.toList.length) :
    binImg (GF := GF) ⊢ strAt p x := by
  unfold binImg strAt
  iintro ⟨-, #H⟩
  iexists rodataByte
  isplitr
  · ipureintro; exact ⟨hc, hw⟩
  unfold roImg
  imodintro
  iintro %k %hk
  have hk' : rodataDom k := by
    obtain ⟨h1, h2⟩ := hk
    simp only at h1 h2
    have := hdom (k - p) (by omega)
    rwa [show p + (k - p) = k by omega] at this
  iapply H $$ %k %hk'

end

end VsaIris.Interp
