import VsaIris.Interp.Arm

/-!
# A symbolic run that pays a later (lane E5)

The partial WP's Löb hypothesis is `▷`-guarded; a recursive `jal` pays for it
(`wp_callAbort_later`). `exec_stmt`'s `if` arm re-enters the dispatch INSIDE
its frame by a jump (`j 0x80004014`, `bnez s0,0x80004014`), so the later is paid
by the run that reaches the dispatch point: its first segment's step strips
the `▷` (`wp_localRunW_later`, `wp_swpF_later`). The run must take a step,
which `RunKne` records: its end state's PC differs from the start's.
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst Vsa.MemRepr

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- **A local run that takes a step pays a later** (partial WP): a `▷ X` in
the context is available, without the later, to the run's continuation. -/
theorem wp_localRunW_later {Φ : Nat × String → IProp GF} {X : IProp GF}
    {ro : List (Nat × BitVec 64)} {text : List (Nat × BitVec 8)} {rs : List Nat}
    {S : Nat → Prop} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} :
    ∀ n rv mv, LocalRun M ro text rs S Q n rv mv → ¬ Q rv mv →
      roOwn (GF := GF) ro text ∗ sepL rs (fun r => r ↦ᵣ rv r) ∗ ownSet S (fun a => a ↦ₘ mv a) ∗
        ▷ X ∗ (X -∗ runKontW (wpW M) Φ rs S Q)
      ⊢ (wpW M).W Φ := by
  intro n rv mv hrun hne
  cases n with
  | zero => exact absurd hrun hne
  | succ n =>
    rcases hrun with hQ | ⟨K, hseg⟩
    · exact absurd hQ hne
    unfold roOwn ownSet
    iintro ⟨⟨#Hro, #Htx⟩, Hrs, ⟨%l, %⟨hnd, hmem⟩, Hl⟩, HX, Hk⟩
    iapply (wpW M).lagRun (hseg.lagFoot hmem)
    unfold runFoot
    isplitl [Hrs Hl]
    · iframe Hro Htx Hrs Hl
    iintro %σ %σf %⟨_, _, _, hP⟩ ⟨_, _, Hrs, Hl⟩
    simp only [wpW_lat]
    inext
    ihave Hk := Hk $$ HX
    iapply wp_localRunW (wpW M) n _ _ hP
    unfold roOwn ownSet
    iframe Hro Htx Hrs Hk
    iexists l
    iframe Hl
    ipureintro; exact ⟨hnd, hmem⟩

variable {live : Nat → Prop}

/-- The post of a run that must leave its start PC `pc0`. -/
abbrev RunKne (pc0 : BitVec 64) (Wp : MachWP (GF := GF) (vsaModel live))
    (Φ : Nat × String → IProp GF) (F : IProp GF) (S : Nat → Prop) (rv : Nat → BitVec 64)
    (mv : Nat → BitVec 8) : Prop :=
  rv VsaIris.PC ≠ pc0 ∧ RunK Wp Φ F S rv mv

/-- **A symbolic run paying a later**, partial WP (`wp_swpF`'s twin): the
run's continuation gets `X` without the later, because the run leaves `pc`. -/
theorem wp_swpF_later {Φ : Nat × String → IProp GF} {F X : IProp GF}
    {text : List (Nat × BitVec 8)} {S : Nat → Prop} {pc : BitVec 64} {R : Nat → BitVec 64}
    {Mt : Mem}
    (h : let F' := iprop(F ∗ X); SWP live text iRegs S (RunKne pc (wpW (vsaModel live)) Φ F' S) pc R Mt) :
    roOwn roR text ∗ F ∗ ▷ X ∗ ms pc R S Mt ⊢ (wpW (vsaModel live)).W Φ := by
  obtain ⟨n, hn⟩ := h
  let rv : Nat → BitVec 64 := fun r => if r = 32 then pc else R r
  have hm : Matches iRegs S pc R Mt rv (imgM Mt) := ⟨by simp [rv, VsaIris.PC],
    fun r _ hne => by simp only [rv, show r ≠ 32 from by simpa [VsaIris.PC] using hne, ite_false],
    fun _ _ => rfl⟩
  have hrun := hn rv (imgM Mt) hm
  have hne : ¬ RunKne pc (wpW (vsaModel live)) Φ iprop(F ∗ X) S rv (imgM Mt) := fun h => h.1 hm.pc
  unfold ms
  iintro ⟨#Hro, HF, HX, ⟨Hpc, Hra, Hregs, HS⟩⟩
  iapply wp_localRunW_later (X := X) n rv (imgM Mt) hrun hne
  iframe Hro HS HX
  isplitl [Hpc Hra Hregs]
  · iapply (sepL_iRegs rv).2
    have e1 : rv 32 = pc := by simp [rv]
    have e2 : rv 1 = R 1 := by simp [rv]
    have e3 : regFile (GF := GF) rv = regFile R := by
      unfold regFile
      exact sepL_congr fun x hx => by
        have : x ≠ 32 := fun e => by subst e; revert hx; decide
        simp only [rv, this, ite_false]
    rw [e1, e2, e3]
    iframe Hpc Hra Hregs
  iintro HX %rv' %mv' %hq Hregs HS
  iapply hq.2
  iframe HF HX Hregs HS

/-- **The end of a later-paying run**: at an end PC other than the start. -/
theorem swp_closeF_ne (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {F : IProp GF} {text : List (Nat × BitVec 8)} {S : Nat → Prop} {pc0 pc : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (hne : pc ≠ pc0) (h : F ∗ ms pc R S Mt ⊢ Wp.W Φ) :
    SWP live text iRegs S (RunKne pc0 Wp Φ F S) pc R Mt := by
  refine swp_done fun rv mv hm => ⟨hm.pc ▸ hne, ?_⟩
  refine .trans ?_ h
  unfold ms
  iintro ⟨HF, Hregs, HS⟩
  ihave ⟨Hpc, Hra, Hregs⟩ := (sepL_iRegs rv).1 $$ Hregs
  have e3 : ∀ x ∈ fRegs, rv x = R x := fun x hx =>
    hm.regs x (by rw [iRegs_eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
      (fun e => by subst e; revert hx; decide)
  have e2 : rv 1 = R 1 := hm.regs 1 (by decide) (by decide)
  have e1 : rv 32 = pc := hm.pc
  rw [e1, e2]
  iframe HF Hpc Hra
  isplitl [Hregs]
  · unfold regFile
    rw [sepL_congr (Ψ := fun r => iprop(r ↦ᵣ R r)) (fun x hx => by rw [e3 x hx])] at *
    iexact Hregs
  iapply ownSet_congr (fun a ha => by rw [hm.img a ha]) $$ HS

/-- `swp_closeF_ne` with the end registers and memory named. -/
theorem swp_closeRM_ne (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {F : IProp GF} {text : List (Nat × BitVec 8)} {S : Nat → Prop} {pc0 pc : BitVec 64}
    {R : Nat → BitVec 64} {Mt : Mem} (hne : pc ≠ pc0)
    (h : ∀ R' Mt', R' = R → Mt' = Mt → F ∗ ms pc R' S Mt' ⊢ Wp.W Φ) :
    SWP live text iRegs S (RunKne pc0 Wp Φ F S) pc R Mt :=
  swp_closeF_ne Wp hne (h R Mt rfl rfl)

end

end VsaIris.Interp
