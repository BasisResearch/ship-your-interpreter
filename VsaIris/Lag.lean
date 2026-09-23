import VsaIris.Ptsto

/-!
# The lagged multi-step kernel, shared by both weakest preconditions

A VSA segment fact describes `K + 1` machine steps by their end state only.
The state interpretation (`fullInterp`, Ptsto.lean §Lag) lets the ghost maps
lag behind the machine while such a run is in flight. `lag_run` is the one
proof that walks the run step by step: each step reads the lag from the
control cell, re-derives the footprint facts at the lagged state, and either
advances the lag or, at the last step, commits the run's effect and resets the
lag to zero.

The kernel is stated against an abstract *raw loop WP* `L` that satisfies a
single-step rule (`StepRule lat L`). `lat` is the modality one machine step
pays for: the identity for the total WP (`twp` forbids laters) and `▷` for the
partial WP (the later that Löb consumes, iris-lean `wp_lift_step_fupd`). The
total instance is in `Step.lean` and the partial one in `PartialWP.lean`;
every segment rule of either WP is this kernel at a footprint.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- Opening the state interpretation with the control cell at lag `j`. -/
theorem fullInterp_lag {σ : M.State} {j : Nat} :
    fullInterp (GF := GF) M σ ⊢ ctlAt j -∗
      ∃ c : NatMap Nat, ghost_map_auth G.ctlName (DFrac.own 1) c ∗
        ⌜PartialMap.get? c 0 = some j⌝ ∗ ctlAt j ∗ lagInterp M j σ := by
  unfold fullInterp
  iintro ⟨%c, %j', Hc, %hj, Hl⟩ Ht
  unfold ctlAt
  ihave %hl := ghost_map_lookup $$ Hc Ht
  rw [hj] at hl
  cases hl
  iexists c
  iframe Hc Ht Hl
  ipureintro; exact hj

theorem fullInterp_intro {σ : M.State} (c : NatMap Nat) (j : Nat)
    (hc : PartialMap.get? c 0 = some j) :
    ghost_map_auth (GF := GF) G.ctlName (DFrac.own 1) c ∗ lagInterp M j σ ⊢ fullInterp M σ := by
  unfold fullInterp
  iintro ⟨Hc, Hl⟩
  iexists c, j
  iframe Hc Hl
  ipureintro; exact hc

theorem lagInterp_intro {σ : M.State} {j : Nat} (mr : NatMap (BitVec 64))
    (mm : NatMap (BitVec 8)) (σ0 : M.State) (h : AgreeOk M mr mm σ0)
    (hre : ReachesN M j σ0 σ) :
    ghost_map_auth (GF := GF) G.regName (DFrac.own 1) mr ∗
      ghost_map_auth G.memName (DFrac.own 1) mm ⊢ lagInterp M j σ := by
  unfold lagInterp
  iintro ⟨Hr, Hm⟩
  iexists mr, mm
  iframe Hr Hm
  ipureintro; exact ⟨σ0, h, hre⟩

variable (M) in
/-- The single-step rule of a raw loop WP `L`: from any state interpretation,
show that the machine takes a normal step, and after it re-establish the
interpretation together with `lat L`. The updates are basic updates: the
kernel only moves ghost maps. -/
def StepRule (lat : IProp GF → IProp GF) (L : IProp GF) : Prop :=
  (∀ σ, fullInterp (GF := GF) M σ ==∗ ⌜∃ σ', M.step σ = .next σ'⌝ ∗
      ∀ σ', ⌜M.step σ = .next σ'⌝ ==∗ fullInterp M σ' ∗ lat L) ⊢ L

/-- A lagged run, described by its footprint: `Fp` is owned before the run
and pins `Pre` in every state the authorities agree with (`look`); from every
well-formed `Pre` state the machine runs `K + 1` steps to a well-formed state
related by `Post` (`run`); and a `Post` pair lets the authorities move from
the start state to the end state, turning `Fp` into `Fp' σf` (`commit`). -/
structure LagFoot (M : MachineModel) (Fp : IProp GF) (Fp' : M.State → IProp GF)
    (Pre : M.State → Prop) (Post : M.State → M.State → Prop) (K : Nat) : Prop where
  look : ∀ mr mm, ghost_map_auth (GF := GF) G.regName (DFrac.own 1) mr ∗
      ghost_map_auth G.memName (DFrac.own 1) mm ∗ Fp ⊢
    ghost_map_auth G.regName (DFrac.own 1) mr ∗ ghost_map_auth G.memName (DFrac.own 1) mm ∗
      Fp ∗ ⌜∀ σ, RegAgree M mr σ → MemAgree M mm σ → Pre σ⌝
  run : ∀ σ, M.ok σ → Pre σ → ∃ σf, ReachesN M (K + 1) σ σf ∧ M.ok σf ∧ Post σ σf
  commit : ∀ mr mm σ σf, RegAgree M mr σ → MemAgree M mm σ → Post σ σf →
    ghost_map_auth (GF := GF) G.regName (DFrac.own 1) mr ∗
      ghost_map_auth G.memName (DFrac.own 1) mm ∗ Fp ⊢ |==>
    ∃ mr' mm', ghost_map_auth G.regName (DFrac.own 1) mr' ∗
      ghost_map_auth G.memName (DFrac.own 1) mm' ∗ Fp' σf ∗
      ⌜RegAgree M mr' σf ∧ MemAgree M mm' σf⌝

/-- **The lag kernel.** `k + 1` steps of a `K + 1`-step run remain and the
ghost maps lag by `j`. The last step commits the run and hands `next` the
CPU token, the committed footprint and the frame `R`; `next` must prove
`lat L` (for the partial WP, the rest of the run under a later). -/
theorem lag_run {lat : IProp GF → IProp GF} {L : IProp GF} (hlat : ∀ P, P ⊢ lat P)
    (hstep : StepRule M lat L) {Fp : IProp GF} {Fp' : M.State → IProp GF}
    {Pre : M.State → Prop} {Post : M.State → M.State → Prop} {K : Nat}
    (hf : LagFoot M Fp Fp' Pre Post K) (R : IProp GF)
    (next : ∀ σ σf, Post σ σf → cpuTok ∗ Fp' σf ∗ R ⊢ lat L) :
    ∀ k j, j + (k + 1) = K + 1 → ctlAt (GF := GF) j ∗ Fp ∗ R ⊢ L := by
  intro k
  induction k with
  | zero => ?_
  | succ k ih => ?_
  all_goals
    intro j hjk
    refine .trans ?_ hstep
    iintro ⟨Hj, Hf, HR⟩ %σ₁ Hσ
    ihave ⟨%c, Hc, %hc, Hj, Hl⟩ := fullInterp_lag (M := M) $$ Hσ Hj
    unfold lagInterp ctlAt
    icases Hl with ⟨%mr, %mm, Hmr, Hmm, %hlag⟩
    obtain ⟨σ0, ⟨hr, hm, hok⟩, hre⟩ := hlag
    ihave ⟨Hmr, Hmm, Hf, %hpre⟩ := hf.look mr mm $$ [Hmr Hmm Hf]
    · iframe Hmr Hmm Hf
    obtain ⟨σf, hrun, hokf, hpost⟩ := hf.run σ0 hok (hpre σ0 hr hm)
  · -- last step: commit the run, reset the lag
    have hrest : ReachesN M 1 σ₁ σf := ReachesN.split hre (hjk ▸ hrun)
    obtain ⟨σ1, hs1, hrest1⟩ : ∃ σ1, M.step σ₁ = .next σ1 ∧ ReachesN M 0 σ1 σf := by
      cases hrest with
      | succ s r => exact ⟨_, s, r⟩
    cases hrest1.zero_eq
    imodintro
    isplitr
    · ipureintro; exact ⟨_, hs1⟩
    iintro %σ' %hs'
    rw [hs1] at hs'
    cases hs'
    imod ghost_map_update 0 $$ Hc Hj with ⟨Hc, Hj⟩
    imod hf.commit mr mm σ0 σf hr hm hpost $$ [Hmr Hmm Hf]
      with ⟨%mr', %mm', Hmr, Hmm, Hf, %⟨hr', hm'⟩⟩
    · iframe Hmr Hmm Hf
    imodintro
    isplitl [Hc Hmr Hmm]
    · iapply fullInterp_intro (M := M) _ 0 (LawfulPartialMap.get?_insert_eq rfl)
      iframe Hc
      iapply lagInterp_intro (M := M) mr' mm' _ ⟨hr', hm', hokf⟩ (.zero _)
      iframe Hmr Hmm
    iapply next σ0 σf hpost
    unfold cpuTok ctlAt
    iframe Hj Hf HR
  · -- intermediate step: advance the lag
    have hrest : ReachesN M (k + 1 + 1) σ₁ σf := ReachesN.split hre (hjk ▸ hrun)
    obtain ⟨σ1, hs1, _⟩ : ∃ σ1, M.step σ₁ = .next σ1 ∧ ReachesN M (k + 1) σ1 σf := by
      cases hrest with
      | succ s r => exact ⟨_, s, r⟩
    imodintro
    isplitr
    · ipureintro; exact ⟨_, hs1⟩
    iintro %σ' %hs'
    rw [hs1] at hs'
    cases hs'
    imod ghost_map_update (j + 1) $$ Hc Hj with ⟨Hc, Hj⟩
    imodintro
    isplitl [Hc Hmr Hmm]
    · iapply fullInterp_intro (M := M) _ (j + 1) (LawfulPartialMap.get?_insert_eq rfl)
      iframe Hc
      iapply lagInterp_intro (M := M) mr mm σ0 ⟨hr, hm, hok⟩ (hre.snoc hs1)
      iframe Hmr Hmm
    iapply hlat
    iapply ih (j + 1) (by omega)
    unfold ctlAt
    iframe Hj Hf HR

end

end VsaIris
