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
    (mm : NatMap (BitVec 8)) (mo : NatMap String) (σ0 : M.State) (h : AgreeOk M mr mm σ0)
    (ho : ConAgree M mo σ0) (hre : ReachesN M j σ0 σ) :
    ghost_map_auth (GF := GF) G.regName (DFrac.own 1) mr ∗
      ghost_map_auth G.memName (DFrac.own 1) mm ∗
      ghost_map_auth G.conName (DFrac.own 1) mo ⊢ lagInterp M j σ := by
  unfold lagInterp
  iintro ⟨Hr, Hm, Ho⟩
  iexists mr, mm, mo
  iframe Hr Hm Ho
  ipureintro; exact ⟨σ0, h, ho, hre⟩

/-- The three authorities the lagged bridges hold: registers, memory, and
the console (F2). -/
abbrev mauths (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8)) (mo : NatMap String) :
    IProp GF :=
  iprop(ghost_map_auth G.regName (DFrac.own 1) mr ∗ ghost_map_auth G.memName (DFrac.own 1) mm ∗
    ghost_map_auth G.conName (DFrac.own 1) mo)

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
the start state to the end state, turning `Fp` into `Fp' σf` (`commit`). The
console authority moves with the others: a run that prints owns the console
cell in `Fp` (`RunFactO.lagFootPrint`), and a silent run keeps the authority
because `Post` frames the output (`LagFoot.ofRM`). -/
structure LagFoot (M : MachineModel) (Fp : IProp GF) (Fp' : M.State → IProp GF)
    (Pre : M.State → Prop) (Post : M.State → M.State → Prop) (K : Nat) : Prop where
  look : ∀ mr mm mo, mauths mr mm mo ∗ Fp ⊢
    mauths mr mm mo ∗ Fp ∗ ⌜∀ σ, RegAgree M mr σ → MemAgree M mm σ → ConAgree M mo σ → Pre σ⌝
  run : ∀ σ, M.ok σ → Pre σ → ∃ σf, ReachesN M (K + 1) σ σf ∧ M.ok σf ∧ Post σ σf
  commit : ∀ mr mm mo σ σf, RegAgree M mr σ → MemAgree M mm σ → ConAgree M mo σ → Post σ σf →
    mauths mr mm mo ∗ Fp ⊢ |==>
    ∃ mr' mm' mo', mauths mr' mm' mo' ∗ Fp' σf ∗
      ⌜RegAgree M mr' σf ∧ MemAgree M mm' σf ∧ ConAgree M mo' σf⌝

/-- A lagged run over registers and memory only, which prints nothing: the
console authority is kept, and `Post`'s output frame re-establishes its
agreement at the end state. Every silent run (`RunFact`, `SegFrom`) is one. -/
theorem LagFoot.ofRM {Fp : IProp GF} {Fp' : M.State → IProp GF}
    {Pre : M.State → Prop} {Post : M.State → M.State → Prop} {K : Nat}
    (look : ∀ mr mm, ghost_map_auth (GF := GF) G.regName (DFrac.own 1) mr ∗
        ghost_map_auth G.memName (DFrac.own 1) mm ∗ Fp ⊢
      ghost_map_auth G.regName (DFrac.own 1) mr ∗ ghost_map_auth G.memName (DFrac.own 1) mm ∗
        Fp ∗ ⌜∀ σ, RegAgree M mr σ → MemAgree M mm σ → Pre σ⌝)
    (run : ∀ σ, M.ok σ → Pre σ → ∃ σf, ReachesN M (K + 1) σ σf ∧ M.ok σf ∧ Post σ σf)
    (commit : ∀ mr mm σ σf, RegAgree M mr σ → MemAgree M mm σ → Post σ σf →
      ghost_map_auth (GF := GF) G.regName (DFrac.own 1) mr ∗
        ghost_map_auth G.memName (DFrac.own 1) mm ∗ Fp ⊢ |==>
      ∃ mr' mm', ghost_map_auth G.regName (DFrac.own 1) mr' ∗
        ghost_map_auth G.memName (DFrac.own 1) mm' ∗ Fp' σf ∗
        ⌜RegAgree M mr' σf ∧ MemAgree M mm' σf⌝)
    (silent : ∀ σ σf, Post σ σf → M.out σf = M.out σ) :
    LagFoot M Fp Fp' Pre Post K where
  look mr mm mo := by
    unfold mauths
    iintro ⟨⟨Hr, Hm, Ho⟩, Hf⟩
    ihave ⟨Hr, Hm, Hf, %h⟩ := look mr mm $$ [Hr Hm Hf]
    · iframe Hr Hm Hf
    iframe Hr Hm Ho Hf
    ipureintro
    exact fun σ hr hm _ => h σ hr hm
  run := run
  commit mr mm mo σ σf hr hm ho hp := by
    unfold mauths
    iintro ⟨⟨Hr, Hm, Ho⟩, Hf⟩
    imod commit mr mm σ σf hr hm hp $$ [Hr Hm Hf] with ⟨%mr', %mm', Hr, Hm, Hf, %⟨hr', hm'⟩⟩
    · iframe Hr Hm Hf
    imodintro
    iexists mr', mm', mo
    iframe Hr Hm Ho Hf
    ipureintro
    exact ⟨hr', hm', fun v hv => (silent σ σf hp).trans (ho v hv)⟩

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
    icases Hl with ⟨%mr, %mm, %mo, Hmr, Hmm, Hmo, %hlag⟩
    obtain ⟨σ0, ⟨hr, hm, hok⟩, ho, hre⟩ := hlag
    ihave ⟨⟨Hmr, Hmm, Hmo⟩, Hf, %hpre⟩ := hf.look mr mm mo $$ [Hmr Hmm Hmo Hf]
    · unfold mauths; iframe Hmr Hmm Hmo Hf
    obtain ⟨σf, hrun, hokf, hpost⟩ := hf.run σ0 hok (hpre σ0 hr hm ho)
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
    imod hf.commit mr mm mo σ0 σf hr hm ho hpost $$ [Hmr Hmm Hmo Hf]
      with ⟨%mr', %mm', %mo', ⟨Hmr, Hmm, Hmo⟩, Hf, %⟨hr', hm', ho'⟩⟩
    · unfold mauths; iframe Hmr Hmm Hmo Hf
    imodintro
    isplitl [Hc Hmr Hmm Hmo]
    · iapply fullInterp_intro (M := M) _ 0 (LawfulPartialMap.get?_insert_eq rfl)
      iframe Hc
      iapply lagInterp_intro (M := M) mr' mm' mo' _ ⟨hr', hm', hokf⟩ ho' (.zero _)
      iframe Hmr Hmm Hmo
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
    isplitl [Hc Hmr Hmm Hmo]
    · iapply fullInterp_intro (M := M) _ (j + 1) (LawfulPartialMap.get?_insert_eq rfl)
      iframe Hc
      iapply lagInterp_intro (M := M) mr mm mo σ0 ⟨hr, hm, hok⟩ ho (hre.snoc hs1)
      iframe Hmr Hmm Hmo
    iapply hlat
    iapply ih (j + 1) (by omega)
    unfold ctlAt
    iframe Hj Hf HR

end

end VsaIris
