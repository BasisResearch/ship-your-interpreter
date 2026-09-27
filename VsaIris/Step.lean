import VsaIris.Lag

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] (M : MachineModel)

abbrev mTWP (Φ : Nat × String → IProp GF) : IProp GF :=
  iprop(cpuTok -∗ WP (MachineModel.Loop M) @ Stuckness.NotStuck; ⊤ [{ Φ }])

end

section SepL

variable {GF : BundledGFunctors}

def sepL {α : Type _} : List α → (α → IProp GF) → IProp GF
  | [], _ => iprop(emp)
  | x :: xs, P => iprop(P x ∗ sepL xs P)

@[simp] theorem sepL_nil {α} (P : α → IProp GF) : sepL [] P = iprop(emp) := rfl
@[simp] theorem sepL_cons {α} (x : α) (xs : List α) (P : α → IProp GF) :
    sepL (x :: xs) P = iprop(P x ∗ sepL xs P) := rfl

instance sepL_persistent {α} (l : List α) (P : α → IProp GF)
    [h : ∀ x, Persistent (P x)] : Persistent (sepL l P) := by
  induction l with
  | nil => simp only [sepL_nil]; infer_instance
  | cons x xs ih => simp only [sepL_cons]; infer_instance

end SepL

section GhostList

variable {GF : BundledGFunctors} {V : Type} [GhostMapG GF Nat V NatMap]

theorem ghost_map_lookup_list (γ : GName) (m : NatMap V) :
    ∀ (R : List (Nat × DFrac × V)),
      ghost_map_auth (GF := GF) γ (DFrac.own 1) m ∗ sepL R (fun p => ghost_map_elem γ p.2.1 p.1 p.2.2)
      ⊢ ghost_map_auth γ (DFrac.own 1) m ∗ sepL R (fun p => ghost_map_elem γ p.2.1 p.1 p.2.2) ∗
        ⌜∀ p ∈ R, PartialMap.get? m p.1 = some p.2.2⌝
  | [] => by
    iintro ⟨Hm, HR⟩
    iframe Hm HR
    ipureintro
    intro p hp; cases hp
  | x :: xs => by
    rw [sepL_cons]
    iintro ⟨Hm, Hx, Hxs⟩
    ihave %hx := ghost_map_lookup $$ Hm Hx
    ihave ⟨Hm, Hxs, %hxs⟩ := ghost_map_lookup_list γ m xs $$ [Hm Hxs]
    · iframe Hm Hxs
    iframe Hm Hx Hxs
    ipureintro
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact hx
    · exact hxs p hp

theorem ghost_map_update_list (γ : GName) :
    ∀ (W : List (Nat × V × V)) (m : NatMap V),
      ghost_map_auth (GF := GF) γ (DFrac.own 1) m ∗ sepL W (fun p => ghost_map_elem γ (DFrac.own 1) p.1 p.2.1)
      ⊢ |==> ∃ m' : NatMap V, ghost_map_auth γ (DFrac.own 1) m' ∗
          sepL W (fun p => ghost_map_elem γ (DFrac.own 1) p.1 p.2.2) ∗
          ⌜∀ k v, PartialMap.get? m' k = some v →
              (∃ p ∈ W, p.1 = k ∧ p.2.2 = v) ∨
              ((∀ p ∈ W, p.1 ≠ k) ∧ PartialMap.get? m k = some v)⌝
  | [], m => by
    iintro ⟨Hm, _⟩
    imodintro
    iexists m
    iframe Hm
    isplitr
    · simp only [sepL_nil]; iempintro
    ipureintro
    intro k v hk
    exact .inr ⟨(fun p hp => by cases hp), hk⟩
  | x :: xs, m => by
    rw [sepL_cons, sepL_cons]
    iintro ⟨Hm, Hx, Hxs⟩
    imod ghost_map_update x.2.2 $$ Hm Hx with ⟨Hm, Hx⟩
    imod ghost_map_update_list γ xs _ $$ [Hm Hxs] with ⟨%m', Hm, Hxs, %hm'⟩
    · iframe Hm Hxs
    imodintro
    iexists m'
    iframe Hm Hx Hxs
    ipureintro
    intro k v hk
    rcases hm' k v hk with ⟨p, hp, hpk, hpv⟩ | ⟨hnot, hk1⟩
    · exact .inl ⟨p, List.mem_cons_of_mem _ hp, hpk, hpv⟩
    · by_cases hxk : x.1 = k
      · subst hxk
        rw [LawfulPartialMap.get?_insert_eq rfl] at hk1
        cases hk1
        exact .inl ⟨x, List.mem_cons_self, rfl, rfl⟩
      · rw [LawfulPartialMap.get?_insert_ne hxk] at hk1
        refine .inr ⟨fun p hp => ?_, hk1⟩
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hxk
        · exact hnot p hp

end GhostList

section Rules

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

theorem wp_exec_halt {Φ : Nat × String → IProp GF} :
    (∀ σ, mstateInterp (GF := GF) M σ ={⊤}=∗
        ⌜∃ e out, M.step σ = .halt e out⌝ ∗
        ∀ e out, ⌜M.step σ = .halt e out⌝ ={⊤}=∗ mstateInterp M σ ∗ Φ (e, out))
    ⊢ mTWP M Φ := by
  iintro H Htok
  iapply twp.lift_atomic_step (s := Stuckness.NotStuck) rfl
  iintro %σ₁ %ns %obs %nt Hσ
  ihave ⟨%c, Hc, %hc, Htok, Hσ⟩ := fullInterp_cpu (M := M) $$ Hσ Htok
  imod H $$ Hσ with ⟨%⟨e, out, hh⟩, H⟩
  imodintro
  isplitr
  · ipureintro
    exact ⟨_, _, _, MachineModel.primStep_loop_halt M hh⟩
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  obtain ⟨hκ, heₜ, (⟨σn, hn, _, _⟩ | ⟨e', out', hh', rfl, rfl⟩)⟩ :=
    MachineModel.primStep_loop_inv M Hstep
  · rw [hh] at hn; cases hn
  · subst hκ heₜ
    imod H $$ %e' %out' %hh' with ⟨Hσ, HΦ⟩
    imodintro
    isplitr
    · ipureintro; rfl
    isplitl [Hc Hσ]
    · iapply fullInterp_of_cpu (M := M) c hc $$ [Hc Hσ]
      iframe Hc Hσ
    isplitl [HΦ]
    · iexists (e', out')
      iframe HΦ
      ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2
    iempintro

structure LocalStep (σ σ' : M.State) (RW : List (Nat × BitVec 64 × BitVec 64))
    (MW : List (Nat × BitVec 8 × BitVec 8)) : Prop where
  reg_new : ∀ p ∈ RW, M.reg σ' p.1 = p.2.2
  reg_frame : ∀ k, (∀ p ∈ RW, p.1 ≠ k) → M.reg σ' k = M.reg σ k
  mem_new : ∀ p ∈ MW, M.mem σ' p.1 = p.2.2
  mem_frame : ∀ k, (∀ p ∈ MW, p.1 ≠ k) → M.mem σ' k = M.mem σ k

def footPre (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8)) :
    IProp GF :=
  iprop(sepL RR (fun p => p.1 ↦ᵣ{p.2.1} p.2.2) ∗ sepL MR (fun p => p.1 ↦ₘ{p.2.1} p.2.2) ∗
    sepL RW (fun p => p.1 ↦ᵣ p.2.1) ∗ sepL MW (fun p => p.1 ↦ₘ p.2.1))

def footPost (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8)) :
    IProp GF :=
  iprop(sepL RR (fun p => p.1 ↦ᵣ{p.2.1} p.2.2) ∗ sepL MR (fun p => p.1 ↦ₘ{p.2.1} p.2.2) ∗
    sepL RW (fun p => p.1 ↦ᵣ p.2.2) ∗ sepL MW (fun p => p.1 ↦ₘ p.2.2))

def FootHolds (σ : M.State) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (RW : List (Nat × BitVec 64 × BitVec 64))
    (MW : List (Nat × BitVec 8 × BitVec 8)) : Prop :=
  (∀ p ∈ RR, M.reg σ p.1 = p.2.2) ∧ (∀ p ∈ MR, M.mem σ p.1 = p.2.2) ∧
  (∀ p ∈ RW, M.reg σ p.1 = p.2.1) ∧ (∀ p ∈ MW, M.mem σ p.1 = p.2.1)

section FootMaps

variable {V : Type} [GhostMapG GF Nat V NatMap]

private theorem sepL_full_eq (γ : GName) {W : Type} (f : W → Nat × V) :
    ∀ (l : List W),
      sepL (GF := GF) l (fun p => ghost_map_elem γ (DFrac.own 1) (f p).1 (f p).2) =
        sepL (l.map (fun p => ((f p).1, DFrac.own 1, (f p).2)))
          (fun p => ghost_map_elem γ p.2.1 p.1 p.2.2)
  | [] => rfl
  | x :: xs => by simp only [sepL_cons, List.map_cons, sepL_full_eq γ f xs]

end FootMaps

theorem foot_lookup (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8)) :
    ghost_map_auth (GF := GF) G.regName (DFrac.own 1) mr ∗
      ghost_map_auth G.memName (DFrac.own 1) mm ∗ footPre RR MR RW MW ⊢
    ghost_map_auth G.regName (DFrac.own 1) mr ∗
      ghost_map_auth G.memName (DFrac.own 1) mm ∗ footPre RR MR RW MW ∗
      ⌜∀ σ, RegAgree M mr σ → MemAgree M mm σ → FootHolds (M := M) σ RR MR RW MW⌝ := by
  unfold footPre
  iintro ⟨Hmr, Hmm, HRR, HMR, HRW, HMW⟩
  ihave ⟨Hmr, HRR, %hRR⟩ := ghost_map_lookup_list G.regName mr RR $$ [Hmr HRR]
  · iframe Hmr; unfold regPointsTo; iexact HRR
  ihave ⟨Hmm, HMR, %hMR⟩ := ghost_map_lookup_list G.memName mm MR $$ [Hmm HMR]
  · iframe Hmm; unfold memPointsTo; iexact HMR
  have eR := sepL_full_eq (GF := GF) G.regName
    (fun p : Nat × BitVec 64 × BitVec 64 => (p.1, p.2.1)) RW
  have eM := sepL_full_eq (GF := GF) G.memName
    (fun p : Nat × BitVec 8 × BitVec 8 => (p.1, p.2.1)) MW
  ihave ⟨Hmr, HRW, %hRW⟩ := ghost_map_lookup_list G.regName mr _ $$ [Hmr HRW]
  · iframe Hmr; unfold regPointsTo; rw [← eR]; iexact HRW
  ihave ⟨Hmm, HMW, %hMW⟩ := ghost_map_lookup_list G.memName mm _ $$ [Hmm HMW]
  · iframe Hmm; unfold memPointsTo; rw [← eM]; iexact HMW
  unfold regPointsTo memPointsTo
  rw [eR, eM]
  iframe Hmr Hmm HRR HMR HRW HMW
  ipureintro
  intro σ hr hm
  refine ⟨fun p hp => hr _ _ (hRR p hp), fun p hp => hm _ _ (hMR p hp),
    fun p hp => ?_, fun p hp => ?_⟩
  · exact hr _ _ (hRW (p.1, DFrac.own 1, p.2.1) (List.mem_map_of_mem hp))
  · exact hm _ _ (hMW (p.1, DFrac.own 1, p.2.1) (List.mem_map_of_mem hp))

theorem foot_update {σ0 σf : M.State} (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hr : RegAgree M mr σ0) (hm : MemAgree M mm σ0) (hloc : LocalStep (M := M) σ0 σf RW MW) :
    ghost_map_auth (GF := GF) G.regName (DFrac.own 1) mr ∗
      ghost_map_auth G.memName (DFrac.own 1) mm ∗ footPre RR MR RW MW ⊢ |==>
    ∃ mr' mm', ghost_map_auth G.regName (DFrac.own 1) mr' ∗
      ghost_map_auth G.memName (DFrac.own 1) mm' ∗ footPost RR MR RW MW ∗
      ⌜RegAgree M mr' σf ∧ MemAgree M mm' σf⌝ := by
  unfold footPre footPost
  iintro ⟨Hmr, Hmm, HRR, HMR, HRW, HMW⟩
  imod ghost_map_update_list G.regName RW mr $$ [Hmr HRW] with ⟨%mr', Hmr, HRW, %hmr'⟩
  · iframe Hmr; unfold regPointsTo; iexact HRW
  imod ghost_map_update_list G.memName MW mm $$ [Hmm HMW] with ⟨%mm', Hmm, HMW, %hmm'⟩
  · iframe Hmm; unfold memPointsTo; iexact HMW
  imodintro
  iexists mr', mm'
  unfold regPointsTo memPointsTo
  iframe Hmr Hmm HRR HMR HRW HMW
  ipureintro
  constructor
  · intro k v hk
    rcases hmr' k v hk with ⟨p, hp, rfl, rfl⟩ | ⟨hnot, hk⟩
    · exact hloc.reg_new p hp
    · rw [hloc.reg_frame k hnot]; exact hr k v hk
  · intro k v hk
    rcases hmm' k v hk with ⟨p, hp, rfl, rfl⟩ | ⟨hnot, hk⟩
    · exact hloc.mem_new p hp
    · rw [hloc.mem_frame k hnot]; exact hm k v hk

def OutStep (σ σ' : M.State) : Option String → Prop
  | none => M.out σ' = M.out σ
  | some o => M.out σ' = M.out σ ++ o

def RunFactO (M : MachineModel) (n : Nat) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (RW : List (Nat × BitVec 64 × BitVec 64))
    (MW : List (Nat × BitVec 8 × BitVec 8)) (o : Option String) : Prop :=
  ∀ σ, M.ok σ → FootHolds (M := M) σ RR MR RW MW →
    ∃ σ', ReachesN M (n + 1) σ σ' ∧ M.ok σ' ∧ LocalStep (M := M) σ σ' RW MW ∧
      OutStep (M := M) σ σ' o

abbrev RunFact (M : MachineModel) (n : Nat) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (RW : List (Nat × BitVec 64 × BitVec 64))
    (MW : List (Nat × BitVec 8 × BitVec 8)) : Prop :=
  RunFactO M n RR MR RW MW none

theorem RunFact.lagFoot {n : Nat} {RR : List (Nat × DFrac × BitVec 64)}
    {MR : List (Nat × DFrac × BitVec 8)} {RW : List (Nat × BitVec 64 × BitVec 64)}
    {MW : List (Nat × BitVec 8 × BitVec 8)} (hexec : RunFact M n RR MR RW MW) :
    LagFoot (GF := GF) M (footPre RR MR RW MW) (fun _ => footPost RR MR RW MW)
      (fun σ => FootHolds (M := M) σ RR MR RW MW)
      (fun σ σf => LocalStep (M := M) σ σf RW MW ∧ OutStep (M := M) σ σf none) n :=
  LagFoot.ofRM (foot_lookup (M := M) · · RR MR RW MW) (fun σ hok hf => hexec σ hok hf)
    (fun mr mm _ _ hr hm hp => foot_update (M := M) mr mm RR MR RW MW hr hm hp.1)
    (fun _ _ hp => hp.2)

def HaltFact (M : MachineModel) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (e : Nat) : Prop :=
  ∀ σ, M.ok σ → FootHolds (M := M) σ RR MR [] [] → M.step σ = .halt e (M.out σ)

theorem twp_stepRule {Φ : Nat × String → IProp GF} :
    StepRule M id (WP (MachineModel.Loop M) @ Stuckness.NotStuck; ⊤ [{ Φ }]) := by
  unfold StepRule
  simp only [id]
  iintro H
  iapply twp.lift_step (s := Stuckness.NotStuck) rfl
  iintro %σ₁ %ns %obs %nt Hσ
  imod H $$ %σ₁ Hσ with ⟨%⟨σ', hσ'⟩, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, _, _, MachineModel.primStep_loop_next M hσ'⟩
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  obtain ⟨hκ, heₜ, (⟨σn, hn, he, hs⟩ | ⟨e, out, hh, _, _⟩)⟩ :=
    MachineModel.primStep_loop_inv M Hstep
  · subst hκ heₜ he hs
    imod H $$ %_ %hn with ⟨Hσ, Hwp⟩
    imod Hclose with -
    imodintro
    isplitr
    · ipureintro; rfl
    isplitl [Hσ]
    · iexact Hσ
    isplitl [Hwp]
    · iexact Hwp
    iapply BigSepL.bigSepL_nil.2
    iempintro
  · rw [hσ'] at hh; cases hh

end Rules

end VsaIris
