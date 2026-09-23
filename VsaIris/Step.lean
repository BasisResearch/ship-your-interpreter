import VsaIris.Ptsto

/-!
# Stepping the machine

`mTWP M Φ` is MachCSL's `mWP Loop` (xv6iris `iris/RiscvPtsto.v:2804-2809`,
`wp_triv`), made total and given a postcondition on the exit value. MachCSL
has no postcondition because its loop never stops; here `Φ (e, out)` is what
must hold when the machine signals HTIF exit `e` having printed `out`.

The step rules follow MachCSL's layering (claude-notes/design/
execution-model.md, "WP layering"): `wp_exec_step` takes an exec witness
computed from the state (their `wp_exec_step`, "caller gives
`exec riscv_step σ = Some (tt, σ')`"); `wp_local_step` is the footprint form
every instruction leaf is stated in (their `wp_instr`), where the witness
may only depend on owned cells and the step may only change owned cells.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] (M : MachineModel)

/-- `mWP Loop` (RiscvPtsto.v:2809), total, with an exit postcondition. Its
prover receives the CPU token, which fixes the lag counter at zero
(Ptsto.lean §Lag). -/
abbrev mTWP (Φ : Nat × String → IProp GF) : IProp GF :=
  iprop(cpuTok -∗ WP (MachineModel.Loop M) @ Stuckness.NotStuck; ⊤ [{ Φ }])

end

/-! ## Separating conjunction over a list

A local big-op with a structural definition, so footprint lemmas go by plain
list induction. -/

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

/-! ## Footprint lemmas on one ghost map -/

section GhostList

variable {GF : BundledGFunctors} {V : Type} [GhostMapG GF Nat V NatMap]

/-- Reading a list of owned cells against the authoritative map; the cells
and the authority are handed back. -/
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

/-- Updating a list of fully owned cells; the new authoritative map agrees
with the old one off the written keys and takes a written value on them. -/
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

/-! ## The machine step rules -/

section Rules

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- `wp_exec_step` (execution-model.md "WP layering"): the caller proves, at
every state satisfying the state interpretation, that the machine takes a
normal step, and re-establishes the interpretation plus the rest of the run
at the successor. The fancy updates let a caller open invariants across the
step, as MachCSL's `wp_exec_step_fupd` does. -/
theorem wp_exec_step {Φ : Nat × String → IProp GF} :
    (∀ σ, mstateInterp (GF := GF) M σ ={⊤}=∗
        ⌜∃ σ', M.step σ = .next σ'⌝ ∗
        ∀ σ', ⌜M.step σ = .next σ'⌝ ={⊤}=∗ mstateInterp M σ' ∗ mTWP M Φ)
    ⊢ mTWP M Φ := by
  iintro H Htok
  iapply twp.lift_step (s := Stuckness.NotStuck) rfl
  iintro %σ₁ %ns %obs %nt Hσ
  ihave ⟨%c, Hc, %hc, Htok, Hσ⟩ := fullInterp_cpu (M := M) $$ Hσ Htok
  imod H $$ Hσ with ⟨%⟨σ', hσ'⟩, H⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, _, _, MachineModel.primStep_loop_next M hσ'⟩
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  imod Hclose with -
  obtain ⟨hκ, heₜ, (⟨σn, hn, he, hs⟩ | ⟨e, out, hh, _, _⟩)⟩ :=
    MachineModel.primStep_loop_inv M Hstep
  · subst hκ heₜ he hs
    imod H $$ %_ %hn with ⟨Hσ, Hwp⟩
    imodintro
    isplitr
    · ipureintro; rfl
    isplitl [Hc Hσ]
    · iapply fullInterp_of_cpu (M := M) c hc $$ [Hc Hσ]
      iframe Hc Hσ
    isplitl [Hwp Htok]
    · iapply Hwp $$ Htok
    iapply BigSepL.bigSepL_nil.2
    iempintro
  · rw [hσ'] at hh; cases hh

/-- The exit rule: when the machine signals HTIF exit, the postcondition
must hold at the exit value. -/
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

/-- The effect of a run on the architectural state, relative to a
footprint: the written registers `RW` and bytes `MW` take their new values,
everything else is unchanged. (MachCSL states this per instruction leaf as an
`exec` equation over `set_reg`/`write_bytes`; VSA's reflected write logs are
exactly this shape.) -/
structure LocalStep (σ σ' : M.State) (RW : List (Nat × BitVec 64 × BitVec 64))
    (MW : List (Nat × BitVec 8 × BitVec 8)) : Prop where
  reg_new : ∀ p ∈ RW, M.reg σ' p.1 = p.2.2
  reg_frame : ∀ k, (∀ p ∈ RW, p.1 ≠ k) → M.reg σ' k = M.reg σ k
  mem_new : ∀ p ∈ MW, M.mem σ' p.1 = p.2.2
  mem_frame : ∀ k, (∀ p ∈ MW, p.1 ≠ k) → M.mem σ' k = M.mem σ k

/-- Footprint ownership before a step: read-only registers `RR` and bytes
`MR` at any fraction, and written cells at their old values. -/
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

/-- The pure facts a footprint pins in any state. -/
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

/-- Reading a footprint against the two authorities: any state the
authorities agree with satisfies the footprint facts. Everything is handed
back. -/
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

/-- Committing a run's effect to the authorities: the written cells take
their new values, and the authorities move from agreeing with `σ0` to
agreeing with `σf`. -/
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

/-- The console effect of a run (INTERP_DESIGN.md §2 F2): `none` prints
nothing, `some o` appends `o` to the output. -/
def OutStep (σ σ' : M.State) : Option String → Prop
  | none => M.out σ' = M.out σ
  | some o => M.out σ' = M.out σ ++ o

/-- The hypothesis of the segment rule: from every well-formed state where
the footprint holds, the machine takes exactly `n + 1` normal steps to a
well-formed state, with an effect confined to the written cells and the
console effect `o`. -/
def RunFactO (M : MachineModel) (n : Nat) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (RW : List (Nat × BitVec 64 × BitVec 64))
    (MW : List (Nat × BitVec 8 × BitVec 8)) (o : Option String) : Prop :=
  ∀ σ, M.ok σ → FootHolds (M := M) σ RR MR RW MW →
    ∃ σ', ReachesN M (n + 1) σ σ' ∧ M.ok σ' ∧ LocalStep (M := M) σ σ' RW MW ∧
      OutStep (M := M) σ σ' o

/-- A run that prints nothing: the shape of VSA's `segEval_sound`
(`VsaIris/Vsa/Instance.lean`, `seg_runFact`), whose `sailOutput` frame is
the last conjunct. A segment that does not own the console cannot print. -/
abbrev RunFact (M : MachineModel) (n : Nat) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (RW : List (Nat × BitVec 64 × BitVec 64))
    (MW : List (Nat × BitVec 8 × BitVec 8)) : Prop :=
  RunFactO M n RR MR RW MW none

/-- The console resource a run consumes: none for a silent run, the console
cell for a printing one. -/
def conPre : Option String → String → IProp GF
  | none, _ => iprop(emp)
  | some _, s => consoleOwn s

/-- The console resource a run gives back. -/
def conPost : Option String → String → IProp GF
  | none, _ => iprop(emp)
  | some o, s => consoleOwn (s ++ o)

/-- Committing a run's console effect: a silent run keeps the console
authority; a printing run advances the console cell by what it printed. -/
theorem con_commit {σ0 σf : M.State} (mo : NatMap String) (o : Option String) (s : String)
    (ho : ConAgree M mo σ0) (hout : OutStep (M := M) σ0 σf o) :
    ghost_map_auth (GF := GF) G.conName (DFrac.own 1) mo ∗ conPre o s ⊢ |==>
      ∃ mo', ghost_map_auth G.conName (DFrac.own 1) mo' ∗ conPost o s ∗ ⌜ConAgree M mo' σf⌝ := by
  cases o with
  | none =>
    unfold conPre conPost
    iintro ⟨Ho, -⟩
    imodintro
    iexists mo
    iframe Ho
    isplitr
    · iempintro
    ipureintro
    intro v hv
    exact (show M.out σf = M.out σ0 from hout).trans (ho v hv)
  | some o =>
    unfold conPre conPost consoleOwn
    iintro ⟨Ho, Hs⟩
    ihave %hs := ghost_map_lookup $$ Ho Hs
    imod ghost_map_update (s ++ o) $$ Ho Hs with ⟨Ho, Hs⟩
    imodintro
    iexists _
    iframe Ho Hs
    ipureintro
    intro v hv
    rw [LawfulPartialMap.get?_insert_eq rfl] at hv
    cases hv
    rw [show M.out σf = M.out σ0 ++ o from hout, ho s hs]

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

/-- The segment rule's inner loop: `k + 1` steps remain, and the ghost maps
lag the machine by `j` steps. Each step reads the lag from the control cell,
re-derives the footprint facts at the lagged state, and either advances the
lag or (last step) commits the effect and resets the lag to zero. -/
theorem run_aux {Φ : Nat × String → IProp GF} {n : Nat}
    {RR : List (Nat × DFrac × BitVec 64)} {MR : List (Nat × DFrac × BitVec 8)}
    {RW : List (Nat × BitVec 64 × BitVec 64)} {MW : List (Nat × BitVec 8 × BitVec 8)}
    {o : Option String} {s : String}
    (hexec : RunFactO M n RR MR RW MW o) (k j : Nat) (hjk : j + (k + 1) = n + 1) :
    ctlAt (GF := GF) j ∗ footPre RR MR RW MW ∗ conPre o s ∗
      (footPost RR MR RW MW -∗ conPost o s -∗ mTWP M Φ) ⊢
      WP (MachineModel.Loop M) @ Stuckness.NotStuck; ⊤ [{ Φ }] := by
  iintro ⟨Hj, Hf, Hs, Hk⟩
  iapply twp.lift_step (s := Stuckness.NotStuck) rfl
  iintro %σ₁ %ns %obs %nt Hσ
  ihave ⟨%c, Hc, %hc, Hj, Hl⟩ := fullInterp_lag (M := M) $$ Hσ Hj
  unfold lagInterp ctlAt
  icases Hl with ⟨%mr, %mm, %mo, Hmr, Hmm, Hmo, %hlag⟩
  obtain ⟨σ0, ⟨hr, hm, hok⟩, ho, hre⟩ := hlag
  ihave ⟨Hmr, Hmm, Hf, %hfoot⟩ := foot_lookup (M := M) mr mm RR MR RW MW $$ [Hmr Hmm Hf]
  · iframe Hmr Hmm Hf
  obtain ⟨σf, hrun, hokf, hloc, hout⟩ := hexec σ0 hok (hfoot σ0 hr hm)
  have hrest : ReachesN M (k + 1) σ₁ σf := ReachesN.split hre (hjk ▸ hrun)
  obtain ⟨σ1, hs1, hrest1⟩ : ∃ σ1, M.step σ₁ = .next σ1 ∧ ReachesN M k σ1 σf := by
    cases hrest with
    | succ s r => exact ⟨_, s, r⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, _, _, MachineModel.primStep_loop_next M hs1⟩
  iintro %κ %e₂ %σ₂ %eₜ %Hstep
  imod Hclose with -
  obtain ⟨hκ, heₜ, (⟨σn, hn, he, hs⟩ | ⟨e, out, hh, _, _⟩)⟩ :=
    MachineModel.primStep_loop_inv M Hstep
  · subst hκ heₜ he hs
    rw [hs1] at hn
    cases hn
    rcases k with _ | k
    · -- last step: commit the effect, reset the lag
      cases hrest1.zero_eq
      imod ghost_map_update 0 $$ Hc Hj with ⟨Hc, Hj⟩
      imod foot_update (M := M) mr mm RR MR RW MW hr hm hloc $$ [Hmr Hmm Hf]
        with ⟨%mr', %mm', Hmr, Hmm, Hf, %⟨hr', hm'⟩⟩
      · iframe Hmr Hmm Hf
      imod con_commit (M := M) mo o s ho hout $$ [Hmo Hs] with ⟨%mo', Hmo, Hs, %ho'⟩
      · iframe Hmo Hs
      imodintro
      isplitr
      · ipureintro; rfl
      isplitl [Hc Hmr Hmm Hmo]
      · iapply fullInterp_intro (M := M) _ 0 (LawfulPartialMap.get?_insert_eq rfl)
        iframe Hc
        iapply lagInterp_intro (M := M) mr' mm' mo' _ ⟨hr', hm', hokf⟩ ho' (.zero _)
        iframe Hmr Hmm Hmo
      isplitl [Hk Hf Hs Hj]
      · ihave Hw := Hk $$ Hf Hs
        unfold mTWP cpuTok ctlAt
        iapply Hw $$ Hj
      iapply BigSepL.bigSepL_nil.2
      iempintro
    · -- intermediate step: advance the lag
      imod ghost_map_update (j + 1) $$ Hc Hj with ⟨Hc, Hj⟩
      imodintro
      isplitr
      · ipureintro; rfl
      isplitl [Hc Hmr Hmm Hmo]
      · iapply fullInterp_intro (M := M) _ (j + 1) (LawfulPartialMap.get?_insert_eq rfl)
        iframe Hc
        iapply lagInterp_intro (M := M) mr mm mo σ0 ⟨hr, hm, hok⟩ ho (hre.snoc hs1)
        iframe Hmr Hmm Hmo
      isplitl [Hk Hf Hs Hj]
      · iapply run_aux hexec k (j + 1) (by omega)
        unfold ctlAt
        iframe Hj Hf Hs Hk
      iapply BigSepL.bigSepL_nil.2
      iempintro
  · rw [hs1] at hh; cases hh
termination_by k

/-- **The segment rule.** If from every well-formed state satisfying the
footprint the machine runs `n + 1` steps with an effect confined to the
written cells (`RunFact`), then owning the footprint and proving the rest of
the run from the updated footprint proves the run. Everything the caller
owns outside the footprint is framed by the wand (paper §4.6). The states
between the first and the last step are never described: the ghost maps lag
behind them (Ptsto.lean §Lag). -/
theorem wp_run {Φ : Nat × String → IProp GF} (n : Nat)
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : RunFact M n RR MR RW MW) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ mTWP M Φ) ⊢ mTWP M Φ := by
  iintro ⟨Hf, Hk⟩ Htok
  iapply run_aux (o := none) (s := "") hexec n 0 (by omega)
  unfold conPre conPost
  iframe Htok Hf
  isplitr
  · iempintro
  iintro Hf -
  iapply Hk $$ Hf

/-- **The printing segment rule** (the `putc` rule, INTERP_DESIGN.md §2 F2).
A run that appends `o` to the output needs the console cell, and hands it
back advanced by `o`. The VSA instance is the HTIF tohost store
(`Inst.putc_runFact`). -/
theorem wp_runOut {Φ : Nat × String → IProp GF} (n : Nat)
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (o s : String) (hexec : RunFactO M n RR MR RW MW (some o)) :
    footPre (GF := GF) RR MR RW MW ∗ consoleOwn s ∗
      (footPost RR MR RW MW -∗ consoleOwn (s ++ o) -∗ mTWP M Φ) ⊢ mTWP M Φ := by
  iintro ⟨Hf, Hs, Hk⟩ Htok
  iapply run_aux (o := some o) (s := s) hexec n 0 (by omega)
  unfold conPre conPost
  iframe Htok Hf Hs Hk

/-- The hypothesis of the halt rule: from every well-formed state holding
the (read-only) footprint, the machine's next step is the exit with code `e`,
and the exit reports the output printed so far. VSA's instance is the HTIF
exit store (`Inst.exit_haltFact`), which leaves `sailOutput` untouched. -/
def HaltFact (M : MachineModel) (RR : List (Nat × DFrac × BitVec 64))
    (MR : List (Nat × DFrac × BitVec 8)) (e : Nat) : Prop :=
  ∀ σ, M.ok σ → FootHolds (M := M) σ RR MR [] [] → M.step σ = .halt e (M.out σ)

/-- **Halt/console agreement.** At an exit step, the exit value's output is
the console cell's contents: `Φ (e, s)` is all the postcondition must meet.
With adequacy this is `Halts c s e`, `s` read from the ghost. -/
theorem wp_halt_console {Φ : Nat × String → IProp GF}
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8)) (e : Nat)
    (s : String) (hh : HaltFact M RR MR e) :
    footPre (GF := GF) RR MR [] [] ∗ consoleOwn s ∗ Φ (e, s) ⊢ mTWP M Φ := by
  iintro ⟨Hf, Hs, HΦ⟩
  iapply wp_exec_halt
  unfold mstateInterp regInterp memInterp conInterp
  iintro %σ ⟨⟨%mr, Hmr, %hr⟩, ⟨%mm, Hmm, %hm⟩, ⟨%mo, Hmo, %ho⟩, %hok⟩
  ihave ⟨Hmr, Hmm, Hf, %hfoot⟩ := foot_lookup (M := M) mr mm RR MR [] [] $$ [Hmr Hmm Hf]
  · iframe Hmr Hmm Hf
  unfold consoleOwn
  ihave %hs := ghost_map_lookup $$ Hmo Hs
  have hstep := hh σ hok (hfoot σ hr hm)
  rw [ho s hs] at hstep
  imodintro
  isplitr
  · ipureintro; exact ⟨_, _, hstep⟩
  iintro %e' %out' %hh'
  rw [hstep] at hh'
  cases hh'
  imodintro
  iframe HΦ
  isplitl [Hmr]
  · iexists mr; iframe Hmr; ipureintro; exact hr
  isplitl [Hmm]
  · iexists mm; iframe Hmm; ipureintro; exact hm
  isplitl [Hmo]
  · iexists mo; iframe Hmo; ipureintro; exact ho
  ipureintro; exact hok

/-- `wp_instr` in footprint form: the one-step case of `wp_run`. -/
theorem wp_local_step {Φ : Nat × String → IProp GF}
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : ∀ σ, M.ok σ → FootHolds (M := M) σ RR MR RW MW →
      ∃ σ', M.step σ = .next σ' ∧ M.ok σ' ∧ LocalStep (M := M) σ σ' RW MW ∧
        M.out σ' = M.out σ) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ mTWP M Φ) ⊢ mTWP M Φ :=
  wp_run 0 RR MR RW MW fun σ hok hf => by
    obtain ⟨σ', hs, hok', hloc, hout⟩ := hexec σ hok hf
    exact ⟨σ', .succ hs (.zero σ'), hok', hloc, hout⟩

end Rules

end VsaIris
