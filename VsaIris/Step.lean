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

/-- `mWP Loop` (RiscvPtsto.v:2809), total, with an exit postcondition. -/
abbrev mTWP (Φ : Nat × String → IProp GF) : IProp GF :=
  WP (MachineModel.Loop M) @ Stuckness.NotStuck; ⊤ [{ Φ }]

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
  iintro H
  unfold mTWP
  iapply twp.lift_step (s := Stuckness.NotStuck) rfl
  iintro %σ₁ %ns %obs %nt Hσ
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
    iframe Hσ Hwp
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
  iintro H
  unfold mTWP
  iapply twp.lift_atomic_step (s := Stuckness.NotStuck) rfl
  iintro %σ₁ %ns %obs %nt Hσ
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
    iframe Hσ
    isplitl
    · iexists (e', out')
      iframe HΦ
      ipureintro; rfl
    iapply BigSepL.bigSepL_nil.2
    iempintro

/-- The effect of one instruction on the architectural state, relative to a
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

/-- `wp_instr` in footprint form: if in EVERY state where the footprint holds
the machine takes a step whose effect is confined to the written cells, then
owning the footprint and proving the rest of the run from the updated
footprint proves the run. Everything the caller owns outside the footprint
is framed by the wand, which is the whole point (paper §4.6). -/
theorem wp_local_step {Φ : Nat × String → IProp GF}
    (RR : List (Nat × DFrac × BitVec 64)) (MR : List (Nat × DFrac × BitVec 8))
    (RW : List (Nat × BitVec 64 × BitVec 64)) (MW : List (Nat × BitVec 8 × BitVec 8))
    (hexec : ∀ σ, FootHolds (M := M) σ RR MR RW MW →
      ∃ σ', M.step σ = .next σ' ∧ LocalStep (M := M) σ σ' RW MW) :
    footPre (GF := GF) RR MR RW MW ∗ (footPost RR MR RW MW -∗ mTWP M Φ) ⊢ mTWP M Φ := by
  unfold footPre
  iintro ⟨⟨HRR, HMR, HRW, HMW⟩, Hk⟩
  iapply wp_exec_step
  unfold mstateInterp regInterp memInterp
  iintro %σ ⟨⟨%mr, Hmr, %hmr⟩, ⟨%mm, Hmm, %hmm⟩⟩
  -- read every footprint cell against the authorities
  ihave ⟨Hmr, HRR, %hRR⟩ := ghost_map_lookup_list G.regName mr RR $$ [Hmr HRR]
  · iframe Hmr; unfold regPointsTo; iexact HRR
  ihave ⟨Hmm, HMR, %hMR⟩ := ghost_map_lookup_list G.memName mm MR $$ [Hmm HMR]
  · iframe Hmm; unfold memPointsTo; iexact HMR
  let RW' : List (Nat × DFrac × BitVec 64) := RW.map (fun p => (p.1, DFrac.own 1, p.2.1))
  let MW' : List (Nat × DFrac × BitVec 8) := MW.map (fun p => (p.1, DFrac.own 1, p.2.1))
  have hRWsep : ∀ (l : List (Nat × BitVec 64 × BitVec 64)),
      sepL (GF := GF) l (fun p => p.1 ↦ᵣ p.2.1) =
        sepL (l.map (fun p => (p.1, DFrac.own 1, p.2.1)))
          (fun p => ghost_map_elem G.regName p.2.1 p.1 p.2.2) := by
    intro l; induction l with
    | nil => rfl
    | cons x xs ih => simp only [sepL_cons, List.map_cons, ih]; rfl
  have hMWsep : ∀ (l : List (Nat × BitVec 8 × BitVec 8)),
      sepL (GF := GF) l (fun p => p.1 ↦ₘ p.2.1) =
        sepL (l.map (fun p => (p.1, DFrac.own 1, p.2.1)))
          (fun p => ghost_map_elem G.memName p.2.1 p.1 p.2.2) := by
    intro l; induction l with
    | nil => rfl
    | cons x xs ih => simp only [sepL_cons, List.map_cons, ih]; rfl
  have hRWsep' : ∀ (l : List (Nat × BitVec 64 × BitVec 64)),
      sepL (GF := GF) l (fun p => ghost_map_elem G.regName (DFrac.own 1) p.1 p.2.1) =
        sepL (l.map (fun p => (p.1, DFrac.own 1, p.2.1)))
          (fun p => ghost_map_elem G.regName p.2.1 p.1 p.2.2) := hRWsep
  have hMWsep' : ∀ (l : List (Nat × BitVec 8 × BitVec 8)),
      sepL (GF := GF) l (fun p => ghost_map_elem G.memName (DFrac.own 1) p.1 p.2.1) =
        sepL (l.map (fun p => (p.1, DFrac.own 1, p.2.1)))
          (fun p => ghost_map_elem G.memName p.2.1 p.1 p.2.2) := hMWsep
  ihave ⟨Hmr, HRW, %hRW⟩ := ghost_map_lookup_list G.regName mr RW' $$ [Hmr HRW]
  · iframe Hmr; rw [← hRWsep]; iexact HRW
  ihave ⟨Hmm, HMW, %hMW⟩ := ghost_map_lookup_list G.memName mm MW' $$ [Hmm HMW]
  · iframe Hmm; rw [← hMWsep]; iexact HMW
  have hfoot : FootHolds (M := M) σ RR MR RW MW := by
    refine ⟨fun p hp => hmr _ _ (hRR p hp), fun p hp => hmm _ _ (hMR p hp),
      fun p hp => ?_, fun p hp => ?_⟩
    · exact hmr _ _ (hRW (p.1, DFrac.own 1, p.2.1) (List.mem_map_of_mem hp))
    · exact hmm _ _ (hMW (p.1, DFrac.own 1, p.2.1) (List.mem_map_of_mem hp))
  obtain ⟨σ', hstep, hloc⟩ := hexec σ hfoot
  imodintro
  isplitr
  · ipureintro; exact ⟨σ', hstep⟩
  iintro %σ'' %hstep'
  rw [hstep] at hstep'
  cases hstep'
  imod ghost_map_update_list G.regName RW mr $$ [Hmr HRW] with ⟨%mr', Hmr, HRW, %hmr'⟩
  · iframe Hmr; rw [hRWsep']; iexact HRW
  imod ghost_map_update_list G.memName MW mm $$ [Hmm HMW] with ⟨%mm', Hmm, HMW, %hmm'⟩
  · iframe Hmm; rw [hMWsep']; iexact HMW
  imodintro
  isplitl [Hmr Hmm]
  · isplitl [Hmr]
    · iexists mr'
      iframe Hmr
      ipureintro
      intro k v hk
      rcases hmr' k v hk with ⟨p, hp, rfl, rfl⟩ | ⟨hnot, hk⟩
      · exact hloc.reg_new p hp
      · rw [hloc.reg_frame k hnot]; exact hmr k v hk
    · iexists mm'
      iframe Hmm
      ipureintro
      intro k v hk
      rcases hmm' k v hk with ⟨p, hp, rfl, rfl⟩ | ⟨hnot, hk⟩
      · exact hloc.mem_new p hp
      · rw [hloc.mem_frame k hnot]; exact hmm k v hk
  iapply Hk
  unfold footPost regPointsTo memPointsTo
  iframe HRR HMR HRW HMW

end Rules

end VsaIris
