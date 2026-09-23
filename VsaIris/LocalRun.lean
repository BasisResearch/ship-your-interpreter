import VsaIris.DlHeap

/-!
# Runs confined to an owned footprint

`wp_local_step` (Step.lean) is the rule for one instruction whose footprint
is a list of cells. A callee such as `malloc` runs hundreds of instructions
over a *state-dependent* set of bytes (`heapFoot L H`). This module gives
the multi-step rule over an owned register list and an owned byte set:

* `LocalRun`: a first-order description of a run, by fuel. From EVERY state
  whose owned cells hold the current values (and whose read-only cells hold
  theirs), the machine takes a normal step that changes only owned cells, and
  the run continues from the successor's values; or the run is done and the
  owned values satisfy `Q`.
* `wp_localRun`: owning the cells and handing the continuation the final
  values proves the loop's total WP. Everything else the caller owns is
  framed by the continuation wand.

The per-step confinement is necessary, not a convenience: the state
interpretation must agree with the machine at every step boundary, and a
cell owned by the caller's frame cannot be updated in the ghost map. A
Hoare triple that only frames the final state (VSA's `Triple`) does not give
this; the first-order facts below are what a callee proof must supply.
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode

/-! ## Ghost-map footprints indexed by a function -/

section GhostFn

variable {GF : BundledGFunctors} {V : Type} [GhostMapG GF Nat V NatMap]

theorem ghost_map_lookup_fn {α : Type} (γ : GName) (m : NatMap V) (k : α → Nat)
    (dq : α → DFrac) (v : α → V) :
    ∀ l : List α,
      ghost_map_auth (GF := GF) γ (DFrac.own 1) m ∗
        sepL l (fun x => ghost_map_elem γ (dq x) (k x) (v x))
      ⊢ ghost_map_auth γ (DFrac.own 1) m ∗ sepL l (fun x => ghost_map_elem γ (dq x) (k x) (v x)) ∗
        ⌜∀ x ∈ l, PartialMap.get? m (k x) = some (v x)⌝
  | [] => by
    iintro ⟨Hm, Hl⟩
    iframe Hm Hl
    ipureintro
    intro x hx; cases hx
  | y :: ys => by
    rw [sepL_cons]
    iintro ⟨Hm, Hy, Hys⟩
    ihave %hy := ghost_map_lookup $$ Hm Hy
    ihave ⟨Hm, Hys, %hys⟩ := ghost_map_lookup_fn γ m k dq v ys $$ [Hm Hys]
    · iframe Hm Hys
    iframe Hm Hy Hys
    ipureintro
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hy
    · exact hys x hx

theorem ghost_map_update_fn {α : Type} (γ : GName) (k : α → Nat) (v v' : α → V) :
    ∀ (l : List α) (m : NatMap V),
      ghost_map_auth (GF := GF) γ (DFrac.own 1) m ∗
        sepL l (fun x => ghost_map_elem γ (DFrac.own 1) (k x) (v x))
      ⊢ |==> ∃ m' : NatMap V, ghost_map_auth γ (DFrac.own 1) m' ∗
          sepL l (fun x => ghost_map_elem γ (DFrac.own 1) (k x) (v' x)) ∗
          ⌜∀ key val, PartialMap.get? m' key = some val →
              (∃ x ∈ l, k x = key ∧ v' x = val) ∨
              ((∀ x ∈ l, k x ≠ key) ∧ PartialMap.get? m key = some val)⌝
  | [], m => by
    iintro ⟨Hm, _⟩
    imodintro
    iexists m
    iframe Hm
    isplitr
    · simp only [sepL_nil]; iempintro
    ipureintro
    intro key val hk
    exact .inr ⟨(fun x hx => by cases hx), hk⟩
  | y :: ys, m => by
    rw [sepL_cons, sepL_cons]
    iintro ⟨Hm, Hy, Hys⟩
    imod ghost_map_update (v' y) $$ Hm Hy with ⟨Hm, Hy⟩
    imod ghost_map_update_fn γ k v v' ys _ $$ [Hm Hys] with ⟨%m', Hm, Hys, %hm'⟩
    · iframe Hm Hys
    imodintro
    iexists m'
    iframe Hm Hy Hys
    ipureintro
    intro key val hk
    rcases hm' key val hk with ⟨x, hx, hxk, hxv⟩ | ⟨hnot, hk1⟩
    · exact .inl ⟨x, List.mem_cons_of_mem _ hx, hxk, hxv⟩
    · by_cases hyk : k y = key
      · subst hyk
        rw [LawfulPartialMap.get?_insert_eq rfl] at hk1
        cases hk1
        exact .inl ⟨y, List.mem_cons_self, rfl, rfl⟩
      · rw [LawfulPartialMap.get?_insert_ne hyk] at hk1
        refine .inr ⟨fun x hx => ?_, hk1⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hyk
        · exact hnot x hx

end GhostFn

/-! ## Local runs -/

section Run

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- Read-only cells a run depends on: persistent register and byte points-to
(`gp`, the callee's code). -/
def roOwn (ro : List (Nat × BitVec 64)) (text : List (Nat × BitVec 8)) : IProp GF :=
  iprop(sepL ro (fun p => p.1 ↦ᵣ□ p.2) ∗ sepL text (fun p => p.1 ↦ₘ□ p.2))

instance (ro : List (Nat × BitVec 64)) (text : List (Nat × BitVec 8)) :
    Persistent (roOwn (GF := GF) ro text) := by
  unfold roOwn; infer_instance

/-- The read-only cells hold their values. -/
def ROHolds (M : MachineModel) (σ : M.State) (ro : List (Nat × BitVec 64))
    (text : List (Nat × BitVec 8)) : Prop :=
  (∀ p ∈ ro, M.reg σ p.1 = p.2) ∧ (∀ p ∈ text, M.mem σ p.1 = p.2)

/-- A run of at most `n` steps from owned register values `rv` (on `rs`) and
byte values `mv` (on `S`), every step confined to the owned cells, ending in
owned values satisfying `Q`. -/
def LocalRun (M : MachineModel) (ro : List (Nat × BitVec 64)) (text : List (Nat × BitVec 8))
    (rs : List Nat) (S : Nat → Prop) (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    Nat → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop
  | 0, rv, mv => Q rv mv
  | n + 1, rv, mv => Q rv mv ∨
      ∀ σ, ROHolds M σ ro text → (∀ r ∈ rs, M.reg σ r = rv r) → (∀ a, S a → M.mem σ a = mv a) →
        ∃ σ', M.step σ = .next σ' ∧ (∀ k, k ∉ rs → M.reg σ' k = M.reg σ k) ∧
          (∀ a, ¬ S a → M.mem σ' a = M.mem σ a) ∧
          LocalRun M ro text rs S Q n (M.reg σ') (M.mem σ')

variable {M : MachineModel}

/-- **Owned-footprint run rule.** Owning the run's registers and bytes at their
current values, with the read-only cells, and handing the continuation the
final owned values, proves the loop's total WP. -/
theorem wp_localRun {Φ : Nat × String → IProp GF} {ro : List (Nat × BitVec 64)}
    {text : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} :
    ∀ n rv mv, LocalRun M ro text rs S Q n rv mv →
      roOwn (GF := GF) ro text ∗ sepL rs (fun r => r ↦ᵣ rv r) ∗ ownSet S (fun a => a ↦ₘ mv a) ∗
        (∀ rv' mv', ⌜Q rv' mv'⌝ -∗ sepL rs (fun r => r ↦ᵣ rv' r) -∗
          ownSet S (fun a => a ↦ₘ mv' a) -∗ mTWP M Φ)
      ⊢ mTWP M Φ := by
  intro n
  induction n with
  | zero =>
    intro rv mv hQ
    iintro ⟨_, Hrs, HS, Hk⟩
    iapply Hk $$ %rv %mv %hQ Hrs HS
  | succ n ih =>
    intro rv mv hrun
    rcases hrun with hQ | hstep
    · iintro ⟨_, Hrs, HS, Hk⟩
      iapply Hk $$ %rv %mv %hQ Hrs HS
    unfold roOwn ownSet
    iintro ⟨⟨#Hro, #Htx⟩, Hrs, ⟨%l, %⟨hnd, hmem⟩, Hl⟩, Hk⟩
    iapply wp_exec_step
    unfold mstateInterp regInterp memInterp
    iintro %σ ⟨⟨%mr, Hmr, %hmr⟩, ⟨%mm, Hmm, %hmm⟩⟩
    ihave ⟨Hmr, -, %hro⟩ := ghost_map_lookup_fn G.regName mr (fun p : Nat × BitVec 64 => p.1)
      (fun _ => DFrac.discard) (fun p => p.2) ro $$ [Hmr]
    · iframe Hmr; unfold regPointsTo; iexact Hro
    ihave ⟨Hmm, -, %htx⟩ := ghost_map_lookup_fn G.memName mm (fun p : Nat × BitVec 8 => p.1)
      (fun _ => DFrac.discard) (fun p => p.2) text $$ [Hmm]
    · iframe Hmm; unfold memPointsTo; iexact Htx
    ihave ⟨Hmr, Hrs, %hrs⟩ := ghost_map_lookup_fn G.regName mr (fun r : Nat => r)
      (fun _ => DFrac.own 1) rv rs $$ [Hmr Hrs]
    · iframe Hmr; unfold regPointsTo; iexact Hrs
    ihave ⟨Hmm, Hl, %hl⟩ := ghost_map_lookup_fn G.memName mm (fun a : Nat => a)
      (fun _ => DFrac.own 1) mv l $$ [Hmm Hl]
    · iframe Hmm; unfold memPointsTo; iexact Hl
    have hRO : ROHolds M σ ro text :=
      ⟨fun p hp => hmr _ _ (hro p hp), fun p hp => hmm _ _ (htx p hp)⟩
    obtain ⟨σ', hs, hregs, hmems, hrest⟩ := hstep σ hRO
      (fun r hr => hmr _ _ (hrs r hr)) (fun a ha => hmm _ _ (hl a ((hmem a).2 ha)))
    imodintro
    isplitr
    · ipureintro; exact ⟨σ', hs⟩
    iintro %σ'' %hs'
    rw [hs] at hs'
    cases hs'
    imod ghost_map_update_fn G.regName (fun r : Nat => r) rv (M.reg σ') rs mr $$ [Hmr Hrs]
      with ⟨%mr', Hmr, Hrs, %hmr'⟩
    · iframe Hmr; iexact Hrs
    imod ghost_map_update_fn G.memName (fun a : Nat => a) mv (M.mem σ') l mm $$ [Hmm Hl]
      with ⟨%mm', Hmm, Hl, %hmm'⟩
    · iframe Hmm; iexact Hl
    imodintro
    isplitl [Hmr Hmm]
    · isplitl [Hmr]
      · iexists mr'
        iframe Hmr
        ipureintro
        intro k v hk
        rcases hmr' k v hk with ⟨x, _, rfl, rfl⟩ | ⟨hnot, hk⟩
        · rfl
        · rw [hregs k (fun hk' => hnot k hk' rfl)]; exact hmr k v hk
      · iexists mm'
        iframe Hmm
        ipureintro
        intro k v hk
        rcases hmm' k v hk with ⟨x, _, rfl, rfl⟩ | ⟨hnot, hk⟩
        · rfl
        · rw [hmems k (fun hS => hnot k ((hmem k).2 hS) rfl)]; exact hmm k v hk
    iapply ih (M.reg σ') (M.mem σ') hrest
    unfold roOwn ownSet
    isplitr
    · iframe Hro Htx
    isplitl [Hrs]
    · unfold regPointsTo; iexact Hrs
    isplitl [Hl]
    · iexists l
      isplitr
      · ipureintro; exact ⟨hnd, hmem⟩
      unfold memPointsTo; iexact Hl
    iexact Hk

end Run

end VsaIris
