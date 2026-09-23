import VsaIris.MachWP
import Iris.ProgramLogic.TotalAdequacy
import Iris.ProgramLogic.Adequacy

/-!
# Adequacy

MachCSL's adequacy (xv6iris `iris/RiscvAdequacy.v`, `riscv_power_adequacy`
at :1533) concludes a *safety* property from `wp CpuLoop`: every reachable
state is not stuck and the observation trace satisfies the client's
predicate. We need VSA's `term_sim` shape instead, `Halts c out 0`
(`Vsa/Machine.lean:73`), which is a termination statement. It comes from the
total weakest precondition:

* `twp_total` (iris-lean `TotalAdequacy.lean`) gives strong normalisation of
  the loop;
* `twp.to_wp` + `wp_adequacy_gen` give not-stuck and the postcondition at
  every value reached;
* the machine is deterministic and has exactly one non-value expression, so
  the two together say the machine halts, and the exit satisfies `φ`.

The ghost-state setup (allocate the register and memory ghost maps from
finite maps that agree with the initial state) follows
`RiscvAdequacy.v:182-196` (`reg_init_map`, `reg_init_map_agree`).
-/

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Language Language.Notation

/-- `Vsa.Machine.Steps` restricted to normal steps. -/
inductive Reaches (M : MachineModel) : M.State → M.State → Prop where
  | refl (σ : M.State) : Reaches M σ σ
  | step {σ σ' σ'' : M.State} : M.step σ = .next σ' → Reaches M σ' σ'' → Reaches M σ σ''

/-- `Vsa.Machine.Halts` (`Vsa/Machine.lean:73`): the machine runs to a state
that signals HTIF exit `e` with console output `out`. -/
def Halts (M : MachineModel) (σ : M.State) (e : Nat) (out : String) : Prop :=
  ∃ σf, Reaches M σ σf ∧ M.step σf = .halt e out

/-- The functors the machine logic needs: invariants and later credits
(slots 0-3, as in HeapLang's `HeapLangS`) plus the two ghost maps. Having a
concrete instance is what makes the adequacy theorem non-vacuous. -/
def MachGF : BundledGFunctors
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨Auth.AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Nat (Agree (DiscreteO (BitVec 64))) NatMap), by infer_instance⟩
  | 5 => ⟨constOF (HeapView Nat (Agree (DiscreteO (BitVec 8))) NatMap), by infer_instance⟩
  | 6 => ⟨constOF (HeapView Nat (Agree (DiscreteO Nat)) NatMap), by infer_instance⟩
  | 7 => ⟨constOF (HeapView Nat (Agree (DiscreteO String)) NatMap), by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance instMachGpreS : MachGpreS MachGF where
  toWsatGpreS := by
    constructor
    · exists 0
    · exists 1
    · exists 2
  toLcGpreS := by
    constructor
    · exists 3
  machPre := by
    constructor
    · constructor; exists 4
    · constructor; exists 5
    · constructor; exists 6
    · constructor; exists 7

section Adequacy

variable {GF : BundledGFunctors} [P : MachGpreS GF] {M : MachineModel}

/-- The client's obligation: from ownership of the initial registers `mr`,
bytes `mm` and the console cell at the initial output `o`, prove the total WP
of the loop with a pure postcondition. -/
abbrev AdequacyHyp (GF : BundledGFunctors) [MachGpreS GF] (M : MachineModel)
    (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8)) (o : String)
    (φ : Nat × String → Prop) : Prop :=
  ∀ [_G : MachGS .hasLC GF],
    ⊢ ([∗map] k ↦ v ∈ mr, k ↦ᵣ v) -∗ ([∗map] k ↦ v ∈ mm, k ↦ₘ v) -∗ consoleOwn o -∗
      mTWP (GF := GF) M (fun v => iprop(⌜φ v⌝))

/-- Allocate the two ghost maps, the control map (lag 0) and the console
cell (at the initial output), and hand the client its initial ownership and
the CPU token. Shared by the termination and the safety halves. -/
theorem alloc_mach [InvGS_gen .hasLC GF] (σ : M.State) (mr : NatMap (BitVec 64))
    (mm : NatMap (BitVec 8)) (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (hok : M.ok σ) :
    ⊢@{IProp GF} |==> ∃ γr γm γc γo,
      (letI : MachGS .hasLC GF :=
          { machPre := P.machPre, regName := γr, memName := γm, ctlName := γc, conName := γo }
       iprop(fullInterp M σ ∗ cpuTok ∗ ([∗map] k ↦ v ∈ mr, k ↦ᵣ v) ∗
         ([∗map] k ↦ v ∈ mm, k ↦ₘ v) ∗ consoleOwn (M.out σ))) := by
  imod ghost_map_alloc (GF := GF) mr with ⟨%γr, Hr, Hrs⟩
  imod ghost_map_alloc (GF := GF) mm with ⟨%γm, Hm, Hms⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Nat) (H := NatMap) with ⟨%γc, Hc⟩
  imod ghost_map_insert (0 : Nat) (0 : Nat) (LawfulPartialMap.get?_empty _) $$ Hc with ⟨Hc, Ht⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := String) (H := NatMap) with ⟨%γo, Ho⟩
  imod ghost_map_insert (0 : Nat) (M.out σ) (LawfulPartialMap.get?_empty _) $$ Ho with ⟨Ho, Hs⟩
  imodintro
  iexists γr, γm, γc, γo
  unfold fullInterp lagInterp cpuTok ctlAt regPointsTo memPointsTo consoleOwn
  iframe Hrs Hms Ht Hs
  iexists _, 0
  iframe Hc
  isplitr
  · ipureintro; exact LawfulPartialMap.get?_insert_eq rfl
  iexists mr, mm, _
  iframe Hr Hm Ho
  ipureintro
  refine ⟨σ, ⟨hr, hm, hok⟩, fun v hv => ?_, .zero σ⟩
  rw [LawfulPartialMap.get?_insert_eq rfl] at hv
  cases hv; rfl

/-- Termination: the loop is strongly normalising. -/
theorem mach_sn (σ : M.State) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (hok : M.ok σ) (φ : Nat × String → Prop)
    (H : AdequacyHyp GF M mr mm (M.out σ) φ) :
    Relation.StronglyNormalizing Language.ErasedStep ([MachineModel.Loop M], σ) := by
  refine twp_total (hlc := .hasLC) (GF := GF) .NotStuck (MachineModel.Loop M) σ
    (fun v => iprop(⌜φ v⌝)) 0 0 ?_
  intro Hinv
  imod alloc_mach (GF := GF) σ mr mm hr hm hok with ⟨%γr, %γm, %γc, %γo, Hσ, Ht, Hrs, Hms, Hs⟩
  letI G : MachGS .hasLC GF :=
    { machPre := P.machPre, regName := γr, memName := γm, ctlName := γc, conName := γo }
  ihave Hw := (H (_G := G)) $$ Hrs Hms Hs Ht
  imodintro
  iexists (fun σ _ _ _ => fullInterp (GF := GF) M σ), (fun _ => 0), (fun _ => iprop(True)),
    (machIrisGS (hlc := .hasLC) (GF := GF) M).stateInterp_mono
  isplitl [Hσ]
  · iexact Hσ
  iintro -
  iexact Hw

/-- Safety and the postcondition at every reachable value. -/
theorem mach_adequate (σ : M.State) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (hok : M.ok σ) (φ : Nat × String → Prop)
    (H : AdequacyHyp GF M mr mm (M.out σ) φ) :
    adequate .NotStuck (MachineModel.Loop M) σ (fun v _ => φ v) := by
  refine wp_adequacy_gen (hlc := .hasLC) (GF := GF) .NotStuck (MachineModel.Loop M) σ φ ?_
  intro Hinv κs
  imod alloc_mach (GF := GF) σ mr mm hr hm hok with ⟨%γr, %γm, %γc, %γo, Hσ, Ht, Hrs, Hms, Hs⟩
  letI G : MachGS .hasLC GF :=
    { machPre := P.machPre, regName := γr, memName := γm, ctlName := γc, conName := γo }
  ihave Hw := (H (_G := G)) $$ Hrs Hms Hs Ht
  imodintro
  iexists (fun σ _ => fullInterp (GF := GF) M σ), (fun _ => iprop(True))
  isplitl [Hσ]
  · iexact Hσ
  iapply twp.to_wp
  iexact Hw

/-- From normalisation and safety to halting, using that the loop is the
only non-value expression and that a loop step is one machine step. -/
theorem halts_of_sn_adequate (σ0 : M.State) (φ : Nat × String → Prop)
    (had : adequate .NotStuck (MachineModel.Loop M) σ0 (fun v _ => φ v)) :
    ∀ x, Relation.StronglyNormalizing Language.ErasedStep x → ∀ σ,
      x = ([MachineModel.Loop M], σ) →
      ([MachineModel.Loop M], σ0) -·->ₜₚ* x →
      ∃ e out, Halts M σ e out ∧ φ (e, out) := by
  intro x hsn
  induction hsn with
  | intro x _ ih =>
    intro σ hx hreach
    subst hx
    have hns := had.adequate_not_stuck [MachineModel.Loop M] σ (MachineModel.Loop M) rfl hreach
      (List.mem_singleton_self _)
    rcases hns with hv | ⟨obs, e', σ', efs, hprim⟩
    · simp [ToVal.toVal, MExpr.toVal] at hv
    · obtain ⟨_, hefs, (⟨σn, hn, he, hs⟩ | ⟨e, out, hh, he, hs⟩)⟩ :=
        MachineModel.primStep_loop_inv M hprim
      · subst hefs he
        have hn' : M.step σ = .next σ' := hs ▸ hn
        have hstep : Language.ErasedStep ([MachineModel.Loop M], σ) ([MachineModel.Loop M], σ') :=
          ⟨obs, by simpa using Language.Step.atomic (t₁ := []) (t₂ := []) hprim⟩
        obtain ⟨e, out, ⟨σf, hre, hf⟩, hφ⟩ :=
          ih ([MachineModel.Loop M], σ') hstep σ' rfl (hreach.tail hstep)
        exact ⟨e, out, ⟨σf, .step hn' hre, hf⟩, hφ⟩
      · subst hefs he
        rw [hs] at hprim
        have hstep : Language.ErasedStep ([MachineModel.Loop M], σ) ([⟨.done e out⟩], σ) :=
          ⟨obs, by simpa using Language.Step.atomic (t₁ := []) (t₂ := []) hprim⟩
        have hφ := had.adequate_result [] σ (e, out) (hreach.tail hstep)
        exact ⟨e, out, ⟨σ, .refl σ, hh⟩, hφ⟩

/-- **Adequacy.** If the client proves the total WP of the loop from the
initial ownership, the machine halts, and its exit satisfies `φ`. With
`φ (e, out) := e = 0 ∧ out = o` this is VSA's `Halts c o 0`. -/
theorem mach_adequacy (σ : M.State) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (hok : M.ok σ) (φ : Nat × String → Prop)
    (H : AdequacyHyp GF M mr mm (M.out σ) φ) :
    ∃ e out, Halts M σ e out ∧ φ (e, out) :=
  halts_of_sn_adequate σ φ (mach_adequate σ mr mm hr hm hok φ H) _
    (mach_sn σ mr mm hr hm hok φ H) σ rfl .refl

/-! ## Partial adequacy

The safety half (INTERP_DESIGN.md §2, F1). From the partial WP of the loop
the machine is never stuck and every exit it reaches satisfies `φ`
(iris-lean `wp_adequacy_gen`, the route of `mach_adequate` without the
total-to-partial step). Determinism of the loop turns this into a dichotomy:
either an exit is reachable, and it satisfies `φ`, or every step count is
realised, i.e. the machine diverges. This is xv6iris's safety reading of
`wp CpuLoop` (`RiscvAdequacy.v:1533`, `riscv_power_adequacy`) plus the exit
postcondition. -/

/-- The client's obligation for partial adequacy: the partial WP of the loop
from the initial ownership, the console cell at the initial output `o`
included. -/
abbrev AdequacyHypP (GF : BundledGFunctors) [MachGpreS GF] (M : MachineModel)
    (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8)) (o : String)
    (φ : Nat × String → Prop) : Prop :=
  ∀ [_G : MachGS .hasLC GF],
    ⊢ ([∗map] k ↦ v ∈ mr, k ↦ᵣ v) -∗ ([∗map] k ↦ v ∈ mm, k ↦ₘ v) -∗ consoleOwn o -∗
      mWP (GF := GF) M (fun v => iprop(⌜φ v⌝))

/-- Safety and the postcondition at every reachable value, from the partial
WP. -/
theorem mach_adequateP (σ : M.State) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (hok : M.ok σ) (φ : Nat × String → Prop)
    (H : AdequacyHypP GF M mr mm (M.out σ) φ) :
    adequate .NotStuck (MachineModel.Loop M) σ (fun v _ => φ v) := by
  refine wp_adequacy_gen (hlc := .hasLC) (GF := GF) .NotStuck (MachineModel.Loop M) σ φ ?_
  intro Hinv κs
  imod alloc_mach (GF := GF) σ mr mm hr hm hok with ⟨%γr, %γm, %γc, %γo, Hσ, Ht, Hrs, Hms, Hs⟩
  letI G : MachGS .hasLC GF :=
    { machPre := P.machPre, regName := γr, memName := γm, ctlName := γc, conName := γo }
  ihave Hw := (H (_G := G)) $$ Hrs Hms Hs Ht
  imodintro
  iexists (fun σ _ => fullInterp (GF := GF) M σ), (fun _ => iprop(True))
  isplitl [Hσ]
  · iexact Hσ
  iexact Hw

/-- `Reaches` is the union of the counted runs. -/
theorem ReachesN.reaches {n : Nat} {a b : M.State} (h : ReachesN M n a b) : Reaches M a b := by
  induction h with
  | zero => exact .refl _
  | succ s _ ih => exact .step s ih

/-- A normal machine step is a thread-pool step of the loop. -/
theorem erased_next {σ σ' : M.State} (h : M.step σ = .next σ') :
    Language.ErasedStep ([MachineModel.Loop M], σ) ([MachineModel.Loop M], σ') := by
  refine ⟨[], ?_⟩
  simpa using Language.Step.atomic (t₁ := []) (t₂ := []) (MachineModel.primStep_loop_next M h)

/-- An exit step is a thread-pool step of the loop to the exit value. -/
theorem erased_halt {σ : M.State} {e : Nat} {out : String} (h : M.step σ = .halt e out) :
    Language.ErasedStep ([MachineModel.Loop M], σ) ([⟨.done e out⟩], σ) := by
  refine ⟨[], ?_⟩
  simpa using Language.Step.atomic (t₁ := []) (t₂ := []) (MachineModel.primStep_loop_halt M h)

/-- A counted run of the loop is a thread-pool run. -/
theorem erased_of_reachesN {n : Nat} {a b : M.State} (h : ReachesN M n a b) :
    ([MachineModel.Loop M], a) -·->ₜₚ* ([MachineModel.Loop M], b) := by
  induction h with
  | zero => exact .refl
  | succ s _ ih => exact .head (erased_next s) ih

/-- From safety to the dichotomy: an adequate loop either reaches an exit,
which satisfies `φ`, or runs for every step count. Classical, by the
reachability of an exit. -/
theorem diverges_or_halts_of_adequate (σ0 : M.State) (φ : Nat × String → Prop)
    (had : adequate .NotStuck (MachineModel.Loop M) σ0 (fun v _ => φ v)) :
    (∀ n, ∃ σ', ReachesN M n σ0 σ') ∨ ∃ e out, Halts M σ0 e out ∧ φ (e, out) := by
  by_cases hh : ∃ n e out σf, ReachesN M n σ0 σf ∧ M.step σf = .halt e out
  · obtain ⟨n, e, out, σf, hre, hf⟩ := hh
    exact .inr ⟨e, out, ⟨σf, hre.reaches, hf⟩,
      had.adequate_result [] σf (e, out) ((erased_of_reachesN hre).tail (erased_halt hf))⟩
  · refine .inl fun n => ?_
    induction n with
    | zero => exact ⟨σ0, .zero σ0⟩
    | succ n ih =>
      obtain ⟨σn, hn⟩ := ih
      have hns := had.adequate_not_stuck [MachineModel.Loop M] σn (MachineModel.Loop M) rfl
        (erased_of_reachesN hn) (List.mem_singleton_self _)
      rcases hns with hv | ⟨obs, e', σ', efs, hprim⟩
      · simp [ToVal.toVal, MExpr.toVal] at hv
      · obtain ⟨_, _, (⟨σs, hs, _, _⟩ | ⟨e, out, hf, _, _⟩)⟩ :=
          MachineModel.primStep_loop_inv M hprim
        · exact ⟨σs, hn.snoc hs⟩
        · exact (hh ⟨n, e, out, σn, hn, hf⟩).elim

/-- **Partial adequacy.** If the client proves the partial WP of the loop from
the initial ownership, then the machine diverges or halts with an exit
satisfying `φ`. -/
theorem mach_adequacyP (σ : M.State) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (hok : M.ok σ) (φ : Nat × String → Prop)
    (H : AdequacyHypP GF M mr mm (M.out σ) φ) :
    (∀ n, ∃ σ', ReachesN M n σ σ') ∨ ∃ e out, Halts M σ e out ∧ φ (e, out) :=
  diverges_or_halts_of_adequate σ φ (mach_adequateP σ mr mm hr hm hok φ H)

end Adequacy

end VsaIris
