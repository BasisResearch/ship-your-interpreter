import VsaIris.Step
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

section Adequacy

variable {GF : BundledGFunctors} [P : MachGpreS GF] {M : MachineModel}

/-- The client's obligation: from ownership of the initial registers `mr`
and bytes `mm`, prove the total WP of the loop with a pure postcondition. -/
abbrev AdequacyHyp (GF : BundledGFunctors) [MachGpreS GF] (M : MachineModel)
    (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8)) (φ : Nat × String → Prop) : Prop :=
  ∀ [_G : MachGS .hasLC GF],
    ⊢ ([∗map] k ↦ v ∈ mr, k ↦ᵣ v) -∗ ([∗map] k ↦ v ∈ mm, k ↦ₘ v) -∗
      mTWP (GF := GF) M (fun v => iprop(⌜φ v⌝))

/-- Allocate the two ghost maps and hand the client its initial ownership.
Shared by the termination and the safety halves. -/
theorem alloc_mach [InvGS_gen .hasLC GF] (σ : M.State) (mr : NatMap (BitVec 64))
    (mm : NatMap (BitVec 8)) (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) :
    ⊢@{IProp GF} |==> ∃ γr γm,
      (letI : MachGS .hasLC GF := { machPre := P.machPre, regName := γr, memName := γm }
       iprop(mstateInterp M σ ∗ ([∗map] k ↦ v ∈ mr, k ↦ᵣ v) ∗
         ([∗map] k ↦ v ∈ mm, k ↦ₘ v))) := by
  imod ghost_map_alloc (GF := GF) mr with ⟨%γr, Hr, Hrs⟩
  imod ghost_map_alloc (GF := GF) mm with ⟨%γm, Hm, Hms⟩
  imodintro
  iexists γr, γm
  unfold mstateInterp regInterp memInterp regPointsTo memPointsTo
  iframe Hrs Hms
  isplitl [Hr]
  · iexists mr; iframe Hr; ipureintro; exact hr
  · iexists mm; iframe Hm; ipureintro; exact hm

/-- Termination: the loop is strongly normalising. -/
theorem mach_sn (σ : M.State) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (φ : Nat × String → Prop)
    (H : AdequacyHyp GF M mr mm φ) :
    Relation.StronglyNormalizing Language.ErasedStep ([MachineModel.Loop M], σ) := by
  refine twp_total (hlc := .hasLC) (GF := GF) .NotStuck (MachineModel.Loop M) σ
    (fun v => iprop(⌜φ v⌝)) 0 0 ?_
  intro Hinv
  imod alloc_mach (GF := GF) σ mr mm hr hm with ⟨%γr, %γm, Hσ, Hrs, Hms⟩
  letI G : MachGS .hasLC GF := { machPre := P.machPre, regName := γr, memName := γm }
  ihave Hw := (H (_G := G)) $$ Hrs Hms
  imodintro
  iexists (fun σ _ _ _ => mstateInterp (GF := GF) M σ), (fun _ => 0), (fun _ => iprop(True)),
    (machIrisGS (hlc := .hasLC) (GF := GF) M).stateInterp_mono
  isplitl [Hσ]
  · iexact Hσ
  iintro -
  iexact Hw

/-- Safety and the postcondition at every reachable value. -/
theorem mach_adequate (σ : M.State) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (φ : Nat × String → Prop)
    (H : AdequacyHyp GF M mr mm φ) :
    adequate .NotStuck (MachineModel.Loop M) σ (fun v _ => φ v) := by
  refine wp_adequacy_gen (hlc := .hasLC) (GF := GF) .NotStuck (MachineModel.Loop M) σ φ ?_
  intro Hinv κs
  imod alloc_mach (GF := GF) σ mr mm hr hm with ⟨%γr, %γm, Hσ, Hrs, Hms⟩
  letI G : MachGS .hasLC GF := { machPre := P.machPre, regName := γr, memName := γm }
  ihave Hw := (H (_G := G)) $$ Hrs Hms
  imodintro
  iexists (fun σ _ => mstateInterp (GF := GF) M σ), (fun _ => iprop(True))
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
    (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (φ : Nat × String → Prop)
    (H : AdequacyHyp GF M mr mm φ) :
    ∃ e out, Halts M σ e out ∧ φ (e, out) :=
  halts_of_sn_adequate σ φ (mach_adequate σ mr mm hr hm φ H) _
    (mach_sn σ mr mm hr hm φ H) σ rfl .refl

end Adequacy

end VsaIris
