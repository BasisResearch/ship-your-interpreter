import VsaIris.MachWP
import Iris.ProgramLogic.TotalAdequacy
import Iris.ProgramLogic.Adequacy

namespace VsaIris

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Language Language.Notation

inductive Reaches (M : MachineModel) : M.State → M.State → Prop where
  | refl (σ : M.State) : Reaches M σ σ
  | step {σ σ' σ'' : M.State} : M.step σ = .next σ' → Reaches M σ' σ'' → Reaches M σ σ''

def Halts (M : MachineModel) (σ : M.State) (e : Nat) (out : String) : Prop :=
  ∃ σf, Reaches M σ σf ∧ M.step σf = .halt e out

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

abbrev AdequacyHyp (GF : BundledGFunctors) [MachGpreS GF] (M : MachineModel)
    (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8)) (o : String)
    (φ : Nat × String → Prop) : Prop :=
  ∀ [_G : MachGS .hasLC GF],
    ⊢ ([∗map] k ↦ v ∈ mr, k ↦ᵣ v) -∗ ([∗map] k ↦ v ∈ mm, k ↦ₘ v) -∗ consoleOwn o -∗
      mTWP (GF := GF) M (fun v => iprop(⌜φ v⌝))

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

theorem mach_adequacy (σ : M.State) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (hok : M.ok σ) (φ : Nat × String → Prop)
    (H : AdequacyHyp GF M mr mm (M.out σ) φ) :
    ∃ e out, Halts M σ e out ∧ φ (e, out) :=
  halts_of_sn_adequate σ φ (mach_adequate σ mr mm hr hm hok φ H) _
    (mach_sn σ mr mm hr hm hok φ H) σ rfl .refl

abbrev AdequacyHypP (GF : BundledGFunctors) [MachGpreS GF] (M : MachineModel)
    (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8)) (o : String)
    (φ : Nat × String → Prop) : Prop :=
  ∀ [_G : MachGS .hasLC GF],
    ⊢ ([∗map] k ↦ v ∈ mr, k ↦ᵣ v) -∗ ([∗map] k ↦ v ∈ mm, k ↦ₘ v) -∗ consoleOwn o -∗
      mWP (GF := GF) M (fun v => iprop(⌜φ v⌝))

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

theorem ReachesN.reaches {n : Nat} {a b : M.State} (h : ReachesN M n a b) : Reaches M a b := by
  induction h with
  | zero => exact .refl _
  | succ s _ ih => exact .step s ih

theorem erased_next {σ σ' : M.State} (h : M.step σ = .next σ') :
    Language.ErasedStep ([MachineModel.Loop M], σ) ([MachineModel.Loop M], σ') := by
  refine ⟨[], ?_⟩
  simpa using Language.Step.atomic (t₁ := []) (t₂ := []) (MachineModel.primStep_loop_next M h)

theorem erased_halt {σ : M.State} {e : Nat} {out : String} (h : M.step σ = .halt e out) :
    Language.ErasedStep ([MachineModel.Loop M], σ) ([⟨.done e out⟩], σ) := by
  refine ⟨[], ?_⟩
  simpa using Language.Step.atomic (t₁ := []) (t₂ := []) (MachineModel.primStep_loop_halt M h)

theorem erased_of_reachesN {n : Nat} {a b : M.State} (h : ReachesN M n a b) :
    ([MachineModel.Loop M], a) -·->ₜₚ* ([MachineModel.Loop M], b) := by
  induction h with
  | zero => exact .refl
  | succ s _ ih => exact .head (erased_next s) ih

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

theorem mach_adequacyP (σ : M.State) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree M mr σ) (hm : MemAgree M mm σ) (hok : M.ok σ) (φ : Nat × String → Prop)
    (H : AdequacyHypP GF M mr mm (M.out σ) φ) :
    (∀ n, ∃ σ', ReachesN M n σ σ') ∨ ∃ e out, Halts M σ e out ∧ φ (e, out) :=
  diverges_or_halts_of_adequate σ φ (mach_adequateP σ mr mm hr hm hok φ H)

end Adequacy

end VsaIris
