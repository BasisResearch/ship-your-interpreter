import Iris.ProgramLogic.Language

namespace VsaIris

inductive StepResult (S : Type) where
  | next (σ' : S)
  | halt (code : Nat) (out : String)
  | stuck

def PC : Nat := 32
def ra : Nat := 1
def sp : Nat := 2
def a0 : Nat := 10

structure MachineModel where
  State : Type
  step : State → StepResult State

  reg : State → Nat → BitVec 64
  mem : State → Nat → BitVec 8

  out : State → String := fun _ => ""

  ok : State → Prop := fun _ => True

variable (M : MachineModel)

inductive ReachesN : Nat → M.State → M.State → Prop where
  | zero (σ : M.State) : ReachesN 0 σ σ
  | succ {n : Nat} {σ σ' σ'' : M.State} :
      M.step σ = .next σ' → ReachesN n σ' σ'' → ReachesN (n + 1) σ σ''

namespace ReachesN

variable {M}

theorem trans {m n : Nat} {a b c : M.State} (h₁ : ReachesN M m a b) (h₂ : ReachesN M n b c) :
    ReachesN M (m + n) a c := by
  induction h₁ with
  | zero => simpa using h₂
  | succ s _ ih => exact Nat.succ_add _ n ▸ .succ s (ih h₂)

theorem snoc {n : Nat} {a b c : M.State} (h : ReachesN M n a b) (s : M.step b = .next c) :
    ReachesN M (n + 1) a c :=
  h.trans (.succ s (.zero c))

theorem split {j k : Nat} {a b c : M.State} (hb : ReachesN M j a b)
    (hc : ReachesN M (j + k) a c) : ReachesN M k b c := by
  induction hb generalizing k with
  | zero => simpa using hc
  | @succ n σ σ' σ'' s _ ih =>
    rw [Nat.add_right_comm] at hc
    cases hc with
    | succ s' hc' =>
      rw [s] at s'
      cases s'
      exact ih hc'

theorem zero_eq {a b : M.State} (h : ReachesN M 0 a b) : a = b := by
  cases h; rfl

end ReachesN

inductive MExpr where
  | loop
  | done (code : Nat) (out : String)
  deriving DecidableEq, Inhabited

abbrev MObs := Empty

inductive MStep : MExpr × M.State → List MObs → MExpr × M.State × List MExpr → Prop where
  | next {σ σ' : M.State} : M.step σ = .next σ' → MStep (.loop, σ) [] (.loop, σ', [])
  | halt {σ : M.State} {e : Nat} {out : String} :
      M.step σ = .halt e out → MStep (.loop, σ) [] (.done e out, σ, [])

theorem MStep.src_loop {x : MExpr} {σ : M.State} {κ} {y : MExpr × M.State × List MExpr}
    (h : MStep M (x, σ) κ y) : x = .loop := by
  cases h <;> rfl

def MExpr.toVal : MExpr → Option (Nat × String)
  | .loop => none
  | .done e o => some (e, o)

structure MExprOf (M : MachineModel) where
  e : MExpr
  deriving DecidableEq

instance : Iris.ProgramLogic.ToVal (MExprOf M) (Nat × String) where
  toVal x := x.e.toVal
  ofVal v := ⟨.done v.1 v.2⟩
  coe_of_toVal_eq_some {x v} h := by
    rcases x with ⟨e⟩
    cases e with
    | loop => cases h
    | done e o => cases h; rfl
  toVal_coe _ := rfl

def primStepOf : MExprOf M × M.State → List MObs → MExprOf M × M.State × List (MExprOf M) → Prop
  | (x, σ), κ, (x', σ', efs) => efs = [] ∧ MStep M (x.e, σ) κ (x'.e, σ', [])

instance machineLang : Iris.ProgramLogic.Language (MExprOf M) M.State MObs (Nat × String) where
  primStep := primStepOf M
  val_stuck {e σ obs e' σ' eₜ} h := by
    rcases e with ⟨e⟩
    obtain ⟨_, h⟩ := h
    cases MStep.src_loop M h
    rfl

namespace MachineModel

abbrev Loop : MExprOf M := ⟨.loop⟩

theorem primStep_loop_next {σ σ' : M.State} (h : M.step σ = .next σ') :
    Iris.ProgramLogic.PrimStep.primStep ((Loop M), σ) [] ((Loop M), σ', []) :=
  ⟨rfl, .next h⟩

theorem primStep_loop_halt {σ : M.State} {e : Nat} {out : String}
    (h : M.step σ = .halt e out) :
    Iris.ProgramLogic.PrimStep.primStep ((Loop M), σ) []
      ((⟨.done e out⟩ : MExprOf M), σ, []) :=
  ⟨rfl, .halt h⟩

theorem primStep_loop_inv {σ : M.State} {κ : List MObs} {x' : MExprOf M} {σ' : M.State}
    {efs : List (MExprOf M)}
    (h : Iris.ProgramLogic.PrimStep.primStep ((Loop M), σ) κ (x', σ', efs)) :
    κ = [] ∧ efs = [] ∧
      ((∃ σn, M.step σ = .next σn ∧ x' = Loop M ∧ σ' = σn) ∨
       (∃ e out, M.step σ = .halt e out ∧ x' = ⟨.done e out⟩ ∧ σ' = σ)) := by
  obtain ⟨hefs, h⟩ := h
  rcases x' with ⟨x'⟩
  cases h with
  | next hs => exact ⟨rfl, hefs, .inl ⟨_, hs, rfl, rfl⟩⟩
  | halt hs => exact ⟨rfl, hefs, .inr ⟨_, _, hs, rfl, rfl⟩⟩

end MachineModel

end VsaIris
