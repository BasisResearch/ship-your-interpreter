import Iris.ProgramLogic.Language

/-!
# The machine as an Iris language

Port of MachCSL's language instance (xv6iris `iris/RiscvLang.v`), cut down
to VSA's setting: one hart, sequential, no devices, no TSO, no interrupts.

What is kept from MachCSL:
* the expression is the *CPU loop*, not a program: `MExpr.loop` plays the role
  of `LoopE gen cpu` (RiscvLang.v:765-775), and every primitive step is one
  architectural step of the ISA model;
* the step is given by the ISA model itself (RiscvLang.v:222 `riscv_step`,
  RiscvLang.v:1604 `prim_step`), never by a hand-written instruction semantics.

What changes (DESIGN.md §"Deviations"):
* MachCSL's language has NO values (`mval := Empty_set`, RiscvLang.v:1593):
  `wp CpuLoop` is a pure safety statement about a machine that never stops.
  VSA's refinement theorem needs `Halts c out 0`, so a machine that signals
  HTIF exit steps to the value `done e out`. This is what makes the *total*
  weakest precondition meaningful here.
* The step is one whole `stepOnce` (VSA `Vsa/Machine.lean:43`), not one
  Sail-monad node (RiscvLang.v:1147 `hart_node_step`): VSA's proof already
  works at instruction granularity.

The model is abstract (`MachineModel`) so this development builds without the
Sail model; `Vsa.Machine` instantiates it with `State := Config`,
`step := stepOnce` (see DESIGN.md §"Instantiating with VSA").
-/

namespace VsaIris

/-- Result of one step of the ISA model: VSA's `Step` (`.next`), `Halted`
(`.halt e out`, the HTIF exit with the console output), or a model failure. -/
inductive StepResult (S : Type) where
  | next (σ' : S)
  | halt (code : Nat) (out : String)
  | stuck

/-- Register index 32 names the PC; 0-31 are the GPRs. MachCSL keeps PC in
the same register ghost map as the GPRs (`PC ↦ᵣ x`, InstrBytes.v:702). -/
def PC : Nat := 32
def ra : Nat := 1
def sp : Nat := 2
def a0 : Nat := 10

/-- The abstract ISA model: a deterministic step function plus total
projections of the architectural state the logic talks about. Reads are
total (`getD 0`), matching VSA's `readByte` and the patched lean-sail. -/
structure MachineModel where
  State : Type
  step : State → StepResult State
  /-- `reg σ PC` is the program counter. -/
  reg : State → Nat → BitVec 64
  mem : State → Nat → BitVec 8
  /-- Everything printed on the console so far (VSA: `Vsa.Machine.output`).
  The console ghost cell (`consoleOwn`, Ptsto.lean) agrees with it, and the
  exit value `done e out` of a halting step carries it (`HaltFact`,
  Step.lean). Defaults to the empty string for models without a console. -/
  out : State → String := fun _ => ""
  /-- A global well-formedness invariant of the states the logic reasons
  about (VSA: `GoodState`, the tick bound, GPR and code-byte presence). It is
  part of the state interpretation, so every step rule must re-establish it.
  Defaults to `True` for models that need none. -/
  ok : State → Prop := fun _ => True

variable (M : MachineModel)

/-- Exactly `n` normal steps of the model (VSA's `StepsN`). -/
inductive ReachesN : Nat → M.State → M.State → Prop where
  | zero (σ : M.State) : ReachesN 0 σ σ
  | succ {n : Nat} {σ σ' σ'' : M.State} :
      M.step σ = .next σ' → ReachesN n σ' σ'' → ReachesN (n + 1) σ σ''

namespace ReachesN

variable {M}

/-- Counted runs compose. -/
theorem trans {m n : Nat} {a b c : M.State} (h₁ : ReachesN M m a b) (h₂ : ReachesN M n b c) :
    ReachesN M (m + n) a c := by
  induction h₁ with
  | zero => simpa using h₂
  | succ s _ ih => exact Nat.succ_add _ n ▸ .succ s (ih h₂)

/-- Append one step at the end. -/
theorem snoc {n : Nat} {a b c : M.State} (h : ReachesN M n a b) (s : M.step b = .next c) :
    ReachesN M (n + 1) a c :=
  h.trans (.succ s (.zero c))

/-- Determinism: a prefix of a longer run is where the longer run passes. If
`a` reaches `b` in `j` steps and `c` in `j + k` steps, then `b` reaches `c` in
`k` steps. -/
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

/-- A run of length zero does not move. -/
theorem zero_eq {a b : M.State} (h : ReachesN M 0 a b) : a = b := by
  cases h; rfl

end ReachesN

/-- The CPU loop (`LoopE`, RiscvLang.v:774) or its terminal value. -/
inductive MExpr where
  | loop
  | done (code : Nat) (out : String)
  deriving DecidableEq, Inhabited

/-- Observations: none. MachCSL's `mobs` are device and power events
(RiscvLang.v:471), none of which exist in VSA. -/
abbrev MObs := Empty

/-- `prim_step` (RiscvLang.v:1604), hart arm only, whole-instruction steps,
no forks, no observations. -/
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

instance : Iris.ProgramLogic.ToVal MExpr (Nat × String) where
  toVal := MExpr.toVal
  ofVal v := .done v.1 v.2
  coe_of_toVal_eq_some {e v} h := by
    cases e with
    | loop => cases h
    | done e o => cases h; rfl
  toVal_coe _ := rfl

/-- The language instance (`riscv_lang`, RiscvLang.v:2254). The `State` is an
`outParam`, so the model is carried in the expression type. -/
structure MExprOf (M : MachineModel) where
  e : MExpr
  deriving DecidableEq

instance : Inhabited (MExprOf M) := ⟨⟨.loop⟩⟩

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

/-- The loop expression. -/
abbrev Loop : MExprOf M := ⟨.loop⟩

theorem primStep_loop_next {σ σ' : M.State} (h : M.step σ = .next σ') :
    Iris.ProgramLogic.PrimStep.primStep ((Loop M), σ) [] ((Loop M), σ', []) :=
  ⟨rfl, .next h⟩

theorem primStep_loop_halt {σ : M.State} {e : Nat} {out : String}
    (h : M.step σ = .halt e out) :
    Iris.ProgramLogic.PrimStep.primStep ((Loop M), σ) []
      ((⟨.done e out⟩ : MExprOf M), σ, []) :=
  ⟨rfl, .halt h⟩

/-- Inversion of a loop step: exactly the two arms. -/
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
