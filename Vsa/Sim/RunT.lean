import Vsa.Machine

namespace Vsa.Machine

open LeanRV64DExecutable

def pcOfC (c : Config) : Option (BitVec 64) := c.σ.regs.get? Register.PC

inductive RunT : Config → List (BitVec 64) → Config → Prop where
  | refl (c : Config) : RunT c [] c
  | step {c c1 c' : Config} {p : BitVec 64} {τ : List (BitVec 64)} :
    Step c c1 → pcOfC c = some p → RunT c1 τ c' → RunT c (p :: τ) c'

theorem RunT.trans {a b c : Config} {τ1 τ2 : List (BitVec 64)} (h1 : RunT a τ1 b) (h2 : RunT b τ2 c) :
    RunT a (τ1 ++ τ2) c := by
  induction h1 with
  | refl => exact h2
  | step s hp _ ih => exact .step s hp (ih h2)

theorem RunT.stepsN {a b : Config} {τ : List (BitVec 64)} (h : RunT a τ b) : StepsN τ.length a b := by
  induction h with
  | refl c => exact .zero c
  | step s _ _ ih => exact .succ s ih

theorem RunT.steps {a b : Config} {τ : List (BitVec 64)} (h : RunT a τ b) : Steps a b := by
  induction h with
  | refl c => exact .refl c
  | step s _ _ ih => exact .head s ih

theorem RunT.single {a b : Config} {p : BitVec 64} (s : Step a b) (hp : pcOfC a = some p) :
    RunT a [p] b := .step s hp (.refl b)

end Vsa.Machine
