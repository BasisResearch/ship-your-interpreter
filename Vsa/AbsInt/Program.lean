import Vsa.AbsInt.Sound

/-!
# Program-level soundness

The analysis of a whole program starts from `initState`, which describes the
globals frame of `initSt`. `analyze_sound` covers every top-level
completion; `bigStep_final` states the result for successful runs: every
global the final store binds has a value in the abstract value the analysis
computes for it.
-/

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

variable {A : Type} [AbsDom A]

/-- The abstract initial state describes the initial store. -/
theorem initState_sound : SGam [0] initSt.store (initState (A := A)) := by
  refine ⟨?_, fun b h => (by cases h), trivial⟩
  rw [frameAt_iff]
  refine ⟨⟨none, [("print", .native .print), ("println", .native .println),
    ("assert", .native .assert)]⟩, rfl, rfl, ?_⟩
  intro x
  simp only [initState, Scope.get_cons, vfind_cons]
  by_cases h1 : "print" = x
  · subst h1
    exact ⟨fun _ => rfl, fun v hv => by cases hv; exact ofValue_sound _⟩
  · by_cases h2 : "println" = x
    · subst h2
      simp only [h1, ↓reduceIte]
      exact ⟨fun _ => rfl, fun v hv => by cases hv; exact ofValue_sound _⟩
    · by_cases h3 : "assert" = x
      · subst h3
        simp only [h1, h2, ↓reduceIte]
        exact ⟨fun _ => rfl, fun v hv => by cases hv; exact ofValue_sound _⟩
      · simp only [h1, h2, h3, ↓reduceIte]
        rfl

/-- **Soundness for programs**: every top-level completion of `p` is covered
by the analysis. -/
theorem analyze_sound (cfg : Cfg) {p : Program} {st' : St} {status : Status}
    (h : ExecSeq initSt 0 0 p st' status) :
    SOK [0] (analyze (A := A) cfg p) status st'.store :=
  seq_sound cfg h [0] initState rfl initState_sound

/-- The final store of a successful run is described by the analysis's
normal-completion state. -/
theorem bigStep_final (cfg : Cfg) {p : Program} {st' : St}
    (h : ExecSeq initSt 0 0 p st' .normal) :
    SGam [0] st'.store (analyze (A := A) cfg p).norm :=
  analyze_sound cfg h

/-- **Values at the end of a run.** For a successful run of `p`, every global
`x` the final store binds to `v` satisfies `v ∈ γ` of the analysis's value
for `x`. -/
theorem bigStep_global (cfg : Cfg) {p : Program} {st' : St}
    (h : ExecSeq initSt 0 0 p st' .normal) {x : String} {v : Value}
    (hx : st'.store.get? 0 x = some v) :
    Gam ((analyze (A := A) cfg p).norm.lookup x).1 v :=
  (SGam.lookup rfl (bigStep_final cfg h)).1 v hx

/-- A global the analysis finds certainly bound is bound in the final store,
to a value in its abstract value. -/
theorem bigStep_global_some (cfg : Cfg) {p : Program} {st' : St}
    (h : ExecSeq initSt 0 0 p st' .normal) {x : String} {a : A}
    (hl : (analyze (A := A) cfg p).norm.lookup x = (a, false)) :
    (st'.store.get? 0 x).isSome = true ∧ ∀ v, st'.store.get? 0 x = some v → Gam a v := by
  have hs := SGam.lookup (x := x) (env := 0) rfl (bigStep_final (A := A) cfg h)
  rw [hl] at hs
  refine ⟨?_, hs.1⟩
  cases hv : st'.store.get? 0 x with
  | none => cases hs.2 hv
  | some _ => rfl

/-- A program whose normal completion the analysis finds unreachable has no
`BigStep` behaviour. -/
theorem no_bigStep_of_bot (cfg : Cfg) {p : Program}
    (hbot : (analyze (A := A) cfg p).norm.isBot = true) (out : String) :
    ¬ BigStep p out := by
  rintro ⟨st', h, _⟩
  have := SGam.isBot_false (bigStep_final (A := A) cfg h)
  rw [hbot] at this
  cases this

end Vsa.AbsInt
