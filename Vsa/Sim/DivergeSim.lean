import Vsa.While.ErrorSem
import Vsa.While.Trichotomy
import Vsa.Sim.ErrorSimFull
import Vsa.Triple

/-!
# Layer 5 — the divergence forward-simulation (`divergenceSim`)

`stuck_sim` (`Vsa/Refinement.lean`) says a program with **no** clean `BigStep`
derivation never halts cleanly: the machine diverges, or exits nonzero.  The
error half (`errorSimFull`, `Vsa/Sim/ErrorSimFull.lean`) discharges the
nonzero-exit disjunct.  This file discharges the **divergence** disjunct: the
spec-side divergence witness `BigStepDiverges p := ∀ n, Approx n initSt 0 0 p`
(`Vsa/While/ErrorSem.lean`) forward-simulates to `Diverges c := ∀ n, ∃ c',
StepsN n c c'` (`Vsa/Machine.lean`).

## The shape of the argument

`Approx n st d env ss` is the fuel-indexed "still running after `n` rule steps"
relation.  It has exactly two constructors:

* `Approx.zero` — zero fuel, always still running (no machine progress required);
* `Approx.step n st d env s ss st'` — the head statement `s` runs to a *normal*
  status (`ExecS st d env s st' .normal`), and the tail `ss` is still running for
  `n` more steps (`Approx n st' d env ss`).

The load-bearing content is the successor case: each `Approx.step` witnesses one
head-statement `exec_stmt` run, which the compiled interpreter realizes in **≥ 1
architectural step** without halting.  So an `Approx n` derivation drives ≥ `n`
machine steps out of a corresponding configuration — exactly what `Diverges`
needs.

This is the STILL-RUNNING analog of `TermSimAssembly.term_sim_of_cases` /
`errorSimFull`: a fuel-recursion (structural on `Approx`, NOT well-founded) that
at each `Approx.step` consumes one head-statement run and emits ≥ 1 machine step,
landing conditional on ONE named per-step residual — "each `Approx.step` head
statement, at a corresponding machine config, reaches ≥ 1 non-halting machine
step to a config corresponding to the tail" (the progress-only analog of the M4
case Triples).

Everything is by structural induction over `Approx` + the machine's `StepsN`
algebra (`Vsa/Triple.lean`).  NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open Vsa.Machine
open Vsa.While

namespace Vsa.Sim

-- `open LeanRV64DExecutable`/`Sail` (pulled in transitively via `ErrorSimFull`)
-- shadow the bare `St`; pin the spec state explicitly, as `ErrorSimFull` does.
local notation "SpecSt" => Vsa.While.St

/-! ## §1. `StepsN` truncation — a run of length `≥ n` has a length-exactly-`n`
prefix.

`Diverges c` demands, for every `n`, a run of length *exactly* `n`.  The
per-step residual only guarantees ≥ 1 step, so the simulation naturally produces
a run of length ≥ `n`; this lemma truncates it back to the exact length the
observable behavior demands.  Pure `StepsN` algebra, by induction on `n`. -/

/-- A `StepsN m` run with `n ≤ m` has a length-exactly-`n` prefix: some `c''` is
reachable from `c` in exactly `n` steps. -/
theorem stepsN_truncate :
    ∀ {n m : Nat} {c c' : Config}, n ≤ m → StepsN m c c' →
      ∃ c'', StepsN n c c'' := by
  intro n
  induction n with
  | zero => intro m c c' _ _; exact ⟨c, .zero c⟩
  | succ n ih =>
    intro m c c' hle hm
    -- n+1 ≤ m ⇒ m = m'+1 and the run starts with a step
    cases m with
    | zero => exact absurd hle (by simp)
    | succ m =>
      cases hm with
      | succ s hrest =>
        obtain ⟨c'', hc''⟩ := ih (Nat.le_of_succ_le_succ hle) hrest
        exact ⟨c'', .succ s hc''⟩

/-! ## §2. The correspondence and the per-step residual

The simulation is parametric in a **correspondence** `Corr c st d env ss` — "the
machine configuration `c` is executing the spec configuration `(st, d, env, ss)`"
— kept abstract exactly as `Loaded`/`Layout` keeps the program-point facts
abstract in `Vsa/Refinement.lean`.  Its one obligation is the per-step
**progress residual** `DivStep`: at a corresponding config, one `Approx.step`
head-run reaches ≥ 1 non-halting machine step to a config corresponding to the
tail.  This is the progress-only (no output, no final-state) analog of the M4
case Triples / the 42 error-site residuals. -/

variable (Corr : Config → SpecSt → Nat → Addr → List Stmt → Prop)

/-- **The per-step progress residual.**  For every spec node that an
`Approx.step` can present — a head statement `s` that runs normally to `st'` with
tail `ss` — a corresponding machine config `c` reaches, in **≥ 1** architectural
step, a config `c₁` that corresponds to the tail `(st', d, env, ss)`.  The `≥ 1`
(via `1 ≤ m`) is what makes the accumulated run grow with the fuel; it is
discharged, per statement kind, by the landed `exec_stmt` case Triples
(`execExprSimC`, `execBlockSim`, `execWhileSim`, …) forgetting their output/
final-value content and keeping only the "took a step, still corresponds"
skeleton. -/
def DivStep : Prop :=
  (∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (st' : SpecSt),
    ExecS st d env s st' .normal →
    ∀ c, Corr c st d env (s :: ss) →
      ∃ m c₁, 1 ≤ m ∧ StepsN m c c₁ ∧ Corr c₁ st' d env ss) ∧
  -- 2026-08-31 amendment arm: a head statement that is INTERNALLY still-running
  -- for `n` fuel (`SApprox n`, the within-statement divergence family) drives
  -- ≥ n+1 machine steps from a corresponding config.  This is the same
  -- "every spec rule costs ≥ 1 instruction" content as the first arm, applied
  -- to the head's internal rule steps; it is the second half of the ONE named
  -- per-step residual (kept inside `DivStep` so `DivFamily`'s shape — and every
  -- downstream signature — is unchanged).
  (∀ (st : SpecSt) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt) (n : Nat),
    SApprox n st d env s →
    ∀ c, Corr c st d env (s :: ss) →
      ∃ m c₁, n + 1 ≤ m ∧ StepsN m c c₁)

/-! ## §3. The fuel recursion — `divStep_run`

The heart: from `Approx n` and a corresponding config, a machine run of length
**≥ n** exists.  Structural induction on the `Approx` derivation (its `step`
constructor already carries the strictly-smaller `Approx n` sub-derivation as
recursion fuel — no well-founded recursion needed).

* `Approx.zero`: length 0 (the empty run), `0 ≤ 0`.
* `Approx.step`: the residual `DivStep` supplies ≥ 1 step to a tail-corresponding
  config; the IH supplies ≥ n more from there; `StepsN.trans_add` composes them
  into ≥ 1 + n = n + 1. -/

/-- From an `Approx n` derivation and a corresponding machine config, some run of
length **≥ n** exists.  The counted (`TripleN`-shaped) core; `divergenceSim`
truncates to exact length. -/
theorem divStep_run (h : DivStep Corr) :
    ∀ {n : Nat} {st : SpecSt} {d : Nat} {env : Addr} {ss : List Stmt},
      Approx n st d env ss → ∀ {c : Config}, Corr c st d env ss →
        ∃ m c', n ≤ m ∧ StepsN m c c' := by
  -- `Approx` is mutually inductive post-amendment, so plain structural
  -- `induction` is unavailable; recurse on the FUEL and `cases` the derivation
  -- (`step` hands a strictly-smaller fuel to the tail; `head` consumes the
  -- residual's second arm directly, no recursion).
  intro n
  induction n with
  | zero =>
    intro st d env ss _ c _
    exact ⟨0, c, Nat.le_refl 0, .zero c⟩
  | succ n ih =>
    intro st d env ss happrox c hc
    cases happrox with
    | step _ _ _ _ s ss' st' hhead htail =>
      -- one head-statement run: ≥ 1 machine step to a tail-corresponding config
      obtain ⟨m₁, c₁, hm₁, hs₁, hc₁⟩ := h.1 st d env s ss' st' hhead c hc
      -- the tail is still running for n more: ≥ n steps from c₁
      obtain ⟨m₂, c', hm₂, hs₂⟩ := ih htail hc₁
      refine ⟨m₁ + m₂, c', ?_, hs₁.trans_add hs₂⟩
      calc n + 1 = 1 + n := by rw [Nat.add_comm]
        _ ≤ m₁ + m₂ := Nat.add_le_add hm₁ hm₂
    | head _ _ _ _ s ss' hs =>
      -- amendment arm: the head is internally still-running for n — the second
      -- half of the residual drives ≥ n+1 machine steps directly
      exact h.2 st d env s ss' n hs c hc

/-! ## §4. `divergenceSim` — the divergence forward simulation

`BigStepDiverges p = ∀ n, Approx n initSt 0 0 p`.  For every fuel `n`, feed
`divStep_run` (≥ n steps) then `stepsN_truncate` (exact n steps) to satisfy
`Diverges c = ∀ n, ∃ c', StepsN n c c'`.  Conditional only on the single named
per-step residual `DivStep` and the entry correspondence
`Corr c initSt 0 0 p`. -/

/-- **Divergence forward simulation.**  A spec-side diverging program, at a
corresponding machine entry configuration, makes the machine diverge.  The whole
argument reduces to the ONE per-step progress residual `DivStep Corr`. -/
theorem divergenceSim (h : DivStep Corr) {p : Program} {c : Config}
    (hentry : Corr c initSt 0 0 p) (hdiv : BigStepDiverges p) : Diverges c := by
  intro n
  obtain ⟨m, c', hle, hm⟩ := divStep_run Corr h (hdiv n) hentry
  exact stepsN_truncate hle hm

/-! ## §5. `stuck_of_divergenceSim` — into `stuck_sim`

`Diverges c` directly realizes `stuck_sim`'s first disjunct, via the committed
`stuck_of_diverges` (`Vsa/While/ErrorSem.lean`).  This is the divergence-arm
mirror of `stuck_of_bigStepErrFull`. -/

/-- **Discharging `stuck_sim`'s divergence disjunct.**  From the per-step residual
and the spec divergence witness, a program that runs forever lands in `stuck_sim`'s
`Diverges c` disjunct.  Composes `divergenceSim` with `stuck_of_diverges`. -/
theorem stuck_of_divergenceSim (h : DivStep Corr) {p : Program} {c : Config}
    (hentry : Corr c initSt 0 0 p) (hdiv : BigStepDiverges p) :
    Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0 :=
  Vsa.While.stuck_of_diverges (divergenceSim Corr h hentry hdiv)

/-! ## §6. `stuckSim` — the full `stuck_sim` composition

`stuck_sim = stuck_of_trichotomy ∘ (errorSim ⊕ divergenceSim)`.  Given a program
with no clean `BigStep` derivation, `stuck_of_trichotomy` (from the `Trichotomy`
obligation) splits into `BigStepErr p ∨ BigStepDiverges p`; the error arm routes
through `stuck_of_bigStepErrFull` (→ nonzero-halt disjunct), the divergence arm
through `stuck_of_divergenceSim` (→ `Diverges` disjunct).  Both arms are taken as
their *packaged* implications so the composition is independent of the 42
error-site / per-step residual lists that discharge them (recorded by name in
`errorSimFull`/`divergenceSim`).

This is the assembled `stuck_sim` structure: it type-checks iff the two forward
simulations and the trichotomy compose, and it produces exactly the disjunction
`InterpSim.stuck_sim` demands (`Vsa/Refinement.lean`). -/

/-- **The assembled `stuck_sim`.**  From the trichotomy obligation and the two
packaged forward-simulation arms — the error arm (`BigStepErr p → stuck_sim`
shape, discharged by `stuck_of_bigStepErrFull`) and the divergence arm
(`BigStepDiverges p → stuck_sim` shape, discharged by `stuck_of_divergenceSim`) —
a program with no clean `BigStep` lands in `stuck_sim`'s disjunction.  Mirrors
`Vsa.Refine.InterpSim.stuck_sim` exactly. -/
theorem stuckSim {p : Program} {c : Config}
    (htri : Vsa.While.Trichotomy)
    (herrArm : Vsa.While.BigStepErr p →
      Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0)
    (hdivArm : Vsa.While.BigStepDiverges p →
      Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0)
    (hno : ¬ ∃ out, Vsa.While.BigStep p out) :
    Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0 := by
  rcases Vsa.While.stuck_of_trichotomy htri p hno with herr | hdiv
  · exact herrArm herr
  · exact hdivArm hdiv

end Vsa.Sim
