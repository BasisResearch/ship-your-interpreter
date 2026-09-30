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

/-! ## §3. The fuel recursion — `divStep_run`

The heart: from `Approx n` and a corresponding config, a machine run of length
**≥ n** exists.  Structural induction on the `Approx` derivation (its `step`
constructor already carries the strictly-smaller `Approx n` sub-derivation as
recursion fuel — no well-founded recursion needed).

* `Approx.zero`: length 0 (the empty run), `0 ≤ 0`.
* `Approx.step`: the residual `DivStep` supplies ≥ 1 step to a tail-corresponding
  config; the IH supplies ≥ n more from there; `StepsN.trans_add` composes them
  into ≥ 1 + n = n + 1. -/

/-! ## §4. `divergenceSim` — the divergence forward simulation

`BigStepDiverges p = ∀ n, Approx n initSt 0 0 p`.  For every fuel `n`, feed
`divStep_run` (≥ n steps) then `stepsN_truncate` (exact n steps) to satisfy
`Diverges c = ∀ n, ∃ c', StepsN n c c'`.  Conditional only on the single named
per-step residual `DivStep` and the entry correspondence
`Corr c initSt 0 0 p`. -/

/-! ## §5. `stuck_of_divergenceSim` — into `stuck_sim`

`Diverges c` directly realizes `stuck_sim`'s first disjunct, via the committed
`stuck_of_diverges` (`Vsa/While/ErrorSem.lean`).  This is the divergence-arm
mirror of `stuck_of_bigStepErrFull`. -/

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

end Vsa.Sim
