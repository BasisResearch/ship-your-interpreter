import Vsa.Sim.DivergeSim
import Vsa.Sim.InterpSimBundle

/-!
# `hdivFam` reduction — `DivFamily L` from a per-load divergence correspondence

`DivFamily L` (`Vsa/Sim/InterpSimBundle.lean`) is the ∀-closed divergence-arm
residual: for every loaded `(p, c)` it demands a correspondence `Corr` with its
per-step progress residual `DivStep Corr` and the entry `Corr c initSt 0 0 p`.

## What this file does — and the honest verdict

Unlike `htri`, the divergence family is **fundamentally gated on the machine
forward-simulation layer** (`hterm`'s sibling), not on spec-layer content.  The
reason is structural:

* `DivStep Corr` says "at a *corresponding* machine config, one spec statement
  step drives ≥ 1 non-halting architectural step to a config corresponding to the
  tail".  This is the STILL-RUNNING analog of the M4 term_sim case Triples
  (`execExprSimC`/`execBlockSim`/`execWhileSim`/…) — its content is the compiled
  per-statement step relation, which lives on the Sail machine, not in the WHILE
  spec.
* The entry `Corr c initSt 0 0 p` must link the *abstract* machine config `c` to
  the spec root, which is exactly the `Loaded L p c` program-load correspondence
  — again a machine-side fact.

There is therefore **no spec-only discharge**: any `Corr` we could write purely
here would either fail `DivStep` (no machine steps to exhibit) or fail the entry
(nothing ties `c` to the spec).  In particular the trivial `Corr := fun _ … =>
False` satisfies `DivStep` vacuously but makes the entry `Corr c initSt 0 0 p =
False` unprovable.

So the honest move is a **clean reduction**: expose `DivFamily L` as following
from a single named per-load residual `DivCorrFamily L` — "for every loaded
`(p, c)` there is a divergence correspondence with its per-step residual and
entry".  This is definitionally `DivFamily` itself; the value of `divFamily_of_corr`
is that it records, in one typed premise with a doc comment, the *exact* machine
obligation the endgame is gated on, and lets the capstone be driven from it.  The
per-step content is discharged by the same forward-simulation Triples that
discharge `hterm`, forgetting output/final-value and keeping only the
"took ≥ 1 step, still corresponds" skeleton (`Vsa/Sim/DivergeSim.lean` §2).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.DivFamily

open Vsa.While
open Vsa.Machine (Config Halts Diverges)
open Vsa.Refine (Layout Loaded)
open Vsa.Sim
open Vsa.Sim.InterpSimBundle (DivFamily)

local notation "SpecSt" => Vsa.While.St

/-- **The per-load divergence-correspondence residual.**  For every loaded
`(p, c)`, a correspondence `Corr` together with its per-step progress residual
`DivStep Corr` and the entry correspondence `Corr c initSt 0 0 p`.

This is the machine-side obligation the divergence arm is gated on: the
still-running forward simulation from the compiled interpreter's per-statement
step relation.  It is *definitionally* `DivFamily L`, surfaced as a single named
residual with the machine content spelled out so the capstone can consume it
directly.

It is discharged, per statement kind, by the M4 `exec_stmt` case Triples
(`execExprSimC`, `execBlockSim`, `execWhileSim`, …) restricted to their
progress-only ("≥ 1 step, still corresponds") skeleton — the same Triples that
supply `hterm`.  The entry `Corr c initSt 0 0 p` is the interpreter's program
load correspondence packaged in `Loaded L p c`. -/
def DivCorrFamily (L : Layout) : Prop :=
  ∀ (p : Program) (c : Config), Loaded L p c →
    ∃ Corr : Config → SpecSt → Nat → Addr → List Stmt → Prop,
      DivStep Corr ∧ Corr c initSt 0 0 p

/-- **`DivFamily` from the per-load correspondence residual.**  The endgame's
`hdivFam` obligation is exactly `DivCorrFamily L` — this records that equality as
a proved lemma so the capstone (`interpSimClosed_of_families`) can be fed
`DivCorrFamily L` directly.  The reduction is definitional; its content is the
naming of the single machine-side residual the divergence arm rests on. -/
theorem divFamily_of_corr (L : Layout) (h : DivCorrFamily L) : DivFamily L :=
  h

end Vsa.Sim.DivFamily
