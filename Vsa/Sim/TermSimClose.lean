import Vsa.Sim.TermSimAssembly
import Vsa.Refinement

/-!
# Layer 7 — the CLOSE skeleton (term side): `termSimClosed`

`TermSimAssembly.term_sim_of_cases` is the nine-motive `@EvalE.rec` assembly:
given the ~50 per-constructor case Triples (the M4 residual bundle), it concludes
`mEvalE … t = EvalIH …` for an arbitrary `EvalE` derivation. This file closes the
**statement (`ExecSeq`) root** — the shape `InterpSim.term_sim` actually needs —
and bridges the resulting per-node `ExecSeq` simulation Triple to the top-level
`BigStep p out → Halts c out 0` obligation.

## Two pieces

* **`execSeq_sim_of_cases`** — the exact same 50 minor premises, but driving
  `@ExecSeq.rec` to conclude `mExecSeq … t` (the ninth motive) for an arbitrary
  `ExecSeq` derivation. Because `EvalE`/`ExecS`/`ExecSeq` are one mutual block,
  the nine motives and 50 premises are literally the same as
  `term_sim_of_cases`; only the final index/derivation and the exposed motive
  differ. This is the `ExecSeq`-rooted twin of `term_sim_of_cases`.

* **`termSimClosed`** — from (a) the 50 minor premises [the aggregated **M4
  residual bundle** — each discharged, conditionally on its own named residuals,
  by the correspondingly-named landed case lemma: `evalIntSim`…`evalFnSim`,
  `execExprSim`…`execContSim`, `execSeqNil`/`execSeqLoop`, `evalArgsNil`/
  `evalArgsCons`, `callAssertOk`/`callPrint`/`callPrintln`, and the open
  `hCallClosure`/loop-scaffold premises] and (b) ONE named **entry bridge**
  `hEntryHalts` [the M6 program-entry residual: the per-node `mExecSeq`
  simulation Triple for the whole program `p`, at the `interp_run` entry
  configuration determined by `Loaded L p c`, transported to a clean
  `Halts c out 0`], concludes exactly `InterpSim.term_sim`.

The entry bridge `hEntryHalts` is precisely the residual-unification /
program-entry-plumbing gap flagged in `TermSimAssembly`'s module doc ("`term_sim`
follows by instantiating … at the whole-program entry … once the
residual-unification interface (M6) closes"). Here it is pinned as a single
explicit hypothesis rather than left implicit.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`/`admit`.
-/

namespace Vsa.Sim.TermSimClose

open Vsa.While
open Vsa.Machine (Config Halts)
open Vsa.Refine (Layout Loaded InterpSim)

local notation "SpecSt" => Vsa.While.St

/-! ## §1. The `ExecSeq`-rooted assembly — `execSeq_sim_of_cases`

Identical hypotheses to `term_sim_of_cases`; `@ExecSeq.rec` exposes the ninth
motive `mExecSeq` at an arbitrary `ExecSeq` node. -/

/-! ## §2. `termSimClosed` — bridging the `ExecSeq` root to `Halts`

From the 50-premise M4 residual bundle (via `execSeq_sim_of_cases`) and ONE
named program-entry bridge, we obtain exactly `InterpSim.term_sim`.

The bridge `hEntryHalts` is the M6 program-entry residual: it consumes the
whole-program per-node `ExecSeq` simulation datum
`mExecSeq initSt 0 0 p st' .normal t` (the `SegEntry → SegExit` Triple for the
program body, produced from the bundle) together with `Loaded L p c` and
`st'.out = out`, and lands the clean `Halts c out 0`. It is the sole residue of
program-entry plumbing (`interp_run` prologue → statement loop → clean exit +
the layout/`Loaded` ↔ `SegEntry` unification). -/

end Vsa.Sim.TermSimClose
