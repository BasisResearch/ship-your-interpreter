import Vsa.Sim.JmpSpec
import Vsa.While.ErrorSem
import Vsa.Refinement

/-!
# Layer 5 — the error forward-simulation: `BigStepErr p → ∃ out, Halts c out 70`

This is the error half of `stuck_sim` (`Vsa/Refinement.lean`), the analog of M4's
`term_sim`.  It has two parts, both assembled here:

**Part A — `errorTailHalts` (the runtime_error → exit(70) chain).**  From a machine
configuration parked at a `jal runtime_error` site (interp_run/main frames set up,
`GoodState`, the setjmp cell populated), the machine transfers control all the way
to a clean HTIF halt with exit code `70`.  The decoded path (see
`memory/m5-stuck-sim.md`):

```
runtime_error @0x80002da8  ──runtime_error_spec──▶  interp_run setjmp-cont 0x80004428, a0=1
  ──bnez a0──▶ 0x80004508 (li s5,1; epilogue; ret a0=1)
  ──main bnez a0──▶ 0x80004600 (fprintf; li a0,70; ret)
  ──crt0 j exit──▶ _exit 0x80000180 (slli/srli/ori = (70<<<1)|1; sd a5,tohost)
  ──htif_store_exit──▶ Halted _ 70
```

`errorTailHalts` performs the reusable *composition*: it runs `runtime_error_spec`
(the big reusable transfer piece) to `0x80004428`, threads the interp_run-cont /
main / crt0 / exit spans as a single **`ErrorTailChain`** `Triple` residual (control
`0x80004428 → exit-store site`, a decode battery to be discharged), then applies the
**`ExitStoreHalts`** bridge (the exit `sd a5,tohost` → `htif_store_exit` →
`Halted _ 70` machine step — the one genuine plumbing residual) and assembles a
`Halts c out 70`.  The two big pieces it reuses by name are `runtime_error_spec`
(`Vsa/Sim/JmpSpec.lean`) and `htif_store_exit` (`Vsa/Sim/Htif.lean`, reached through
`ExitStoreHalts`).

**Part B — `errorSim` (the error forward-simulation skeleton).**  A mutual recursion
over `EvalErr`/`ExecErr`/… (mirroring `TermSimAssembly.term_sim_of_cases`'s
`@EvalE.rec` structure) whose per-constructor motive is "the compiled code reaches a
`jal runtime_error` site" — taken as per-error-site residual hypotheses, exactly as
`term_sim_of_cases` takes the case Triples.  Composed with `errorTailHalts` and
discharged into `stuck_sim`'s second disjunct via `stuck_of_halts_70`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step Steps Halted Halts output)
open Vsa.Logic
open Vsa.While
open Vsa.Sim.Code (LongjmpLoaded)

set_option maxHeartbeats 4000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- The WHILE spec state (`Vsa.While.St`), qualified to avoid the clash with the
`Vsa.Sim.St` register-bundle structure in scope from `Muldi3Spec`. -/
local notation "SpecSt" => Vsa.While.St

/-! ## Part A — the runtime_error → exit(70) chain

### A `Halts` introduction helper

`Halts c out e` unfolds to `∃ c' σf, Steps c c' ∧ Halted c' e σf ∧ output σf = out`.
Building it from a `Steps` prefix reaching a config that halts is pure `Steps`
plumbing; we package it once so the chain assembly is a one-liner. -/

/-! ### The exit-store site predicate and the two residuals

`ExitStorePre` abstracts the configuration at the `_exit` HTIF store `sd a5,tohost`
(`0x80000180`), after `crt0` has driven `a0 = 70` into `_exit` and the
`slli/srli/ori` have formed the syscall-exit word `(70<<<1)|1` in `a5`.  We keep it
opaque: the two residuals below say exactly what the chain needs of it, and a future
decode pass will instantiate it with the concrete PC/register facts. -/

/-! ### `errorTailHalts` — the assembled chain

The reusable runtime_error→halt-70 composition.  Conditional on: the
`runtime_error_spec` frame geometry (its precondition, taken as a hypothesis `hre`),
the `SnprintfContract` `SC`, the `ErrorTailChain` span `HT`, and the `ExitStoreHalts`
bridge `HX`. -/

/-! ## Part B — the error forward-simulation skeleton

The mutual recursion over the error judgment, mirroring
`TermSimAssembly.term_sim_of_cases`'s `@EvalE.rec` structure, but with error
motives.  Each error constructor's motive is "the compiled code, from the interp
entry, reaches a `jal runtime_error` site" — packaged as a `Triple` into a
`RuntimeErrorEntry` predicate (the `runtime_error_spec` precondition family).  These
per-error-site facts are taken as residual hypotheses, exactly as
`term_sim_of_cases` takes the per-case Triples.

Below is the skeleton for the `ExecSeqErr` relation (`BigStepErr = ExecSeqErr initSt
0 0 p`, `Vsa/While/ErrorSem.lean`): its two constructors (`head`: the first statement
errors; `tail`: the head runs normally and the tail errors) recursed with an
error-motive that concludes `∃ out, Halts c out 70`.  The full six-relation mutual
recursor (`@ExecSeqErr.rec` with `EvalErr`/`EvalArgsErr`/`CallErr`/`ExecErr`/
`ForLoopErr` co-motives) is the same assembly widened to all six error relations;
the `errorSim` entry composes it with `errorTailHalts`. -/

end Vsa.Sim
