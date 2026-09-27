import Vsa.Sim.ExitFootprint

/-!
# `ArmTailFootprint` — `armTail_rec` for `sp`/`m0`-aware child facts

`armTail_rec_gen` (`EvalRecCommon.lean`) is the `jal eval_expr ≫ child ⇒
SubEvalReturn` glue for ANY fact `Q` retained at the child's actual return.
This file instantiates it at the `sp`/`m0`-aware child contracts of
`ExitFootprint.lean`:

* `armTail_rec_withM` — at `EvalIHWithM Extra`;
* `armTail_rec_footprint` — at `EvalIHF F`: the child's return memory has the
  footprint `F SL A (sp - 1088) subsret` relative to the call memory `mcall`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

