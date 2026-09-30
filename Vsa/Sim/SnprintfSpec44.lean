import Vsa.Sim.SnprintfSpec8
import Vsa.Sim.SnprintfSpec43

/-!
# M3 Layer-3 — `SnprintfSpec44` : `entryToPrint_neg_any_spec` — ALL negative magnitudes

`entryToPrint_neg_spec` (SnprintfSpec8) covers the negative arm for magnitudes
`> 9` (the decimal loop).  `fastToPrint_neg_spec` (SnprintfSpec43) covers the
single-digit fast path (`≤ 9`).  This module removes the magnitude hypothesis:
the SAME statement as `entryToPrint_neg_spec` (postcondition verbatim, `p = 0`
in the fast case), for **every** negative `v` — the case split on
`9 < ((0#64) - v).toNat` happens here, not in the caller.

The only new hypothesis vs Spec8 is `ArmPinsLoaded` (the `0x80008ea4` tail
block + nonneg-hop byte pins, `Code/ArmPins.lean`), which the fast path
executes through.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (__hidden___udivdi3Loaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

