import Vsa.Sim.rows.EnvDefineScanRows
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.BridgeSegFramed

/-!
# `EnvDefineScanCallOut` — the scan's argument loads and `jal strcmp`, with output

`envDefineScanCallRead64` (`EnvDefineScanRows.lean`) runs the two argument loads
at `0x80002ab0` and the `jal strcmp` at `0x80002ab8` but exports no
`sailOutput` clause, so the framed scan (`EnvDefineScanFramed.lean`) could not
carry the console output past the `strcmp` seam.  This file lands the same run
through `bridgeOfSegFull` (`BridgeSegFull.lean`), whose `SegCallFacts.output`
keeps the output, as the named-field carrier `EnvDefineScanCallOut`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)

