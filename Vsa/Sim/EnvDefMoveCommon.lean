import Vsa.Sim.EnvDefSpillCommon

/-!
# `env_define` argument-move postprocessing

Compact carry predicates replace the spill-phase register bundle once the
callee-saved values have been written to the frame.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Vsa.Machine (MState Config Step)
open Vsa.Sim.Code (StrcmpLoaded)

