import Vsa.Sim.EnvDefSpillCommon

/-!
# `env_define` prologue: count load

This module keeps the next prologue instruction separate from the two-site entry
fragment.  Small declarations keep incremental elaboration predictable.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step)
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

