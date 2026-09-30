import Vsa.Sim.EnvDefSpec4

/-!
# `env_define` spill postprocessing

Shared memory normalization and frame preservation for bounded prologue stores.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step)
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

