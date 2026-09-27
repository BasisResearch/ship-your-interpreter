import Vsa.Sim.ValueSites
import Vsa.Sim.DecodeTable.Batch11Part15
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch02Part08
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch03Part06
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch03Part26
import Vsa.Sim.DecodeTable.Batch04Part06
import Vsa.Sim.DecodeTable.Batch04Part13
import Vsa.Sim.DecodeTable.Batch04Part18
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch05Part12
import Vsa.Sim.DecodeTable.Batch05Part20
import Vsa.Sim.DecodeTable.Batch05Part21
import Vsa.Sim.DecodeTable.Batch05Part26
import Vsa.Sim.DecodeTable.Batch05Part27
import Vsa.Sim.DecodeTable.Batch05Part29
import Vsa.Sim.DecodeTable.Batch05Part30
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch06Part31
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part12
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch16Part01
import Vsa.Sim.Code.Env_define

/-!
# Layer 3 — per-site observational step lemmas for `env_define` (scan + update)

One `StepObs` lemma per straight-line instruction of the `env_define`
(`c/src/env.c`, @0x80002a5c) **entry prologue + scan-loop body + update path +
epilogue** — the addresses `[0x80002a5c, 0x80002b10]` EXCLUDING the control-flow
sites (`blez`/`beq`/`bnez`/`j`/`jal strcmp`/`ret`), which the Spec file steps
through its own branch/loop/call lemmas.

These are all ALU-class (`addi`/`mv`/`li`/`slli`/`add`), signed-load
(`lw`/`ld` — ALU-class post via `exec_lw`/`exec_ld`), and 8-byte store (`sd` via
`exec_sd_val`) sites, generated to the EnvNewSites template (see that file's
header for the malloc-composition method).  Byte-word/non-RVC facts carry the
`_ed` suffix (collision sweep vs. EnvNewSites' `_env`).

Reuses everything from `ValueSites`: `stepObs_alu`/`stepObs_store`,
`exec_sd_val`, `exec_lw`, `exec_ld`, `execute_itype_addi_char`,
`execute_shiftiop_slli_char`, `execute_rtype_add_char`, `writeMap8`,
`sdData_val`, the `DecodeTable.decode_*` table, and the `rX_bits_*`/`wX_bits_*`
prelude-frame read/writes.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState)
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

