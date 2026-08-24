import Vsa.Sim.ValueSites
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

namespace Vsa.Sim

/-! ## Byte-word / non-RVC facts for the fresh `env_define` instruction words -/

theorem w_fc010113_ed : (((0xfc#8).append (0x01#8)).append (0x01#8)).append (0x13#8) = (0xfc010113#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_fc010113_ed : Sail.BitVec.extractLsb ((((0xfc#8).append (0x01#8)).append (0x01#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_01313c23_ed : (((0x01#8).append (0x31#8)).append (0x3c#8)).append (0x23#8) = (0x01313c23#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_01313c23_ed : Sail.BitVec.extractLsb ((((0x01#8).append (0x31#8)).append (0x3c#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00052983_ed : (((0x00#8).append (0x05#8)).append (0x29#8)).append (0x83#8) = (0x00052983#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00052983_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x29#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_03213023_ed : (((0x03#8).append (0x21#8)).append (0x30#8)).append (0x23#8) = (0x03213023#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_03213023_ed : Sail.BitVec.extractLsb ((((0x03#8).append (0x21#8)).append (0x30#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_01413823_ed : (((0x01#8).append (0x41#8)).append (0x38#8)).append (0x23#8) = (0x01413823#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_01413823_ed : Sail.BitVec.extractLsb ((((0x01#8).append (0x41#8)).append (0x38#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_01513423_ed : (((0x01#8).append (0x51#8)).append (0x34#8)).append (0x23#8) = (0x01513423#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_01513423_ed : Sail.BitVec.extractLsb ((((0x01#8).append (0x51#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_02113c23_ed : (((0x02#8).append (0x11#8)).append (0x3c#8)).append (0x23#8) = (0x02113c23#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_02113c23_ed : Sail.BitVec.extractLsb ((((0x02#8).append (0x11#8)).append (0x3c#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_02813823_ed : (((0x02#8).append (0x81#8)).append (0x38#8)).append (0x23#8) = (0x02813823#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_02813823_ed : Sail.BitVec.extractLsb ((((0x02#8).append (0x81#8)).append (0x38#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_02913423_ed : (((0x02#8).append (0x91#8)).append (0x34#8)).append (0x23#8) = (0x02913423#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_02913423_ed : Sail.BitVec.extractLsb ((((0x02#8).append (0x91#8)).append (0x34#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_01613023_ed : (((0x01#8).append (0x61#8)).append (0x30#8)).append (0x23#8) = (0x01613023#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_01613023_ed : Sail.BitVec.extractLsb ((((0x01#8).append (0x61#8)).append (0x30#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00050a13_ed : (((0x00#8).append (0x05#8)).append (0x0a#8)).append (0x13#8) = (0x00050a13#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00050a13_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x0a#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00058913_ed : (((0x00#8).append (0x05#8)).append (0x89#8)).append (0x13#8) = (0x00058913#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00058913_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x05#8)).append (0x89#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00060a93_ed : (((0x00#8).append (0x06#8)).append (0x0a#8)).append (0x93#8) = (0x00060a93#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00060a93_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x06#8)).append (0x0a#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00853b03_ed : (((0x00#8).append (0x85#8)).append (0x3b#8)).append (0x03#8) = (0x00853b03#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00853b03_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x85#8)).append (0x3b#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00000413_ed : (((0x00#8).append (0x00#8)).append (0x04#8)).append (0x13#8) = (0x00000413#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00000413_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x00#8)).append (0x04#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_000b0493_ed : (((0x00#8).append (0x0b#8)).append (0x04#8)).append (0x93#8) = (0x000b0493#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_000b0493_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x0b#8)).append (0x04#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00140413_ed : (((0x00#8).append (0x14#8)).append (0x04#8)).append (0x13#8) = (0x00140413#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00140413_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x14#8)).append (0x04#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00848493_ed : (((0x00#8).append (0x84#8)).append (0x84#8)).append (0x93#8) = (0x00848493#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00848493_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x84#8)).append (0x84#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_0004b503_ed : (((0x00#8).append (0x04#8)).append (0xb5#8)).append (0x03#8) = (0x0004b503#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_0004b503_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x04#8)).append (0xb5#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00090593_ed : (((0x00#8).append (0x09#8)).append (0x05#8)).append (0x93#8) = (0x00090593#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00090593_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x09#8)).append (0x05#8)).append (0x93#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_010a3783_ed : (((0x01#8).append (0x0a#8)).append (0x37#8)).append (0x83#8) = (0x010a3783#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_010a3783_ed : Sail.BitVec.extractLsb ((((0x01#8).append (0x0a#8)).append (0x37#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00141713_ed : (((0x00#8).append (0x14#8)).append (0x17#8)).append (0x13#8) = (0x00141713#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00141713_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x14#8)).append (0x17#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_000ab583_ed : (((0x00#8).append (0x0a#8)).append (0xb5#8)).append (0x83#8) = (0x000ab583#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_000ab583_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x0a#8)).append (0xb5#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_008ab603_ed : (((0x00#8).append (0x8a#8)).append (0xb6#8)).append (0x03#8) = (0x008ab603#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_008ab603_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x8a#8)).append (0xb6#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_010ab683_ed : (((0x01#8).append (0x0a#8)).append (0xb6#8)).append (0x83#8) = (0x010ab683#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_010ab683_ed : Sail.BitVec.extractLsb ((((0x01#8).append (0x0a#8)).append (0xb6#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00870733_ed : (((0x00#8).append (0x87#8)).append (0x07#8)).append (0x33#8) = (0x00870733#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00870733_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x87#8)).append (0x07#8)).append (0x33#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00371713_ed : (((0x00#8).append (0x37#8)).append (0x17#8)).append (0x13#8) = (0x00371713#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00371713_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x37#8)).append (0x17#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00e787b3_ed : (((0x00#8).append (0xe7#8)).append (0x87#8)).append (0xb3#8) = (0x00e787b3#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00e787b3_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0xe7#8)).append (0x87#8)).append (0xb3#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00b7b023_ed : (((0x00#8).append (0xb7#8)).append (0xb0#8)).append (0x23#8) = (0x00b7b023#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00b7b023_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0xb7#8)).append (0xb0#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00c7b423_ed : (((0x00#8).append (0xc7#8)).append (0xb4#8)).append (0x23#8) = (0x00c7b423#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00c7b423_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0xc7#8)).append (0xb4#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00d7b823_ed : (((0x00#8).append (0xd7#8)).append (0xb8#8)).append (0x23#8) = (0x00d7b823#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00d7b823_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0xd7#8)).append (0xb8#8)).append (0x23#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_03813083_ed : (((0x03#8).append (0x81#8)).append (0x30#8)).append (0x83#8) = (0x03813083#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_03813083_ed : Sail.BitVec.extractLsb ((((0x03#8).append (0x81#8)).append (0x30#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_03013403_ed : (((0x03#8).append (0x01#8)).append (0x34#8)).append (0x03#8) = (0x03013403#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_03013403_ed : Sail.BitVec.extractLsb ((((0x03#8).append (0x01#8)).append (0x34#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_02813483_ed : (((0x02#8).append (0x81#8)).append (0x34#8)).append (0x83#8) = (0x02813483#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_02813483_ed : Sail.BitVec.extractLsb ((((0x02#8).append (0x81#8)).append (0x34#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_02013903_ed : (((0x02#8).append (0x01#8)).append (0x39#8)).append (0x03#8) = (0x02013903#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_02013903_ed : Sail.BitVec.extractLsb ((((0x02#8).append (0x01#8)).append (0x39#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_01813983_ed : (((0x01#8).append (0x81#8)).append (0x39#8)).append (0x83#8) = (0x01813983#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_01813983_ed : Sail.BitVec.extractLsb ((((0x01#8).append (0x81#8)).append (0x39#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_01013a03_ed : (((0x01#8).append (0x01#8)).append (0x3a#8)).append (0x03#8) = (0x01013a03#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_01013a03_ed : Sail.BitVec.extractLsb ((((0x01#8).append (0x01#8)).append (0x3a#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00813a83_ed : (((0x00#8).append (0x81#8)).append (0x3a#8)).append (0x83#8) = (0x00813a83#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00813a83_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x81#8)).append (0x3a#8)).append (0x83#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_00013b03_ed : (((0x00#8).append (0x01#8)).append (0x3b#8)).append (0x03#8) = (0x00013b03#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_00013b03_ed : Sail.BitVec.extractLsb ((((0x00#8).append (0x01#8)).append (0x3b#8)).append (0x03#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide
theorem w_04010113_ed : (((0x04#8).append (0x01#8)).append (0x01#8)).append (0x13#8) = (0x04010113#32 : BitVec 32) := by apply BitVec.eq_of_toNat_eq; decide
theorem nr_04010113_ed : Sail.BitVec.extractLsb ((((0x04#8).append (0x01#8)).append (0x01#8)).append (0x13#8)) 1 0 = (0b11#2 : BitVec 2) := by apply BitVec.eq_of_toNat_eq; decide

/-- Site 0x80002a5c (`addi`): x2 := x2 + sext 0xfc0. -/
theorem site_80002a5c_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a5c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x2 (v2 + sign_extend (m := 64) (0xfc0#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a5c hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a5c#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002a5c#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002a5c#64) vminstret (0xfc010113#32)
    (instruction.ITYPE (0xfc0#12, (regidx.Regidx 0x02#5), (regidx.Regidx 0x02#5), iop.ADDI))
    Register.x2 (v2 + sign_extend (m := 64) (0xfc0#12)) (0x13#8) (0x01#8) (0x01#8) (0xfc#8)
    hG hpc hminstret w_fc010113_ed nr_fc010113_ed
    (Vsa.Sim.DecodeTable.decode_fc010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0xfc0#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) v2
      (afterNextPC (afterPrelude σ) (0x80002a5c#64))
      (sigma3_alu σ (0x80002a5c#64) Register.x2 (v2 + sign_extend (m := 64) (0xfc0#12)))
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x2 _ (v2 + sign_extend (m := 64) (0xfc0#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a60 (`sd`): store x19 (8B) @ x2+0x018. -/
theorem site_80002a60_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v19 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx19 : σ.regs.get? Register.x19 = some v19)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a60#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x018#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x018#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a60#64)).mem (v2 + sign_extend (m := 64) (0x018#12)).toNat (sdData_val v19)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a60#64)).mem (v2 + sign_extend (m := 64) (0x018#12)).toNat (sdData_val v19))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a60 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a60#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002a60#64) _ (by decide) (by decide)]; exact hx2
  have hx19₂ : (afterNextPC (afterPrelude σ) (0x80002a60#64)).regs.get? Register.x19 = some v19 := by
    rw [get?_afterNextPC σ (0x80002a60#64) _ (by decide) (by decide)]; exact hx19
  exact stepObs_store σ i u (0x80002a60#64) vminstret (0x01313c23#32)
    (instruction.STORE (0x018#12, (regidx.Regidx 0x13#5), (regidx.Regidx 0x02#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a60#64)).mem (v2 + sign_extend (m := 64) (0x018#12)).toNat (sdData_val v19))
    (0x23#8) (0x3c#8) (0x31#8) (0x01#8)
    hG hpc hminstret w_01313c23_ed nr_01313c23_ed
    (Vsa.Sim.DecodeTable.decode_01313c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a60#64) (0x018#12) (regidx.Regidx 0x13#5) (regidx.Regidx 0x02#5)
      v2 v19 hG (rX_bits_x2 _ v2 hx2₂) (rX_bits_x19 _ v19 hx19₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a64 (`lw`): x19 := sext(mem[x10+0x000]) (4B). -/
theorem site_80002a64_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a64#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x000#12)).toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x000#12)).toNat % 4 = 0)
    (hm0 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v10 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x19 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a64 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002a64#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002a64#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80002a64#64) vminstret (0x00052983#32)
    (instruction.LOAD (0x000#12, (regidx.Regidx 0x0a#5), (regidx.Regidx 0x13#5), false, 4))
    Register.x19 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))) (0x83#8) (0x29#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00052983_ed nr_00052983_ed
    (Vsa.Sim.DecodeTable.decode_00052983 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_lw σ (0x80002a64#64) (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x13#5)
      (sigma3_alu σ (0x80002a64#64) Register.x19 (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4)))) v10 b0 b1 b2 b3 hG
      (rX_bits_x10 _ v10 hx10₂) (wX_bits_x19 _ (sign_extend (m := 64) ((((b3.append b2).append b1).append b0) : BitVec (8 * 4))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a68 (`sd`): store x18 (8B) @ x2+0x020. -/
theorem site_80002a68_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v18 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx18 : σ.regs.get? Register.x18 = some v18)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a68#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x020#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x020#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a68#64)).mem (v2 + sign_extend (m := 64) (0x020#12)).toNat (sdData_val v18)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a68#64)).mem (v2 + sign_extend (m := 64) (0x020#12)).toNat (sdData_val v18))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a68 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a68#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002a68#64) _ (by decide) (by decide)]; exact hx2
  have hx18₂ : (afterNextPC (afterPrelude σ) (0x80002a68#64)).regs.get? Register.x18 = some v18 := by
    rw [get?_afterNextPC σ (0x80002a68#64) _ (by decide) (by decide)]; exact hx18
  exact stepObs_store σ i u (0x80002a68#64) vminstret (0x03213023#32)
    (instruction.STORE (0x020#12, (regidx.Regidx 0x12#5), (regidx.Regidx 0x02#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a68#64)).mem (v2 + sign_extend (m := 64) (0x020#12)).toNat (sdData_val v18))
    (0x23#8) (0x30#8) (0x21#8) (0x03#8)
    hG hpc hminstret w_03213023_ed nr_03213023_ed
    (Vsa.Sim.DecodeTable.decode_03213023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a68#64) (0x020#12) (regidx.Regidx 0x12#5) (regidx.Regidx 0x02#5)
      v2 v18 hG (rX_bits_x2 _ v2 hx2₂) (rX_bits_x18 _ v18 hx18₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a6c (`sd`): store x20 (8B) @ x2+0x010. -/
theorem site_80002a6c_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v20 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a6c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x010#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x010#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a6c#64)).mem (v2 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val v20)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a6c#64)).mem (v2 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val v20))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a6c hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a6c#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002a6c#64) _ (by decide) (by decide)]; exact hx2
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x80002a6c#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x80002a6c#64) _ (by decide) (by decide)]; exact hx20
  exact stepObs_store σ i u (0x80002a6c#64) vminstret (0x01413823#32)
    (instruction.STORE (0x010#12, (regidx.Regidx 0x14#5), (regidx.Regidx 0x02#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a6c#64)).mem (v2 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val v20))
    (0x23#8) (0x38#8) (0x41#8) (0x01#8)
    hG hpc hminstret w_01413823_ed nr_01413823_ed
    (Vsa.Sim.DecodeTable.decode_01413823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a6c#64) (0x010#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x02#5)
      v2 v20 hG (rX_bits_x2 _ v2 hx2₂) (rX_bits_x20 _ v20 hx20₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a70 (`sd`): store x21 (8B) @ x2+0x008. -/
theorem site_80002a70_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v21 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx21 : σ.regs.get? Register.x21 = some v21)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a70#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a70#64)).mem (v2 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v21)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a70#64)).mem (v2 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v21))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a70 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a70#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002a70#64) _ (by decide) (by decide)]; exact hx2
  have hx21₂ : (afterNextPC (afterPrelude σ) (0x80002a70#64)).regs.get? Register.x21 = some v21 := by
    rw [get?_afterNextPC σ (0x80002a70#64) _ (by decide) (by decide)]; exact hx21
  exact stepObs_store σ i u (0x80002a70#64) vminstret (0x01513423#32)
    (instruction.STORE (0x008#12, (regidx.Regidx 0x15#5), (regidx.Regidx 0x02#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a70#64)).mem (v2 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v21))
    (0x23#8) (0x34#8) (0x51#8) (0x01#8)
    hG hpc hminstret w_01513423_ed nr_01513423_ed
    (Vsa.Sim.DecodeTable.decode_01513423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a70#64) (0x008#12) (regidx.Regidx 0x15#5) (regidx.Regidx 0x02#5)
      v2 v21 hG (rX_bits_x2 _ v2 hx2₂) (rX_bits_x21 _ v21 hx21₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a74 (`sd`): store x1 (8B) @ x2+0x038. -/
theorem site_80002a74_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v1 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx1 : σ.regs.get? Register.x1 = some v1)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a74#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x038#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x038#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a74#64)).mem (v2 + sign_extend (m := 64) (0x038#12)).toNat (sdData_val v1)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a74#64)).mem (v2 + sign_extend (m := 64) (0x038#12)).toNat (sdData_val v1))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a74 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a74#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002a74#64) _ (by decide) (by decide)]; exact hx2
  have hx1₂ : (afterNextPC (afterPrelude σ) (0x80002a74#64)).regs.get? Register.x1 = some v1 := by
    rw [get?_afterNextPC σ (0x80002a74#64) _ (by decide) (by decide)]; exact hx1
  exact stepObs_store σ i u (0x80002a74#64) vminstret (0x02113c23#32)
    (instruction.STORE (0x038#12, (regidx.Regidx 0x01#5), (regidx.Regidx 0x02#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a74#64)).mem (v2 + sign_extend (m := 64) (0x038#12)).toNat (sdData_val v1))
    (0x23#8) (0x3c#8) (0x11#8) (0x02#8)
    hG hpc hminstret w_02113c23_ed nr_02113c23_ed
    (Vsa.Sim.DecodeTable.decode_02113c23 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a74#64) (0x038#12) (regidx.Regidx 0x01#5) (regidx.Regidx 0x02#5)
      v2 v1 hG (rX_bits_x2 _ v2 hx2₂) (rX_bits_x1 _ v1 hx1₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a78 (`sd`): store x8 (8B) @ x2+0x030. -/
theorem site_80002a78_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a78#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x030#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x030#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a78#64)).mem (v2 + sign_extend (m := 64) (0x030#12)).toNat (sdData_val v8)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a78#64)).mem (v2 + sign_extend (m := 64) (0x030#12)).toNat (sdData_val v8))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a78 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a78#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002a78#64) _ (by decide) (by decide)]; exact hx2
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002a78#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002a78#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_store σ i u (0x80002a78#64) vminstret (0x02813823#32)
    (instruction.STORE (0x030#12, (regidx.Regidx 0x08#5), (regidx.Regidx 0x02#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a78#64)).mem (v2 + sign_extend (m := 64) (0x030#12)).toNat (sdData_val v8))
    (0x23#8) (0x38#8) (0x81#8) (0x02#8)
    hG hpc hminstret w_02813823_ed nr_02813823_ed
    (Vsa.Sim.DecodeTable.decode_02813823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a78#64) (0x030#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x02#5)
      v2 v8 hG (rX_bits_x2 _ v2 hx2₂) (rX_bits_x8 _ v8 hx8₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a7c (`sd`): store x9 (8B) @ x2+0x028. -/
theorem site_80002a7c_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a7c#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x028#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x028#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a7c#64)).mem (v2 + sign_extend (m := 64) (0x028#12)).toNat (sdData_val v9)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a7c#64)).mem (v2 + sign_extend (m := 64) (0x028#12)).toNat (sdData_val v9))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a7c hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a7c#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002a7c#64) _ (by decide) (by decide)]; exact hx2
  have hx9₂ : (afterNextPC (afterPrelude σ) (0x80002a7c#64)).regs.get? Register.x9 = some v9 := by
    rw [get?_afterNextPC σ (0x80002a7c#64) _ (by decide) (by decide)]; exact hx9
  exact stepObs_store σ i u (0x80002a7c#64) vminstret (0x02913423#32)
    (instruction.STORE (0x028#12, (regidx.Regidx 0x09#5), (regidx.Regidx 0x02#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a7c#64)).mem (v2 + sign_extend (m := 64) (0x028#12)).toNat (sdData_val v9))
    (0x23#8) (0x34#8) (0x91#8) (0x02#8)
    hG hpc hminstret w_02913423_ed nr_02913423_ed
    (Vsa.Sim.DecodeTable.decode_02913423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a7c#64) (0x028#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x02#5)
      v2 v9 hG (rX_bits_x2 _ v2 hx2₂) (rX_bits_x9 _ v9 hx9₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a80 (`sd`): store x22 (8B) @ x2+0x000. -/
theorem site_80002a80_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 v22 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hx22 : σ.regs.get? Register.x22 = some v22)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a80#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a80#64)).mem (v2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v22)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a80#64)).mem (v2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v22))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a80 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002a80#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002a80#64) _ (by decide) (by decide)]; exact hx2
  have hx22₂ : (afterNextPC (afterPrelude σ) (0x80002a80#64)).regs.get? Register.x22 = some v22 := by
    rw [get?_afterNextPC σ (0x80002a80#64) _ (by decide) (by decide)]; exact hx22
  exact stepObs_store σ i u (0x80002a80#64) vminstret (0x01613023#32)
    (instruction.STORE (0x000#12, (regidx.Regidx 0x16#5), (regidx.Regidx 0x02#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002a80#64)).mem (v2 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v22))
    (0x23#8) (0x30#8) (0x61#8) (0x01#8)
    hG hpc hminstret w_01613023_ed nr_01613023_ed
    (Vsa.Sim.DecodeTable.decode_01613023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002a80#64) (0x000#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x02#5)
      v2 v22 hG (rX_bits_x2 _ v2 hx2₂) (rX_bits_x22 _ v22 hx22₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a84 (`addi`): x20 := x10 + sext 0x000. -/
theorem site_80002a84_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v10 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a84#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x20 (v10 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a84 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002a84#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002a84#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80002a84#64) vminstret (0x00050a13#32)
    (instruction.ITYPE (0x000#12, (regidx.Regidx 0x0a#5), (regidx.Regidx 0x14#5), iop.ADDI))
    Register.x20 (v10 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x0a#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00050a13_ed nr_00050a13_ed
    (Vsa.Sim.DecodeTable.decode_00050a13 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x14#5) v10
      (afterNextPC (afterPrelude σ) (0x80002a84#64))
      (sigma3_alu σ (0x80002a84#64) Register.x20 (v10 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x10 _ v10 hx10₂) (wX_bits_x20 _ (v10 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a88 (`addi`): x18 := x11 + sext 0x000. -/
theorem site_80002a88_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a88#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x18 (v11 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a88 hmem
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80002a88#64)).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ (0x80002a88#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_alu σ i u (0x80002a88#64) vminstret (0x00058913#32)
    (instruction.ITYPE (0x000#12, (regidx.Regidx 0x0b#5), (regidx.Regidx 0x12#5), iop.ADDI))
    Register.x18 (v11 + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x89#8) (0x05#8) (0x00#8)
    hG hpc hminstret w_00058913_ed nr_00058913_ed
    (Vsa.Sim.DecodeTable.decode_00058913 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x12#5) v11
      (afterNextPC (afterPrelude σ) (0x80002a88#64))
      (sigma3_alu σ (0x80002a88#64) Register.x18 (v11 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x11 _ v11 hx11₂) (wX_bits_x18 _ (v11 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a8c (`addi`): x21 := x12 + sext 0x000. -/
theorem site_80002a8c_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a8c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x21 (v12 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a8c hmem
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x80002a8c#64)).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ (0x80002a8c#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_alu σ i u (0x80002a8c#64) vminstret (0x00060a93#32)
    (instruction.ITYPE (0x000#12, (regidx.Regidx 0x0c#5), (regidx.Regidx 0x15#5), iop.ADDI))
    Register.x21 (v12 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x0a#8) (0x06#8) (0x00#8)
    hG hpc hminstret w_00060a93_ed nr_00060a93_ed
    (Vsa.Sim.DecodeTable.decode_00060a93 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x15#5) v12
      (afterNextPC (afterPrelude σ) (0x80002a8c#64))
      (sigma3_alu σ (0x80002a8c#64) Register.x21 (v12 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x12 _ v12 hx12₂) (wX_bits_x21 _ (v12 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a94 (`ld`): x22 := sext(mem[x10+0x008]) (8B). -/
theorem site_80002a94_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v10 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx10 : σ.regs.get? Register.x10 = some v10)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a94#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v10 + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (v10 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v10 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v10 + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (v10 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v10 + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x22 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a94 hmem
  have hx10₂ : (afterNextPC (afterPrelude σ) (0x80002a94#64)).regs.get? Register.x10 = some v10 := by
    rw [get?_afterNextPC σ (0x80002a94#64) _ (by decide) (by decide)]; exact hx10
  exact stepObs_alu σ i u (0x80002a94#64) vminstret (0x00853b03#32)
    (instruction.LOAD (0x008#12, (regidx.Regidx 0x0a#5), (regidx.Regidx 0x16#5), false, 8))
    Register.x22 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x3b#8) (0x85#8) (0x00#8)
    hG hpc hminstret w_00853b03_ed nr_00853b03_ed
    (Vsa.Sim.DecodeTable.decode_00853b03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002a94#64) (0x008#12) (regidx.Regidx 0x0a#5) (regidx.Regidx 0x16#5)
      (sigma3_alu σ (0x80002a94#64) Register.x22 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v10 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x10 _ v10 hx10₂) (wX_bits_x22 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a98 (`addi`): x8 := x0 + sext 0x000. -/
theorem site_80002a98_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a98#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x8 ((0#64) + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a98 hmem
  exact stepObs_alu σ i u (0x80002a98#64) vminstret (0x00000413#32)
    (instruction.ITYPE (0x000#12, (regidx.Regidx 0x00#5), (regidx.Regidx 0x08#5), iop.ADDI))
    Register.x8 ((0#64) + sign_extend (m := 64) (0x000#12)) (0x13#8) (0x04#8) (0x00#8) (0x00#8)
    hG hpc hminstret w_00000413_ed nr_00000413_ed
    (Vsa.Sim.DecodeTable.decode_00000413 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x00#5) (regidx.Regidx 0x08#5) (0#64)
      (afterNextPC (afterPrelude σ) (0x80002a98#64))
      (sigma3_alu σ (0x80002a98#64) Register.x8 ((0#64) + sign_extend (m := 64) (0x000#12)))
      (rX_bits_zero _) (wX_bits_x8 _ ((0#64) + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002a9c (`addi`): x9 := x22 + sext 0x000. -/
theorem site_80002a9c_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v22 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx22 : σ.regs.get? Register.x22 = some v22)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002a9c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x9 (v22 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002a9c hmem
  have hx22₂ : (afterNextPC (afterPrelude σ) (0x80002a9c#64)).regs.get? Register.x22 = some v22 := by
    rw [get?_afterNextPC σ (0x80002a9c#64) _ (by decide) (by decide)]; exact hx22
  exact stepObs_alu σ i u (0x80002a9c#64) vminstret (0x000b0493#32)
    (instruction.ITYPE (0x000#12, (regidx.Regidx 0x16#5), (regidx.Regidx 0x09#5), iop.ADDI))
    Register.x9 (v22 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x04#8) (0x0b#8) (0x00#8)
    hG hpc hminstret w_000b0493_ed nr_000b0493_ed
    (Vsa.Sim.DecodeTable.decode_000b0493 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x16#5) (regidx.Regidx 0x09#5) v22
      (afterNextPC (afterPrelude σ) (0x80002a9c#64))
      (sigma3_alu σ (0x80002a9c#64) Register.x9 (v22 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x22 _ v22 hx22₂) (wX_bits_x9 _ (v22 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002aa4 (`addi`): x8 := x8 + sext 0x001. -/
theorem site_80002aa4_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002aa4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x8 (v8 + sign_extend (m := 64) (0x001#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002aa4 hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002aa4#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002aa4#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_alu σ i u (0x80002aa4#64) vminstret (0x00140413#32)
    (instruction.ITYPE (0x001#12, (regidx.Regidx 0x08#5), (regidx.Regidx 0x08#5), iop.ADDI))
    Register.x8 (v8 + sign_extend (m := 64) (0x001#12)) (0x13#8) (0x04#8) (0x14#8) (0x00#8)
    hG hpc hminstret w_00140413_ed nr_00140413_ed
    (Vsa.Sim.DecodeTable.decode_00140413 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x001#12) (regidx.Regidx 0x08#5) (regidx.Regidx 0x08#5) v8
      (afterNextPC (afterPrelude σ) (0x80002aa4#64))
      (sigma3_alu σ (0x80002aa4#64) Register.x8 (v8 + sign_extend (m := 64) (0x001#12)))
      (rX_bits_x8 _ v8 hx8₂) (wX_bits_x8 _ (v8 + sign_extend (m := 64) (0x001#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002aa8 (`addi`): x9 := x9 + sext 0x008. -/
theorem site_80002aa8_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v9 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002aa8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x9 (v9 + sign_extend (m := 64) (0x008#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002aa8 hmem
  have hx9₂ : (afterNextPC (afterPrelude σ) (0x80002aa8#64)).regs.get? Register.x9 = some v9 := by
    rw [get?_afterNextPC σ (0x80002aa8#64) _ (by decide) (by decide)]; exact hx9
  exact stepObs_alu σ i u (0x80002aa8#64) vminstret (0x00848493#32)
    (instruction.ITYPE (0x008#12, (regidx.Regidx 0x09#5), (regidx.Regidx 0x09#5), iop.ADDI))
    Register.x9 (v9 + sign_extend (m := 64) (0x008#12)) (0x93#8) (0x84#8) (0x84#8) (0x00#8)
    hG hpc hminstret w_00848493_ed nr_00848493_ed
    (Vsa.Sim.DecodeTable.decode_00848493 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x008#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x09#5) v9
      (afterNextPC (afterPrelude σ) (0x80002aa8#64))
      (sigma3_alu σ (0x80002aa8#64) Register.x9 (v9 + sign_extend (m := 64) (0x008#12)))
      (rX_bits_x9 _ v9 hx9₂) (wX_bits_x9 _ (v9 + sign_extend (m := 64) (0x008#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ab0 (`ld`): x10 := sext(mem[x9+0x000]) (8B). -/
theorem site_80002ab0_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v9 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx9 : σ.regs.get? Register.x9 = some v9)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ab0#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v9 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (v9 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v9 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v9 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (v9 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v9 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v9 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v9 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v9 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v9 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v9 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v9 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v9 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x10 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ab0 hmem
  have hx9₂ : (afterNextPC (afterPrelude σ) (0x80002ab0#64)).regs.get? Register.x9 = some v9 := by
    rw [get?_afterNextPC σ (0x80002ab0#64) _ (by decide) (by decide)]; exact hx9
  exact stepObs_alu σ i u (0x80002ab0#64) vminstret (0x0004b503#32)
    (instruction.LOAD (0x000#12, (regidx.Regidx 0x09#5), (regidx.Regidx 0x0a#5), false, 8))
    Register.x10 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0xb5#8) (0x04#8) (0x00#8)
    hG hpc hminstret w_0004b503_ed nr_0004b503_ed
    (Vsa.Sim.DecodeTable.decode_0004b503 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002ab0#64) (0x000#12) (regidx.Regidx 0x09#5) (regidx.Regidx 0x0a#5)
      (sigma3_alu σ (0x80002ab0#64) Register.x10 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v9 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x9 _ v9 hx9₂) (wX_bits_x10 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ab4 (`addi`): x11 := x18 + sext 0x000. -/
theorem site_80002ab4_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v18 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx18 : σ.regs.get? Register.x18 = some v18)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ab4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (v18 + sign_extend (m := 64) (0x000#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ab4 hmem
  have hx18₂ : (afterNextPC (afterPrelude σ) (0x80002ab4#64)).regs.get? Register.x18 = some v18 := by
    rw [get?_afterNextPC σ (0x80002ab4#64) _ (by decide) (by decide)]; exact hx18
  exact stepObs_alu σ i u (0x80002ab4#64) vminstret (0x00090593#32)
    (instruction.ITYPE (0x000#12, (regidx.Regidx 0x12#5), (regidx.Regidx 0x0b#5), iop.ADDI))
    Register.x11 (v18 + sign_extend (m := 64) (0x000#12)) (0x93#8) (0x05#8) (0x09#8) (0x00#8)
    hG hpc hminstret w_00090593_ed nr_00090593_ed
    (Vsa.Sim.DecodeTable.decode_00090593 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x000#12) (regidx.Regidx 0x12#5) (regidx.Regidx 0x0b#5) v18
      (afterNextPC (afterPrelude σ) (0x80002ab4#64))
      (sigma3_alu σ (0x80002ab4#64) Register.x11 (v18 + sign_extend (m := 64) (0x000#12)))
      (rX_bits_x18 _ v18 hx18₂) (wX_bits_x11 _ (v18 + sign_extend (m := 64) (0x000#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ac0 (`ld`): x15 := sext(mem[x20+0x010]) (8B). -/
theorem site_80002ac0_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v20 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx20 : σ.regs.get? Register.x20 = some v20)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ac0#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v20 + sign_extend (m := 64) (0x010#12)).toNat)
    (hahiram : (v20 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v20 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v20 + sign_extend (m := 64) (0x010#12)).toNat)
    (haalign : (v20 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v20 + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ac0 hmem
  have hx20₂ : (afterNextPC (afterPrelude σ) (0x80002ac0#64)).regs.get? Register.x20 = some v20 := by
    rw [get?_afterNextPC σ (0x80002ac0#64) _ (by decide) (by decide)]; exact hx20
  exact stepObs_alu σ i u (0x80002ac0#64) vminstret (0x010a3783#32)
    (instruction.LOAD (0x010#12, (regidx.Regidx 0x14#5), (regidx.Regidx 0x0f#5), false, 8))
    Register.x15 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x37#8) (0x0a#8) (0x01#8)
    hG hpc hminstret w_010a3783_ed nr_010a3783_ed
    (Vsa.Sim.DecodeTable.decode_010a3783 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002ac0#64) (0x010#12) (regidx.Regidx 0x14#5) (regidx.Regidx 0x0f#5)
      (sigma3_alu σ (0x80002ac0#64) Register.x15 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v20 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x20 _ v20 hx20₂) (wX_bits_x15 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ac4 (`slli`): x14 := x8 <<< 1. -/
theorem site_80002ac4_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v8 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ac4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (shift_bits_left v8 (Sail.BitVec.extractLsb (0x01#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ac4 hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002ac4#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002ac4#64) _ (by decide) (by decide)]; exact hx8
  exact stepObs_alu σ i u (0x80002ac4#64) vminstret (0x00141713#32)
    (instruction.SHIFTIOP (0x01#6, (regidx.Regidx 0x08#5), (regidx.Regidx 0x0e#5), sop.SLLI))
    Register.x14 (shift_bits_left v8 (Sail.BitVec.extractLsb (0x01#6) 5 0)) (0x13#8) (0x17#8) (0x14#8) (0x00#8)
    hG hpc hminstret w_00141713_ed nr_00141713_ed
    (Vsa.Sim.DecodeTable.decode_00141713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_slli_char (0x01#6) (regidx.Regidx 0x08#5) (regidx.Regidx 0x0e#5) v8
      (afterNextPC (afterPrelude σ) (0x80002ac4#64))
      (sigma3_alu σ (0x80002ac4#64) Register.x14 (shift_bits_left v8 (Sail.BitVec.extractLsb (0x01#6) 5 0)))
      (rX_bits_x8 _ v8 hx8₂) (wX_bits_x14 _ (shift_bits_left v8 (Sail.BitVec.extractLsb (0x01#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ac8 (`ld`): x11 := sext(mem[x21+0x000]) (8B). -/
theorem site_80002ac8_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v21 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx21 : σ.regs.get? Register.x21 = some v21)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ac8#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v21 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (v21 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v21 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v21 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (v21 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v21 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v21 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v21 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v21 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v21 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v21 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v21 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v21 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x11 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ac8 hmem
  have hx21₂ : (afterNextPC (afterPrelude σ) (0x80002ac8#64)).regs.get? Register.x21 = some v21 := by
    rw [get?_afterNextPC σ (0x80002ac8#64) _ (by decide) (by decide)]; exact hx21
  exact stepObs_alu σ i u (0x80002ac8#64) vminstret (0x000ab583#32)
    (instruction.LOAD (0x000#12, (regidx.Regidx 0x15#5), (regidx.Regidx 0x0b#5), false, 8))
    Register.x11 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0xb5#8) (0x0a#8) (0x00#8)
    hG hpc hminstret w_000ab583_ed nr_000ab583_ed
    (Vsa.Sim.DecodeTable.decode_000ab583 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002ac8#64) (0x000#12) (regidx.Regidx 0x15#5) (regidx.Regidx 0x0b#5)
      (sigma3_alu σ (0x80002ac8#64) Register.x11 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v21 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x21 _ v21 hx21₂) (wX_bits_x11 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002acc (`ld`): x12 := sext(mem[x21+0x008]) (8B). -/
theorem site_80002acc_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v21 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx21 : σ.regs.get? Register.x21 = some v21)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002acc#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v21 + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (v21 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v21 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v21 + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (v21 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v21 + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v21 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v21 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v21 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v21 + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v21 + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v21 + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v21 + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002acc hmem
  have hx21₂ : (afterNextPC (afterPrelude σ) (0x80002acc#64)).regs.get? Register.x21 = some v21 := by
    rw [get?_afterNextPC σ (0x80002acc#64) _ (by decide) (by decide)]; exact hx21
  exact stepObs_alu σ i u (0x80002acc#64) vminstret (0x008ab603#32)
    (instruction.LOAD (0x008#12, (regidx.Regidx 0x15#5), (regidx.Regidx 0x0c#5), false, 8))
    Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0xb6#8) (0x8a#8) (0x00#8)
    hG hpc hminstret w_008ab603_ed nr_008ab603_ed
    (Vsa.Sim.DecodeTable.decode_008ab603 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002acc#64) (0x008#12) (regidx.Regidx 0x15#5) (regidx.Regidx 0x0c#5)
      (sigma3_alu σ (0x80002acc#64) Register.x12 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v21 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x21 _ v21 hx21₂) (wX_bits_x12 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ad0 (`ld`): x13 := sext(mem[x21+0x010]) (8B). -/
theorem site_80002ad0_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v21 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx21 : σ.regs.get? Register.x21 = some v21)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ad0#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v21 + sign_extend (m := 64) (0x010#12)).toNat)
    (hahiram : (v21 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v21 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v21 + sign_extend (m := 64) (0x010#12)).toNat)
    (haalign : (v21 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v21 + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v21 + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v21 + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v21 + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v21 + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v21 + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v21 + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v21 + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x13 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ad0 hmem
  have hx21₂ : (afterNextPC (afterPrelude σ) (0x80002ad0#64)).regs.get? Register.x21 = some v21 := by
    rw [get?_afterNextPC σ (0x80002ad0#64) _ (by decide) (by decide)]; exact hx21
  exact stepObs_alu σ i u (0x80002ad0#64) vminstret (0x010ab683#32)
    (instruction.LOAD (0x010#12, (regidx.Regidx 0x15#5), (regidx.Regidx 0x0d#5), false, 8))
    Register.x13 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0xb6#8) (0x0a#8) (0x01#8)
    hG hpc hminstret w_010ab683_ed nr_010ab683_ed
    (Vsa.Sim.DecodeTable.decode_010ab683 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002ad0#64) (0x010#12) (regidx.Regidx 0x15#5) (regidx.Regidx 0x0d#5)
      (sigma3_alu σ (0x80002ad0#64) Register.x13 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v21 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x21 _ v21 hx21₂) (wX_bits_x13 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ad4 (`add`): x14 := x14 + x8. -/
theorem site_80002ad4_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v8 : BitVec 64) (v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx8 : σ.regs.get? Register.x8 = some v8)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ad4#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (v14 + v8)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ad4 hmem
  have hx8₂ : (afterNextPC (afterPrelude σ) (0x80002ad4#64)).regs.get? Register.x8 = some v8 := by
    rw [get?_afterNextPC σ (0x80002ad4#64) _ (by decide) (by decide)]; exact hx8
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x80002ad4#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x80002ad4#64) _ (by decide) (by decide)]; exact hx14
  exact stepObs_alu σ i u (0x80002ad4#64) vminstret (0x00870733#32)
    (instruction.RTYPE ((regidx.Regidx 0x08#5), (regidx.Regidx 0x0e#5), (regidx.Regidx 0x0e#5), rop.ADD))
    Register.x14 (v14 + v8) (0x33#8) (0x07#8) (0x87#8) (0x00#8)
    hG hpc hminstret w_00870733_ed nr_00870733_ed
    (Vsa.Sim.DecodeTable.decode_00870733 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_add_char (regidx.Regidx 0x08#5) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14 v8
      (afterNextPC (afterPrelude σ) (0x80002ad4#64))
      (sigma3_alu σ (0x80002ad4#64) Register.x14 (v14 + v8))
      (rX_bits_x14 _ v14 hx14₂) (rX_bits_x8 _ v8 hx8₂) (wX_bits_x14 _ (v14 + v8)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ad8 (`slli`): x14 := x14 <<< 3. -/
theorem site_80002ad8_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v14 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ad8#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x14 (shift_bits_left v14 (Sail.BitVec.extractLsb (0x03#6) 5 0))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ad8 hmem
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x80002ad8#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x80002ad8#64) _ (by decide) (by decide)]; exact hx14
  exact stepObs_alu σ i u (0x80002ad8#64) vminstret (0x00371713#32)
    (instruction.SHIFTIOP (0x03#6, (regidx.Regidx 0x0e#5), (regidx.Regidx 0x0e#5), sop.SLLI))
    Register.x14 (shift_bits_left v14 (Sail.BitVec.extractLsb (0x03#6) 5 0)) (0x13#8) (0x17#8) (0x37#8) (0x00#8)
    hG hpc hminstret w_00371713_ed nr_00371713_ed
    (Vsa.Sim.DecodeTable.decode_00371713 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_shiftiop_slli_char (0x03#6) (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0e#5) v14
      (afterNextPC (afterPrelude σ) (0x80002ad8#64))
      (sigma3_alu σ (0x80002ad8#64) Register.x14 (shift_bits_left v14 (Sail.BitVec.extractLsb (0x03#6) 5 0)))
      (rX_bits_x14 _ v14 hx14₂) (wX_bits_x14 _ (shift_bits_left v14 (Sail.BitVec.extractLsb (0x03#6) 5 0))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002adc (`add`): x15 := x15 + x14. -/
theorem site_80002adc_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v14 : BitVec 64) (v15 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx14 : σ.regs.get? Register.x14 = some v14)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002adc#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x15 (v15 + v14)) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002adc hmem
  have hx14₂ : (afterNextPC (afterPrelude σ) (0x80002adc#64)).regs.get? Register.x14 = some v14 := by
    rw [get?_afterNextPC σ (0x80002adc#64) _ (by decide) (by decide)]; exact hx14
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002adc#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002adc#64) _ (by decide) (by decide)]; exact hx15
  exact stepObs_alu σ i u (0x80002adc#64) vminstret (0x00e787b3#32)
    (instruction.RTYPE ((regidx.Regidx 0x0e#5), (regidx.Regidx 0x0f#5), (regidx.Regidx 0x0f#5), rop.ADD))
    Register.x15 (v15 + v14) (0xb3#8) (0x87#8) (0xe7#8) (0x00#8)
    hG hpc hminstret w_00e787b3_ed nr_00e787b3_ed
    (Vsa.Sim.DecodeTable.decode_00e787b3 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_rtype_add_char (regidx.Regidx 0x0e#5) (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0f#5) v15 v14
      (afterNextPC (afterPrelude σ) (0x80002adc#64))
      (sigma3_alu σ (0x80002adc#64) Register.x15 (v15 + v14))
      (rX_bits_x15 _ v15 hx15₂) (rX_bits_x14 _ v14 hx14₂) (wX_bits_x15 _ (v15 + v14)))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ae0 (`sd`): store x11 (8B) @ x15+0x000. -/
theorem site_80002ae0_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v11 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx11 : σ.regs.get? Register.x11 = some v11)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ae0#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v15 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (v15 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v15 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (v15 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ae0#64)).mem (v15 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v11)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ae0#64)).mem (v15 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v11))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ae0 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002ae0#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002ae0#64) _ (by decide) (by decide)]; exact hx15
  have hx11₂ : (afterNextPC (afterPrelude σ) (0x80002ae0#64)).regs.get? Register.x11 = some v11 := by
    rw [get?_afterNextPC σ (0x80002ae0#64) _ (by decide) (by decide)]; exact hx11
  exact stepObs_store σ i u (0x80002ae0#64) vminstret (0x00b7b023#32)
    (instruction.STORE (0x000#12, (regidx.Regidx 0x0b#5), (regidx.Regidx 0x0f#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ae0#64)).mem (v15 + sign_extend (m := 64) (0x000#12)).toNat (sdData_val v11))
    (0x23#8) (0xb0#8) (0xb7#8) (0x00#8)
    hG hpc hminstret w_00b7b023_ed nr_00b7b023_ed
    (Vsa.Sim.DecodeTable.decode_00b7b023 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002ae0#64) (0x000#12) (regidx.Regidx 0x0b#5) (regidx.Regidx 0x0f#5)
      v15 v11 hG (rX_bits_x15 _ v15 hx15₂) (rX_bits_x11 _ v11 hx11₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ae4 (`sd`): store x12 (8B) @ x15+0x008. -/
theorem site_80002ae4_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v12 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx12 : σ.regs.get? Register.x12 = some v12)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ae4#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v15 + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (v15 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v15 + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (v15 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ae4#64)).mem (v15 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v12)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ae4#64)).mem (v15 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ae4 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002ae4#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002ae4#64) _ (by decide) (by decide)]; exact hx15
  have hx12₂ : (afterNextPC (afterPrelude σ) (0x80002ae4#64)).regs.get? Register.x12 = some v12 := by
    rw [get?_afterNextPC σ (0x80002ae4#64) _ (by decide) (by decide)]; exact hx12
  exact stepObs_store σ i u (0x80002ae4#64) vminstret (0x00c7b423#32)
    (instruction.STORE (0x008#12, (regidx.Regidx 0x0c#5), (regidx.Regidx 0x0f#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ae4#64)).mem (v15 + sign_extend (m := 64) (0x008#12)).toNat (sdData_val v12))
    (0x23#8) (0xb4#8) (0xc7#8) (0x00#8)
    hG hpc hminstret w_00c7b423_ed nr_00c7b423_ed
    (Vsa.Sim.DecodeTable.decode_00c7b423 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002ae4#64) (0x008#12) (regidx.Regidx 0x0c#5) (regidx.Regidx 0x0f#5)
      v15 v12 hG (rX_bits_x15 _ v15 hx15₂) (rX_bits_x12 _ v12 hx12₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002ae8 (`sd`): store x13 (8B) @ x15+0x010. -/
theorem site_80002ae8_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v15 v13 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx15 : σ.regs.get? Register.x15 = some v15)
    (hx13 : σ.regs.get? Register.x13 = some v13)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002ae8#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v15 + sign_extend (m := 64) (0x010#12)).toNat)
    (hahiram : (v15 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hahiwin : tohostAddr + 16 ≤ (v15 + sign_extend (m := 64) (0x010#12)).toNat)
    (haalign : (v15 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧
      σ'.mem = (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ae8#64)).mem (v15 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val v13)) ∧
      ReadsLikePost σ' (sigmaPost_store σ pc vminstret (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ae8#64)).mem (v15 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val v13))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002ae8 hmem
  have hx15₂ : (afterNextPC (afterPrelude σ) (0x80002ae8#64)).regs.get? Register.x15 = some v15 := by
    rw [get?_afterNextPC σ (0x80002ae8#64) _ (by decide) (by decide)]; exact hx15
  have hx13₂ : (afterNextPC (afterPrelude σ) (0x80002ae8#64)).regs.get? Register.x13 = some v13 := by
    rw [get?_afterNextPC σ (0x80002ae8#64) _ (by decide) (by decide)]; exact hx13
  exact stepObs_store σ i u (0x80002ae8#64) vminstret (0x00d7b823#32)
    (instruction.STORE (0x010#12, (regidx.Regidx 0x0d#5), (regidx.Regidx 0x0f#5), 8))
    (writeMap8 (afterNextPC (afterPrelude σ) (0x80002ae8#64)).mem (v15 + sign_extend (m := 64) (0x010#12)).toNat (sdData_val v13))
    (0x23#8) (0xb8#8) (0xd7#8) (0x00#8)
    hG hpc hminstret w_00d7b823_ed nr_00d7b823_ed
    (Vsa.Sim.DecodeTable.decode_00d7b823 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_sd_val σ (0x80002ae8#64) (0x010#12) (regidx.Regidx 0x0d#5) (regidx.Regidx 0x0f#5)
      v15 v13 hG (rX_bits_x15 _ v15 hx15₂) (rX_bits_x13 _ v13 hx13₂) halo hahiram hahiwin haalign)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002aec (`ld`): x1 := sext(mem[x2+0x038]) (8B). -/
theorem site_80002aec_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002aec#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x038#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x038#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x038#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x038#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v2 + sign_extend (m := 64) (0x038#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x1 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002aec hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002aec#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002aec#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002aec#64) vminstret (0x03813083#32)
    (instruction.LOAD (0x038#12, (regidx.Regidx 0x02#5), (regidx.Regidx 0x01#5), false, 8))
    Register.x1 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x30#8) (0x81#8) (0x03#8)
    hG hpc hminstret w_03813083_ed nr_03813083_ed
    (Vsa.Sim.DecodeTable.decode_03813083 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002aec#64) (0x038#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x01#5)
      (sigma3_alu σ (0x80002aec#64) Register.x1 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x1 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002af0 (`ld`): x8 := sext(mem[x2+0x030]) (8B). -/
theorem site_80002af0_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002af0#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x030#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x030#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x030#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x030#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v2 + sign_extend (m := 64) (0x030#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x8 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002af0 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002af0#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002af0#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002af0#64) vminstret (0x03013403#32)
    (instruction.LOAD (0x030#12, (regidx.Regidx 0x02#5), (regidx.Regidx 0x08#5), false, 8))
    Register.x8 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x34#8) (0x01#8) (0x03#8)
    hG hpc hminstret w_03013403_ed nr_03013403_ed
    (Vsa.Sim.DecodeTable.decode_03013403 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002af0#64) (0x030#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x08#5)
      (sigma3_alu σ (0x80002af0#64) Register.x8 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x8 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002af4 (`ld`): x9 := sext(mem[x2+0x028]) (8B). -/
theorem site_80002af4_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002af4#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x028#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x028#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x028#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x028#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v2 + sign_extend (m := 64) (0x028#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x9 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002af4 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002af4#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002af4#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002af4#64) vminstret (0x02813483#32)
    (instruction.LOAD (0x028#12, (regidx.Regidx 0x02#5), (regidx.Regidx 0x09#5), false, 8))
    Register.x9 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x34#8) (0x81#8) (0x02#8)
    hG hpc hminstret w_02813483_ed nr_02813483_ed
    (Vsa.Sim.DecodeTable.decode_02813483 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002af4#64) (0x028#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x09#5)
      (sigma3_alu σ (0x80002af4#64) Register.x9 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x9 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002af8 (`ld`): x18 := sext(mem[x2+0x020]) (8B). -/
theorem site_80002af8_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002af8#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x020#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x020#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x020#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x020#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v2 + sign_extend (m := 64) (0x020#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v2 + sign_extend (m := 64) (0x020#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v2 + sign_extend (m := 64) (0x020#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v2 + sign_extend (m := 64) (0x020#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v2 + sign_extend (m := 64) (0x020#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v2 + sign_extend (m := 64) (0x020#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v2 + sign_extend (m := 64) (0x020#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v2 + sign_extend (m := 64) (0x020#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x18 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002af8 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002af8#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002af8#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002af8#64) vminstret (0x02013903#32)
    (instruction.LOAD (0x020#12, (regidx.Regidx 0x02#5), (regidx.Regidx 0x12#5), false, 8))
    Register.x18 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x39#8) (0x01#8) (0x02#8)
    hG hpc hminstret w_02013903_ed nr_02013903_ed
    (Vsa.Sim.DecodeTable.decode_02013903 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002af8#64) (0x020#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x12#5)
      (sigma3_alu σ (0x80002af8#64) Register.x18 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x18 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002afc (`ld`): x19 := sext(mem[x2+0x018]) (8B). -/
theorem site_80002afc_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002afc#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x018#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x018#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x018#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x018#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v2 + sign_extend (m := 64) (0x018#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v2 + sign_extend (m := 64) (0x018#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v2 + sign_extend (m := 64) (0x018#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v2 + sign_extend (m := 64) (0x018#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v2 + sign_extend (m := 64) (0x018#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v2 + sign_extend (m := 64) (0x018#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v2 + sign_extend (m := 64) (0x018#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v2 + sign_extend (m := 64) (0x018#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x19 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002afc hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002afc#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002afc#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002afc#64) vminstret (0x01813983#32)
    (instruction.LOAD (0x018#12, (regidx.Regidx 0x02#5), (regidx.Regidx 0x13#5), false, 8))
    Register.x19 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x39#8) (0x81#8) (0x01#8)
    hG hpc hminstret w_01813983_ed nr_01813983_ed
    (Vsa.Sim.DecodeTable.decode_01813983 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002afc#64) (0x018#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x13#5)
      (sigma3_alu σ (0x80002afc#64) Register.x19 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x19 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002b00 (`ld`): x20 := sext(mem[x2+0x010]) (8B). -/
theorem site_80002b00_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b00#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x010#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x010#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x010#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x010#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v2 + sign_extend (m := 64) (0x010#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v2 + sign_extend (m := 64) (0x010#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v2 + sign_extend (m := 64) (0x010#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v2 + sign_extend (m := 64) (0x010#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v2 + sign_extend (m := 64) (0x010#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v2 + sign_extend (m := 64) (0x010#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v2 + sign_extend (m := 64) (0x010#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v2 + sign_extend (m := 64) (0x010#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x20 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b00 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002b00#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002b00#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002b00#64) vminstret (0x01013a03#32)
    (instruction.LOAD (0x010#12, (regidx.Regidx 0x02#5), (regidx.Regidx 0x14#5), false, 8))
    Register.x20 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x3a#8) (0x01#8) (0x01#8)
    hG hpc hminstret w_01013a03_ed nr_01013a03_ed
    (Vsa.Sim.DecodeTable.decode_01013a03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002b00#64) (0x010#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x14#5)
      (sigma3_alu σ (0x80002b00#64) Register.x20 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x20 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002b04 (`ld`): x21 := sext(mem[x2+0x008]) (8B). -/
theorem site_80002b04_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b04#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x008#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x008#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x008#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x008#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v2 + sign_extend (m := 64) (0x008#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v2 + sign_extend (m := 64) (0x008#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v2 + sign_extend (m := 64) (0x008#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v2 + sign_extend (m := 64) (0x008#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v2 + sign_extend (m := 64) (0x008#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v2 + sign_extend (m := 64) (0x008#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v2 + sign_extend (m := 64) (0x008#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v2 + sign_extend (m := 64) (0x008#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x21 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b04 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002b04#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002b04#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002b04#64) vminstret (0x00813a83#32)
    (instruction.LOAD (0x008#12, (regidx.Regidx 0x02#5), (regidx.Regidx 0x15#5), false, 8))
    Register.x21 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x83#8) (0x3a#8) (0x81#8) (0x00#8)
    hG hpc hminstret w_00813a83_ed nr_00813a83_ed
    (Vsa.Sim.DecodeTable.decode_00813a83 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002b04#64) (0x008#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x15#5)
      (sigma3_alu σ (0x80002b04#64) Register.x21 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x21 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002b08 (`ld`): x22 := sext(mem[x2+0x000]) (8B). -/
theorem site_80002b08_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret v2 : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b08#64 : BitVec 64))
    (halo : 0x80000000 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (hahiram : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000)
    (hhtif : (v2 + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v2 + sign_extend (m := 64) (0x000#12)).toNat)
    (haalign : (v2 + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0)
    (hm0 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat]? = some b0)
    (hm1 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 1]? = some b1)
    (hm2 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 2]? = some b2)
    (hm3 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 3]? = some b3)
    (hm4 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 4]? = some b4)
    (hm5 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 5]? = some b5)
    (hm6 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 6]? = some b6)
    (hm7 : σ.mem[(v2 + sign_extend (m := 64) (0x000#12)).toNat + 7]? = some b7)
    (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x22 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b08 hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002b08#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002b08#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002b08#64) vminstret (0x00013b03#32)
    (instruction.LOAD (0x000#12, (regidx.Regidx 0x02#5), (regidx.Regidx 0x16#5), false, 8))
    Register.x22 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))) (0x03#8) (0x3b#8) (0x01#8) (0x00#8)
    hG hpc hminstret w_00013b03_ed nr_00013b03_ed
    (Vsa.Sim.DecodeTable.decode_00013b03 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (exec_ld σ (0x80002b08#64) (0x000#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x16#5)
      (sigma3_alu σ (0x80002b08#64) Register.x22 (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8)))) v2 b0 b1 b2 b3 b4 b5 b6 b7 hG
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x22 _ (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8 * 8))))
      halo hahiram hhtif haalign hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

/-- Site 0x80002b0c (`addi`): x2 := x2 + sext 0x040. -/
theorem site_80002b0c_ed
    (σ : MState) (i u : Nat) (pc : BitVec 64) (vminstret : BitVec 64) (v2 : BitVec 64)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some pc)
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hx2 : σ.regs.get? Register.x2 = some v2)
    (hmem : Env_defineLoaded σ.mem)
    (hpcv : pc = (0x80002b0c#64 : BitVec 64)) (hi : i < 2) :
    ∃ (σ' : MState) (i' : Nat),
      Vsa.Machine.Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
      ReadsLikePost σ' (sigmaPost_alu σ pc vminstret Register.x2 (v2 + sign_extend (m := 64) (0x040#12))) := by
  subst hpcv
  obtain ⟨hb0, hb1, hb2, hb3⟩ := env_define_at_80002b0c hmem
  have hx2₂ : (afterNextPC (afterPrelude σ) (0x80002b0c#64)).regs.get? Register.x2 = some v2 := by
    rw [get?_afterNextPC σ (0x80002b0c#64) _ (by decide) (by decide)]; exact hx2
  exact stepObs_alu σ i u (0x80002b0c#64) vminstret (0x04010113#32)
    (instruction.ITYPE (0x040#12, (regidx.Regidx 0x02#5), (regidx.Regidx 0x02#5), iop.ADDI))
    Register.x2 (v2 + sign_extend (m := 64) (0x040#12)) (0x13#8) (0x01#8) (0x01#8) (0x04#8)
    hG hpc hminstret w_04010113_ed nr_04010113_ed
    (Vsa.Sim.DecodeTable.decode_04010113 (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (execute_itype_addi_char (0x040#12) (regidx.Regidx 0x02#5) (regidx.Regidx 0x02#5) v2
      (afterNextPC (afterPrelude σ) (0x80002b0c#64))
      (sigma3_alu σ (0x80002b0c#64) Register.x2 (v2 + sign_extend (m := 64) (0x040#12)))
      (rX_bits_x2 _ v2 hx2₂) (wX_bits_x2 _ (v2 + sign_extend (m := 64) (0x040#12))))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi

end Vsa.Sim
