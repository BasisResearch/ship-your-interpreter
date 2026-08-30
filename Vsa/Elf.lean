import LeanRiscv

/-!
# The frozen machine-semantics interface

`c/while-riscv-htif.elf` is the source of truth for this development: a
bare-metal RISC-V build of the WHILE interpreter with a WHILE script linked
into the image, doing console I/O over the HTIF `tohost` mailbox.

This module is the STABLE INTERFACE under ~570 proof modules: the machine
setup (`setupElf`) and the single-step loop body (`stepOnce`) that the whole
`Vsa.Sim` development abstracts. The heavy, evolving pieces — the embedded
ELF bytes, the parsed file, and the fuel-bounded runner (`runElf` and
friends) — live in `Vsa.ElfRun`, which only `Vsa.ElfMono` and `VsaRun`
import, so editing them no longer rebuilds the world.

**FREEZE (2026-08-29).** Any olean-changing edit to THIS file rebuilds the
full ~570-module cone (measured: 75 min pre-campaign, ~20 min after). Do not
add declarations here; put them in `Vsa.ElfRun` (runner-side) or a `Vsa.Sim`
leaf (proof-side). An edit here needs a full-build justification.
-/

open LeanRV64DExecutable
open Register

namespace Vsa

open Sail in
open LeanRV64DExecutable.Functions in
/-- Set up the machine exactly like the reference emulator
(`lean_emulator/LeanRiscv.lean`): model init, register/HTIF init from the
ELF, then entry point into `PC`. -/
def setupElf (elf : ELF64File) : SailM Unit := do
  sail_model_init ()
  initializeRegisters elf
  init_model ""
  cycle_count ()
  -- init_model resets the PC, so set it (again) afterwards.
  writeReg PC (elf.file_header.e_entry : UInt64).toBitVec

open Sail in
open LeanRV64DExecutable.Functions in
/-- One iteration of the Sail model's top-level `loop`: check for the HTIF
exit signal, otherwise `try_step`, mirroring the retired-instruction
counting and clock ticking of the reference loop. `.inl` = halted with
(exit code, steps used); `.inr` = continue with (tick counter, steps). -/
def stepOnce (i used : Nat) : SailM (Sum (Option Nat × Nat) (Nat × Nat)) := do
  if (← readReg htif_done) then
    pure (.inl (some (BitVec.toNat (← readReg htif_exit_code)), used))
  else
    let stepped ← try_step used true
    if stepped then cycle_count () else pure ()
    if (← readReg htif_done) then
      pure (.inl (some (BitVec.toNat (← readReg htif_exit_code)), used + 1))
    else
      let i := i + 1
      if i == plat_insns_per_tick then do
        tick_clock ()
        pure (.inr (0, used + 1))
      else
        pure (.inr (i, used + 1))

end Vsa
