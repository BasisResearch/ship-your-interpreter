import LeanRiscv

open LeanRV64DExecutable
open Register

namespace Vsa

open Sail in
open LeanRV64DExecutable.Functions in

def setupElf (elf : ELF64File) : SailM Unit := do
  sail_model_init ()
  initializeRegisters elf
  init_model ""
  cycle_count ()

  writeReg PC (elf.file_header.e_entry : UInt64).toBitVec

open Sail in
open LeanRV64DExecutable.Functions in

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
