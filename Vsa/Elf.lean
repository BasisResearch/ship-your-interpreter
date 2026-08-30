import LeanRiscv
import Vsa.ElfBytes

/-!
# The ELF binary as a Lean term, and its execution semantics

`c/while-riscv-htif.elf` is the source of truth for this development: a
bare-metal RISC-V build of the WHILE interpreter with a WHILE script linked
into the image, doing console I/O over the HTIF `tohost` mailbox.

This file embeds the ELF bytes as a closed Lean term, parses them with
ELFSage, and defines a *pure*, fuel-bounded execution function on top of the
Sail-generated RV64D semantics (`try_step`). Because `SailM` is an `EStateM`,
running the machine is a pure computation: the observable behavior of the
binary (console output + HTIF exit code) is a well-defined Lean value that
theorems can talk about.
-/

open LeanRV64DExecutable
open Register

namespace Vsa

/-- Decode one hex digit (lowercase, as produced by `xxd -p`). -/
def hexVal (c : Char) : UInt8 :=
  if c.isDigit then c.toUInt8 - '0'.toUInt8
  else c.toUInt8 - 'a'.toUInt8 + 10

/-- Decode a hex string (even length, lowercase) to bytes. -/
def hexToBytes (s : String) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (s.length / 2)
  let mut pending : Option UInt8 := none
  for c in s.toList do
    match pending with
    | none => pending := some (hexVal c)
    | some hi =>
      out := out.push ((hi <<< 4) ||| hexVal c)
      pending := none
  return out

/-- The raw bytes of `c/while-riscv-htif.elf`. -/
def elfBytes : ByteArray := hexToBytes elfHex

/-- The parsed ELF file. Parsing happens inside Lean via ELFSage. -/
def whileElf? : Except String ELF64File :=
  match mkRawELFFile? elfBytes with
  | .error e => .error e
  | .ok (.elf64 elf) => .ok elf
  | .ok (.elf32 _) => .error "expected a 64-bit ELF file"

/-- Observable result of running the machine for a bounded number of steps. -/
structure RunResult where
  /-- `some code` iff the binary signalled exit via HTIF within the fuel. -/
  exitCode : Option Nat
  /-- Everything the machine printed (HTIF console device). -/
  output : String
  /-- Loop iterations consumed (fuel actually used). -/
  steps : Nat
  deriving Repr, DecidableEq

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

open Sail in
/-- Fuel-bounded top-level loop: iterate `stepOnce` until the machine halts.
Returns the exit code and step count, or `none` if fuel ran out first. -/
def runSteps : Nat → Nat → Nat → SailM (Option Nat × Nat)
  | 0, _, used => pure (none, used)
  | fuel + 1, i, used => do
    match ← stepOnce i used with
    | .inl r => pure r
    | .inr (i', used') => runSteps fuel i' used'

open Sail ConcurrencyInterfaceV1 in
/-- The initial machine state: memory loaded from the ELF segments, no
registers written yet. -/
def initState (elf : ELF64File) :
    SequentialState RegisterType trivialChoiceSource :=
  ⟨Std.ExtDHashMap.emptyWithCapacity, (), initializeMemory .B64 elf, default,
    default, default⟩

/-- Pure, fuel-bounded execution of an ELF under the Sail RV64D semantics.
This is *the semantics of the binary*: everything downstream abstracts it. -/
def runElf (elf : ELF64File) (fuel : Nat) : Except String RunResult :=
  let prog : SailM (Option Nat × Nat) := do
    setupElf elf
    runSteps fuel 0 0
  match prog.run (initState elf) with
  | .ok (exit?, steps) s =>
    .ok ⟨exit?, String.join s.sailOutput.toList, steps⟩
  | .error e _ => .error e.print

/-- The observable behavior of `c/while-riscv-htif.elf` with the given fuel. -/
def runWhileElf (fuel : Nat) : Except String RunResult :=
  whileElf?.bind fun elf => runElf elf fuel

end Vsa

-- build-speed baseline marker (2026-08-29): edits to this file rebuild the world (573 importers).
-- See experiments/build-speed-exponentiation-plan.md Axis 2.

/-- Baseline cone marker (2026-08-29): an olean-changing edit here rebuilds the
573-importer cone. Used once to measure the per-module build-time baseline;
see `experiments/build-speed-exponentiation-plan.md` Axis 2/3. -/
theorem elf_cone_marker : True := trivial
