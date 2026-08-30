import Vsa.Elf
import Vsa.ElfBytes

/-!
# The ELF binary as a Lean term, and its fuel-bounded runner

Split out of `Vsa.Elf` (2026-08-29, build-speed campaign Axis 2): the
embedded ELF bytes, the ELFSage parse, and the pure fuel-bounded execution
function. Only `Vsa.ElfMono` and `VsaRun` consume these, so runner edits and
ELF regeneration rebuild a 3-module cone instead of the world.

Because `SailM` is an `EStateM`, running the machine is a pure computation:
the observable behavior of the binary (console output + HTIF exit code) is a
well-defined Lean value that theorems can talk about.
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
