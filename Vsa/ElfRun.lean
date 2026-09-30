import Vsa.Elf
import Vsa.ElfBytes

open LeanRV64DExecutable
open Register

namespace Vsa

def hexVal (c : Char) : UInt8 :=
  if c.isDigit then c.toUInt8 - '0'.toUInt8
  else c.toUInt8 - 'a'.toUInt8 + 10

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

def elfBytes : ByteArray := hexToBytes elfHex

def whileElf? : Except String ELF64File :=
  match mkRawELFFile? elfBytes with
  | .error e => .error e
  | .ok (.elf64 elf) => .ok elf
  | .ok (.elf32 _) => .error "expected a 64-bit ELF file"

structure RunResult where

  exitCode : Option Nat

  output : String

  steps : Nat
  deriving Repr, DecidableEq

open Sail in

def runSteps : Nat → Nat → Nat → SailM (Option Nat × Nat)
  | 0, _, used => pure (none, used)
  | fuel + 1, i, used => do
    match ← stepOnce i used with
    | .inl r => pure r
    | .inr (i', used') => runSteps fuel i' used'

open Sail ConcurrencyInterfaceV1 in

def initState (elf : ELF64File) :
    SequentialState RegisterType trivialChoiceSource :=
  ⟨Std.ExtDHashMap.emptyWithCapacity, (), initializeMemory .B64 elf, default,
    default, default⟩

def runElf (elf : ELF64File) (fuel : Nat) : Except String RunResult :=
  let prog : SailM (Option Nat × Nat) := do
    setupElf elf
    runSteps fuel 0 0
  match prog.run (initState elf) with
  | .ok (exit?, steps) s =>
    .ok ⟨exit?, String.join s.sailOutput.toList, steps⟩
  | .error e _ => .error e.print

def runWhileElf (fuel : Nat) : Except String RunResult :=
  whileElf?.bind fun elf => runElf elf fuel

end Vsa
