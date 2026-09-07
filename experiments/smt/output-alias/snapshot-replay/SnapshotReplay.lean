import Vsa.Sim.OutputAliasSnapshot
import Vsa.Sim.OutputAliasPhysical
import Lean

/-! Executable sparse replay of the explicit snapshot's byte function.
No boot or state repair occurs. No executable definition references snapshotMem.
This file does not prove a trace of the dense Loaded state: absent bytes read
as zero in Sail, but the memory-equivalence execution lift is not yet proved.
-/

open Lean Sail LeanRV64DExecutable Register
open Vsa Vsa.Machine Vsa.MemRepr
open Vsa.Sim.OutputAliasLoaded

namespace OutputAliasSnapshotReplay

/-- Populate only the fixed image and finite snapshot field extents. Use the
byte function even for overlapping extents, preserving its first-match rule. -/
def sparseMemory : Mem := Id.run do
  let mut m : Mem := ∅
  for a in [0x80000000:0x8001acf0] do
    m := m.insert a (snapshotByte a)
  for (base, width, _) in snapshotWords do
    for offset in [:width] do
      let a := base + offset
      m := m.insert a (snapshotByte a)
  return m

def readLE? (s : MState) (address width : Nat) : Option Nat := do
  let mut n := 0
  for offset in [:width] do
    let b ← s.mem[address + offset]?
    n := n + (b.toNat <<< (8 * offset))
  return n

def stateEvent (s : MState) (tick used : Nat) : Lean.Json :=
  Lean.Json.mkObj [
    ("steps", toJson used), ("tick", toJson tick),
    ("pc", toJson ((s.regs.get? PC).map BitVec.toNat)),
    ("a0", toJson ((s.regs.get? x10).map BitVec.toNat)),
    ("a1", toJson ((s.regs.get? x11).map BitVec.toNat)),
    ("a2", toJson ((s.regs.get? x12).map BitVec.toNat)),
    ("sp", toJson ((s.regs.get? x2).map BitVec.toNat)),
    ("buffer", toJson (readLE? s 0x8001bb97 1)),
    ("buffer_next", toJson (readLE? s 0x8001bb98 1)),
    ("left_pointer", toJson (readLE? s 0x82000108 8)),
    ("output", toJson (Vsa.Machine.output s))]

structure ReplayResult where
  halted : Bool
  exitCode : Option Nat
  tick : Nat
  steps : Nat
  interpReturn : Option Lean.Json
  events : Array Lean.Json

/-- Stop only on actual stepOnce halt or fuel exhaustion. Observe the
interpreter return before executing main's continuation. -/
def replay : Nat → Nat → Nat → Option Lean.Json → Array Lean.Json → SailM ReplayResult
  | 0, tick, used, interpReturn, events =>
    pure ⟨false, none, tick, used, interpReturn, events⟩
  | fuel + 1, tick, used, interpReturn, events => do
    let s ← get
    let pc := (← readReg PC).toNat
    let interpReturn :=
      if pc == 0x800045ec && interpReturn.isNone then
        some (stateEvent s tick used)
      else interpReturn
    let events :=
      if [0x800043ec, 0x80002f7c, 0x8000281c, 0x8000285c,
          0x80006ea0, 0x800045ec, 0x80000038, 0x80005d18,
          0x8000f0c0].contains pc then
        events.push (stateEvent s tick used)
      else events
    match ← Vsa.stepOnce tick used with
    | .inl (exitCode, used') =>
      pure ⟨true, exitCode, tick, used', interpReturn, events⟩
    | .inr (tick', used') =>
      replay fuel tick' used' interpReturn events

end OutputAliasSnapshotReplay

def main (args : List String) : IO UInt32 := do
  let fuel := (args.head?.bind String.toNat?).getD 2000000
  let initial := physicalState OutputAliasSnapshotReplay.sparseMemory
  match (OutputAliasSnapshotReplay.replay fuel 0 0 none #[]).run initial with
  | .error e final =>
    IO.println (Lean.Json.mkObj [
      ("status", toJson "sail_error"), ("error", toJson e.print),
      ("final_pc", toJson ((final.regs.get? PC).map BitVec.toNat)),
      ("final_output", toJson (Vsa.Machine.output final)),
      ("dense_loaded_execution_proved", toJson false)]).compress
    return 1
  | .ok result final =>
    let expected := result.halted && result.exitCode == some 0 &&
      result.interpReturn.isSome && Vsa.Machine.output final == "\n\n"
    IO.println (Lean.Json.mkObj [
      ("status", toJson (if result.halted then "htif_halted" else "fuel_exhausted")),
      ("fuel", toJson fuel), ("halted", toJson result.halted),
      ("exit_code", toJson result.exitCode), ("steps", toJson result.steps),
      ("initial_state", OutputAliasSnapshotReplay.stateEvent initial 0 0),
      ("interp_return", toJson result.interpReturn),
      ("final_state", OutputAliasSnapshotReplay.stateEvent final result.tick result.steps),
      ("events", toJson result.events), ("expected_alias_behavior", toJson expected),
      ("memory_model", toJson "Fixed image plus all snapshotWords extents; other bytes absent and read as zero"),
      ("memory_caveat", toJson "Every nonzero snapshot byte must be included. No dense/sparse stepOnce equivalence theorem is assumed or proved."),
      ("loaded_scope", toJson "snapshot_loaded applies to dense snapshotMem, not this sparse map"),
      ("dense_memory_evaluated", toJson false),
      ("dense_loaded_execution_proved", toJson false)]).compress
    return if expected then 0 else 1
