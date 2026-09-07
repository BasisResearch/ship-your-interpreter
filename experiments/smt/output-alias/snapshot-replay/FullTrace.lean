import Vsa.Sim.OutputAliasSnapshot
import Vsa.Sim.OutputAliasPhysical
import Vsa.Sim.BlockPilot
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

/-- Record both physical presence and the actual zero-default Sail read value. -/
def byteTrace (s : MState) (address : Nat) : Lean.Json :=
  let value := s.mem[address]?
  Lean.Json.mkObj [("address", toJson address), ("present", toJson value.isSome),
    ("value", toJson (value.map BitVec.toNat)),
    ("effective", toJson ((value.getD 0).toNat))]

def effectiveRead (s : MState) (address width : Nat) : Nat := Id.run do
  let mut n := 0
  for offset in [:width] do
    let b := (s.mem[address + offset]?).getD 0
    n := n + (b.toNat <<< (8 * offset))
  return n

def gprTrace (s : MState) : Array Lean.Json := Id.run do
  let mut out := #[]
  for n in [1:32] do
    let v := Vsa.Sim.gprGet s n
    out := out.push (Lean.Json.mkObj [("register", toJson n),
      ("present", toJson v.isSome), ("value", toJson (v.map BitVec.toNat))])
  return out

/-- Decode only base integer LOAD (opcode 0x03). This is untrusted trace
annotation, not a substitute for Sail decoding or a semantic load theorem. -/
def loadTrace (s : MState) (word : Nat) : Lean.Json := Id.run do
  if word &&& 0x7f != 0x03 then return Lean.Json.null
  let rs1 := (word >>> 15) &&& 0x1f
  let rd := (word >>> 7) &&& 0x1f
  let funct3 := (word >>> 12) &&& 7
  let immediate := BitVec.ofNat 12 (word >>> 20)
  let width : Option Nat := match funct3 with
    | 0 | 4 => some 1
    | 1 | 5 => some 2
    | 2 | 6 => some 4
    | 3 => some 8
    | _ => none
  let base : Option (BitVec 64) :=
    if rs1 == 0 then some 0 else Vsa.Sim.gprGet s rs1
  let address := base.map fun b => (b + immediate.signExtend 64).toNat
  let mut bytes : Array Lean.Json := #[]
  match address, width with
  | some a, some w =>
    for offset in [:w] do bytes := bytes.push (byteTrace s (a + offset))
  | _, _ => pure ()
  return Lean.Json.mkObj [("rs1", toJson rs1), ("rd", toJson rd),
    ("funct3", toJson funct3), ("immediate_signed", toJson immediate.toInt),
    ("base", toJson (base.map BitVec.toNat)), ("width", toJson width),
    ("address", toJson address), ("bytes", toJson bytes),
    ("integer_load_annotation_only", toJson true)]

def fullState (s : MState) : Lean.Json :=
  Lean.Json.mkObj [("pc", toJson ((s.regs.get? PC).map BitVec.toNat)),
    ("gprs", toJson (gprTrace s)),
    ("htif_payload_writes", toJson ((s.regs.get? htif_payload_writes).map BitVec.toNat)),
    ("htif_done", toJson (s.regs.get? htif_done)),
    ("htif_exit_code", toJson ((s.regs.get? htif_exit_code).map BitVec.toNat)),
    ("output", toJson (Vsa.Machine.output s)),
    ("sail_output", toJson s.sailOutput)]

/-- One pre-step state and its observed post-step output. Successor PC/GPRs
are the next row's pre-state, or final_full_state for the final row. -/
def traceRow (s post : MState) (tick used : Nat) : Lean.Json := Id.run do
  let pc := ((s.regs.get? PC).getD 0).toNat
  let word := effectiveRead s pc 4
  let mut instructionBytes : Array Lean.Json := #[]
  for offset in [:4] do
    instructionBytes := instructionBytes.push (byteTrace s (pc + offset))
  return Lean.Json.mkObj [
    ("steps", toJson used), ("tick", toJson tick),
    ("pc", toJson ((s.regs.get? PC).map BitVec.toNat)),
    ("gprs", toJson (gprTrace s)),
    ("instruction_word", toJson word),
    ("instruction_bytes", toJson instructionBytes),
    ("load", loadTrace s word),
    ("htif_payload_writes", toJson ((s.regs.get? htif_payload_writes).map BitVec.toNat)),
    ("output_before", toJson (Vsa.Machine.output s)),
    ("output_after", toJson (Vsa.Machine.output post)),
    ("output_changed", toJson (s.sailOutput != post.sailOutput)),
    ("next_pc", toJson ((post.regs.get? PC).map BitVec.toNat))]

structure ReplayResult where
  halted : Bool
  exitCode : Option Nat
  tick : Nat
  steps : Nat
  interpReturn : Option Lean.Json
  events : Array Lean.Json
  trace : Array Lean.Json

/-- Stop only on actual stepOnce halt or fuel exhaustion. Observe the
interpreter return before executing main's continuation. -/
def replay (fullTrace : Bool) :
    Nat → Nat → Nat → Option Lean.Json → Array Lean.Json → Array Lean.Json → SailM ReplayResult
  | 0, tick, used, interpReturn, events, trace =>
    pure ⟨false, none, tick, used, interpReturn, events, trace⟩
  | fuel + 1, tick, used, interpReturn, events, trace => do
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
    let result ← Vsa.stepOnce tick used
    let post ← get
    let trace := if fullTrace then trace.push (traceRow s post tick used) else trace
    match result with
    | .inl (exitCode, used') =>
      pure ⟨true, exitCode, tick, used', interpReturn, events, trace⟩
    | .inr (tick', used') =>
      replay fullTrace fuel tick' used' interpReturn events trace

end OutputAliasSnapshotReplay

def main (args : List String) : IO UInt32 := do
  let fuel := (args.head?.bind String.toNat?).getD 2000000
  let fullTrace := args.contains "--trace"
  let initial := physicalState OutputAliasSnapshotReplay.sparseMemory
  match (OutputAliasSnapshotReplay.replay fullTrace fuel 0 0 none #[] #[]).run initial with
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
      ("trace_enabled", toJson fullTrace), ("trace", toJson result.trace),
      ("final_full_state", OutputAliasSnapshotReplay.fullState final),
      ("trace_scope", toJson "Untrusted pre-step rows; opcode 0x03 integer loads annotated, missing bytes read with getD 0; next row/final_full_state gives successor"),
      ("memory_model", toJson "Fixed image plus all snapshotWords extents; other bytes absent and read as zero"),
      ("memory_caveat", toJson "Every nonzero snapshot byte must be included. No dense/sparse stepOnce equivalence theorem is assumed or proved."),
      ("loaded_scope", toJson "snapshot_loaded applies to dense snapshotMem, not this sparse map"),
      ("dense_memory_evaluated", toJson false),
      ("dense_loaded_execution_proved", toJson false)]).compress
    return if expected then 0 else 1
