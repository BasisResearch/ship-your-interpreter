import Vsa.ElfRun
import Vsa.Machine
import Lean

/- Scratch execution experiment. This is not a theorem or a Loaded witness.
   Both cases use the fixed ELF and production Vsa.stepOnce. -/
open Lean Sail LeanRV64DExecutable Register
open Vsa Vsa.Machine

namespace AliasMachine

abbrev EntryResult := Nat × Nat × Bool

/-- Stop before target instruction. False means fuel exhausted or HTIF halted. -/
def untilPC : Nat → Nat → Nat → Nat → SailM EntryResult
  | 0, _, tick, used => pure (tick, used, false)
  | fuel + 1, target, tick, used => do
    if (← readReg PC).toNat == target then
      return (tick, used, true)
    match ← Vsa.stepOnce tick used with
    | .inl (_, used') => pure (tick, used', false)
    | .inr (tick', used') => untilPC fuel target tick' used'

def putLE (s : MState) (address width value : Nat) : MState := Id.run do
  let mut s := s
  for offset in [:width] do
    s := { s with mem := s.mem.insert (address + offset) (BitVec.ofNat 8 (value >>> (8 * offset))) }
  return s

def zeroPage (s : MState) (address : Nat) : MState := Id.run do
  let mut s := s
  for offset in [:4096] do
    s := { s with mem := s.mem.insert (address + offset) 0 }
  return s

def putString (s : MState) (address : Nat) (value : String) : MState := Id.run do
  let mut s := s
  for offset in [:value.toUTF8.size] do
    s := putLE s (address + offset) 1 (value.toUTF8[offset]!.toNat)
  return putLE s (address + value.toUTF8.size) 1 0

/-- Both cases differ only in the left string pointer at AST+0x108. -/
def patch (s : MState) (alias : Bool) : MState := Id.run do
  let mut s := zeroPage (zeroPage s 0x81000000) 0x82000000
  -- Native global environment, independently allocated from the AST.
  for (address, width, value) in [
      (0x81000000, 4, 3), (0x81000004, 4, 8),
      (0x81000008, 8, 0x81000040), (0x81000010, 8, 0x81000080),
      (0x81000018, 8, 0)] do
    s := putLE s address width value
  for (idx, name, address, fn) in [
      (0, "print", 0x81000200, 0x80002ed4),
      (1, "println", 0x81000210, 0x80002f7c),
      (2, "assert", 0x81000220, 0x80002df4)] do
    s := putString s address name
    s := putLE s (0x81000040 + 8 * idx) 8 address
    s := putLE s (0x81000080 + 24 * idx) 4 5
    s := putLE s (0x81000088 + 24 * idx) 8 address
    s := putLE s (0x81000090 + 24 * idx) 8 fn
  -- println(); if ("" == "\n") println();
  for (address, width, value) in [
      (0x82000000, 8, 0x82000020), (0x82000008, 8, 0x82000040),
      (0x82000020, 4, 0), (0x82000028, 8, 0x82000080),
      (0x82000040, 4, 3), (0x82000048, 8, 0x820000c0),
      (0x82000050, 8, 0x82000020), (0x82000058, 8, 0),
      (0x82000080, 4, 9), (0x82000088, 8, 0x820000a0),
      (0x82000090, 8, 0), (0x82000098, 4, 0),
      (0x820000a0, 4, 4), (0x820000a8, 8, 0x81000210),
      (0x820000c0, 4, 6), (0x820000c8, 4, 19),
      (0x820000d0, 8, 0x82000100), (0x820000d8, 8, 0x82000120),
      (0x82000100, 4, 1),
      (0x82000108, 8, if alias then 0x8001bb97 else 0x82000160),
      (0x82000120, 4, 1), (0x82000128, 8, 0x82000140),
      (0x82000140, 1, 10), (0x82000141, 1, 0),
      (0x82000160, 1, 0), (0x8001bb97, 1, 0),
      (0x87fffe10, 8, 0x81000000), (0x87fffe18, 4, 0)] do
    s := putLE s address width value
  -- Keep the reached physical register state except the array/count arguments.
  s := { s with regs := (s.regs.insert x11 (BitVec.ofNat 64 0x82000000)).insert x12 (BitVec.ofNat 64 2) }
  return s

def readLE? (s : MState) (address width : Nat) : Option Nat := do
  let mut n := 0
  for offset in [:width] do
    let b ← s.mem[address + offset]?
    n := n + (b.toNat <<< (8 * offset))
  return n

def imageMismatches (expected actual : MState) : Nat := Id.run do
  let mut mismatches := 0
  for address in [0x80000000:0x8001acf0] do
    if expected.mem[address]? != actual.mem[address]? then
      mismatches := mismatches + 1
  return mismatches

def number (n : Nat) : Lean.Json := toJson n

def maybeNumber (n : Option Nat) : Lean.Json := toJson n

/-- Executable read checks, reported separately from any Lean proposition. -/
def runtimeChecks (s : MState) : Lean.Json := Id.run do
  let mut checks : Array Lean.Json := #[]
  let mut fields := [
    (0x8001b970, 8, 0x8001b538), (0x8001b548, 8, 0x8001bb20),
    (0x8001b580, 8, 0x80005d2c), (0x8001bb20, 8, 0x8001bb97),
    (0x8001bb28, 4, 0), (0x8001bb2c, 4, 0),
    (0x8001bb30, 2, 0x200a), (0x8001bb32, 2, 1),
    (0x8001bb38, 8, 0x8001bb97), (0x8001bb40, 4, 1),
    (0x8001bb48, 4, 0), (0x8001bb50, 8, 0x8001bb20),
    (0x8001bb60, 8, 0x8000efd4), (0x8001bbc0, 8, 0),
    (0x8001bbd0, 4, 0), (0x8001b9f8, 8, 0),
    (0x8001b9b0, 8, 0x80005d18), (0x8001b520, 8, 0),
    (0x8001b528, 4, 3), (0x8001b530, 8, 0x8001ba68),
    (0x8001bb70, 8, 0x8000f0c0), (0x8001bb78, 8, 0),
    (0x8001bb98, 8, 0), (0x87fffff8, 8, 0x80000038),
    (0x8001bb97, 1, 0), (0x87fffe10, 8, 0x81000000),
    (0x87fffe18, 4, 0)]
  for (file, flags, fd) in [(0x8001ba68, 4, 0), (0x8001bbd8, 0x12, 2)] do
    fields := fields ++ [
      (file + 16, 2, flags), (file + 18, 2, fd),
      (file + 8, 4, 0), (file + 112, 4, 0),
      (file + 48, 8, file), (file + 80, 8, 0x8000f0c0),
      (file + 88, 8, 0), (file + 120, 8, 0),
      (file + 160, 8, 0), (file + 176, 4, 0)]
  for (address, width, expected) in fields do
    let actual := readLE? s address width
    checks := checks.push (Lean.Json.mkObj [
      ("address", number address), ("width", number width),
      ("expected", number expected), ("actual", maybeNumber actual),
      ("passed", toJson (actual == some expected))])
  return Lean.Json.mkObj [("read_checks", toJson checks),
    ("htif_payload_writes", maybeNumber ((s.regs.get? htif_payload_writes).map BitVec.toNat)),
    ("htif_tohost_present", toJson (s.regs.get? htif_tohost).isSome),
    ("output_empty", toJson s.sailOutput.isEmpty),
    ("a1", maybeNumber ((s.regs.get? x11).map BitVec.toNat)),
    ("a2", maybeNumber ((s.regs.get? x12).map BitVec.toNat)),
    ("atexit_lock_present", toJson (readLE? s 0x8001b978 8).isSome),
    ("buffer_present", toJson (readLE? s 0x8001bb97 1).isSome),
    ("full_stack_presence", toJson "not checked"),
    ("good_state", toJson "not checked"),
    ("loaded_proof", toJson "not constructed")]

def memFields (s : MState) : Lean.Json := Lean.Json.mkObj <|
  [("buffer", 0x8001bb97, 1), ("buffer_next", 0x8001bb98, 1),
   ("stdout_cursor", 0x8001bb20, 8), ("stdout_write_count", 0x8001bb2c, 4),
   ("stdout_flags", 0x8001bb30, 2), ("saved_main_ra", 0x87fffff8, 8),
   ("left_pointer", 0x82000108, 8)].map fun (key, address, width) =>
      (key, maybeNumber (readLE? s address width))

/-- Compact causal trace; no instruction or memory transition is summarized. -/
def runCase : Nat → Nat → Nat → Array Lean.Json → SailM (EntryResult × Array Lean.Json)
  | 0, tick, used, events => pure ((tick, used, false), events)
  | fuel + 1, tick, used, events => do
    let pc := (← readReg PC).toNat
    let mut events := events
    if [0x80002f7c, 0x8000281c, 0x8000285c, 0x80006ea0, 0x800045ec].contains pc then
      events := events.push (Lean.Json.mkObj [
        ("step", number used), ("pc", number pc),
        ("a0", number (← readReg x10).toNat),
        ("a1", number (← readReg x11).toNat),
        ("a2", number (← readReg x12).toNat)])
    if pc == 0x800045ec then return ((tick, used, true), events)
    match ← Vsa.stepOnce tick used with
    | .inl (_, used') => pure ((tick, used', false), events)
    | .inr (tick', used') => runCase fuel tick' used' events

def executeCase (label : String) (alias : Bool) (s : MState)
    (tick used fuel : Nat) : IO Bool := do
  let start := patch s alias
  let initial := memFields start
  match (runCase fuel tick used #[]).run start with
  | .error e _ => throw (IO.userError s!"{label}: {e.print}")
  | .ok ((_, finalUsed, reached), events) final =>
    IO.println (Lean.Json.mkObj [
      ("case", toJson label), ("reached_interp_return", toJson reached),
      ("steps", number (finalUsed - used)), ("initial_memory", initial),
      ("initial_runtime_checks", runtimeChecks start),
      ("final_memory", memFields final), ("events", toJson events),
      ("fixed_image_changes", number (imageMismatches s final)),
      ("output", toJson (String.join final.sailOutput.toList)),
      ("loaded_verified", toJson false)]).compress
    return reached

end AliasMachine

def main (args : List String) : IO UInt32 := do
  let fuel := (args.head?.bind String.toNat?).getD 2000000
  let elf ← match Vsa.whileElf? with
    | .ok elf => pure elf
    | .error e => throw (IO.userError e)
  let boot : SailM AliasMachine.EntryResult := do
    Vsa.setupElf elf
    AliasMachine.untilPC fuel 0x800043ec 0 0
  match boot.run (Vsa.initState elf) with
  | .error e _ => throw (IO.userError s!"boot: {e.print}")
  | .ok (tick, used, reached) s =>
    unless reached do throw (IO.userError "boot did not reach interp_run")
    -- Reject a different startup ABI instead of silently patching it away.
    unless s.regs.get? x2 == some (BitVec.ofNat 64 0x87fffd00) &&
        s.regs.get? x3 == some (BitVec.ofNat 64 0x8001b510) &&
        s.regs.get? x1 == some (BitVec.ofNat 64 0x800045ec) &&
        s.regs.get? x10 == some (BitVec.ofNat 64 0x87fffe10) &&
        s.regs.get? x13 == some (BitVec.ofNat 64 0) do
      throw (IO.userError "unexpected interp_run entry register geometry")
    IO.println (Lean.Json.mkObj [("boot_steps", toJson used),
      ("boot_output", toJson (String.join s.sailOutput.toList)),
      ("fixed_image_changes", toJson (AliasMachine.imageMismatches (Vsa.initState elf) s)),
      ("loaded_verified", toJson false)]).compress
    let control ← AliasMachine.executeCase "control" false s tick used fuel
    let alias ← AliasMachine.executeCase "alias" true s tick used fuel
    return if control && alias then 0 else 1
