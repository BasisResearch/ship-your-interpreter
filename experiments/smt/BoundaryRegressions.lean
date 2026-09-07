import Vsa.Sim.OutputAliasSnapshot
import Vsa.Sim.OutputAliasPhysical
import Vsa.Sim.BlockMem
import Vsa.Sim.NativeNameAudit.Loaded
import Vsa.Sim.NativeNameAudit.InitialExclusion
import Vsa.Sim.NativeNameAudit.ControlLoaded
import Vsa.Sim.OutputAliasOwnedExclusion
import Vsa.Sim.OutputAliasRefutation
import Vsa.Sim.AstAccessAudit.AccessOwnedExclusion
import Vsa.Sim.AstAccessAudit.AccessRefutation
import Lean

/-! Deterministic sparse Sail replays of four initial-state witnesses.
Imported source derivations and dense admission/exclusion theorems are checked
separately. These executable observations do not prove sparse-to-dense execution
agreement. Successful rows survive errors; terminal attempts remain separate.
-/

open Lean Sail LeanRV64DExecutable Register
open Vsa Vsa.Machine Vsa.MemRepr
open Vsa.Sim.OutputAliasLoaded

namespace BoundaryRegressions

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
    ("binding_name_pointer", toJson (readLE? s 0x81000048 8)),
    ("binding_name_bytes", toJson ((List.range 8).map fun i => readLE? s (0x8001bb91 + i) 1)),
    ("ast_name_pointer", toJson (readLE? s 0x820000a8 8)),
    ("ast_name_bytes", toJson ((List.range 8).map fun i => readLE? s (0x820000c0 + i) 1)),
    ("native_value_name_pointer", toJson (readLE? s 0x810000a0 8)),
    ("second_statement_pointer", toJson (readLE? s 0x82000008 8)),
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
    ("mcause", toJson ((s.regs.get? mcause).map BitVec.toNat)),
    ("mtvec", toJson ((s.regs.get? mtvec).map BitVec.toNat)),
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
  status : String
  state : MState
  tick : Nat
  steps : Nat
  trace : Array Lean.Json
  terminalEvent : Lean.Json := Lean.Json.null
  exitCode : Option Nat := none

/-- Execute each Sail step independently. The terminal attempt is separate
from successful rows, whether it halts or fails after partial state updates. -/
def replay (fuel : Nat) (initial : MState) : ReplayResult := Id.run do
  let mut s := initial
  let mut tick := 0
  let mut used := 0
  let mut rows : Array Lean.Json := #[]
  for _ in [:fuel] do
    match (Vsa.stepOnce tick used).run s with
    | .error e post =>
      return {
        status := "sail_error", state := s, tick := tick,
        steps := used, trace := rows,
        terminalEvent := Lean.Json.mkObj [
          ("kind", toJson "sail_error"), ("error", toJson e.print),
          ("attempt", traceRow s post tick used),
          ("before_full_state", fullState s),
          ("error_full_state", fullState post),
          ("before_memory_observations", stateEvent s tick used),
          ("error_memory_observations", stateEvent post tick used)] }
    | .ok (.inl (exitCode, used')) post =>
      return {
        status := "htif_halt", state := post, tick := tick,
        steps := used', trace := rows, exitCode := exitCode,
        terminalEvent := Lean.Json.mkObj [
          ("kind", toJson "htif_halt"), ("exit_code", toJson exitCode),
          ("attempt", traceRow s post tick used),
          ("before_full_state", fullState s),
          ("halt_full_state", fullState post),
          ("halt_memory_observations", stateEvent post tick used')] }
    | .ok (.inr (tick', used')) post =>
      rows := rows.push (traceRow s post tick used)
      s := post
      tick := tick'
      used := used'
  return {
    status := "fuel_exhausted", state := s, tick := tick,
    steps := used, trace := rows }

/-- Admission classification is checked against the exact dense snapshot. -/
inductive CurrentBoundary (p : Vsa.While.Program) (c : Vsa.Machine.Config) where
  | admitted (name : String)
      (proof : Vsa.Refine.Loaded Vsa.Sim.LayoutInstance.interpRunLayout p c)
  | excluded (name : String)
      (proof : ¬ Vsa.Refine.Loaded Vsa.Sim.LayoutInstance.interpRunLayout p c)

def CurrentBoundary.status {p c} : CurrentBoundary p c → String
  | .admitted _ _ => "admitted"
  | .excluded _ _ => "excluded"

def CurrentBoundary.admission {p c} : CurrentBoundary p c → Option String
  | .admitted name _ => some name
  | .excluded _ _ => none

def CurrentBoundary.exclusion {p c} : CurrentBoundary p c → Option String
  | .admitted _ _ => none
  | .excluded name _ => some name

/-- Each source-output string carries its kernel-checked source derivation. -/
structure Case where
  id : String
  program : Vsa.While.Program
  expectedOutput : String
  sourceProof : Vsa.While.BigStep program expectedOutput
  log : List Vsa.Sim.WEntry
  oracle : String
  admission : String
  currentBoundary : CurrentBoundary program (physicalConfig (Vsa.Sim.writeLog snapshotMem log))
  executionProof : Option String

open Vsa.Sim.NativeNameAudit Vsa.Sim.AstAccessAudit

def cases : List Case := [
  { id := "ast_output_alias", program := Vsa.While.LoadedOutputAlias.program,
    expectedOutput := "\n", sourceProof := Vsa.While.LoadedOutputAlias.program_bigStep,
    log := [], oracle := "Vsa.While.LoadedOutputAlias.program_bigStep",
    admission := "Vsa.Sim.OutputAliasLoaded.snapshot_loaded (BeforeAstOwnership)",
    currentBoundary := .excluded "Vsa.Sim.OutputAliasLoaded.snapshot_not_loaded"
      (Vsa.Sim.OutputAliasLoaded.snapshot_not_loaded _),
    executionProof := some "Vsa.Sim.OutputAliasLoaded.snapshot_halts_twoLF" },
  { id := "ast_unreadable", program := accessProgram, expectedOutput := "",
    sourceProof := access_bigStep, log := accessLog,
    oracle := "Vsa.Sim.AstAccessAudit.access_bigStep",
    admission := "Vsa.Sim.AstAccessAudit.access_loaded (BeforeAstReadability)",
    currentBoundary := .excluded "Vsa.Sim.AstAccessAudit.access_not_loaded"
      (Vsa.Sim.AstAccessAudit.access_not_loaded _),
    executionProof := some "Vsa.Sim.AstAccessAudit.access_not_halts" },
  { id := "native_name_alias", program := nativeNameProgram, expectedOutput := "\n\n",
    sourceProof := nativeName_bigStep, log := nativeNameLog,
    oracle := "Vsa.Sim.NativeNameAudit.nativeName_bigStep",
    admission := "Vsa.Sim.NativeNameAudit.nativeName_loaded (BeforeRuntimeOwnership)",
    currentBoundary := .excluded "Vsa.Sim.NativeNameAudit.nativeName_not_loaded"
      (nativeName_not_loaded _), executionProof := none },
  { id := "stable_control", program := nativeNameProgram, expectedOutput := "\n\n",
    sourceProof := nativeName_bigStep,
    log := nativeNameLog ++ [(0x81000048, 8, 0x81000210#64)],
    oracle := "Vsa.Sim.NativeNameAudit.nativeName_bigStep",
    admission := "Vsa.Sim.NativeNameAudit.Control.loaded (current)",
    currentBoundary := .admitted "Vsa.Sim.NativeNameAudit.Control.loaded" Control.loaded,
    executionProof := none }]

#print axioms Vsa.While.LoadedOutputAlias.program_bigStep
#print axioms Vsa.Sim.OutputAliasLoaded.snapshot_loaded
#print axioms Vsa.Sim.OutputAliasLoaded.snapshot_not_loaded
#print axioms Vsa.Sim.OutputAliasLoaded.snapshot_halts_twoLF
#print axioms access_bigStep
#print axioms access_loaded
#print axioms access_not_loaded
#print axioms access_not_halts
#print axioms nativeName_bigStep
#print axioms nativeName_loaded
#print axioms nativeName_not_loaded
#print axioms Control.loaded

end BoundaryRegressions

def main (args : List String) : IO UInt32 := do
  let [caseId, outputPath] := args | throw (IO.userError "expected CASE OUTPUT.json")
  let some fixture := BoundaryRegressions.cases.find? (fun c => c.id == caseId)
    | throw (IO.userError s!"unknown case: {caseId}")
  let initial := physicalState (Vsa.Sim.writeLog BoundaryRegressions.sparseMemory fixture.log)
  let result := BoundaryRegressions.replay 20000 initial
  let overrides := fixture.log.map fun (a, width, value) =>
    Json.mkObj [("address", toJson a), ("width", toJson width), ("value", toJson value.toNat)]
  let report := Json.mkObj [
    ("schema", toJson 1), ("case", toJson fixture.id),
    ("status", toJson result.status), ("fuel", toJson (20000 : Nat)),
    ("steps", toJson result.steps), ("tick", toJson result.tick),
    ("exit_code", toJson result.exitCode),
    ("expected_source_output", toJson fixture.expectedOutput),
    ("source_oracle", toJson fixture.oracle), ("dense_admission", toJson fixture.admission),
    ("current_boundary_status", toJson fixture.currentBoundary.status),
    ("current_admission", toJson fixture.currentBoundary.admission),
    ("current_exclusion", toJson fixture.currentBoundary.exclusion),
    ("independent_dense_execution_theorem", toJson fixture.executionProof),
    ("initial_overrides", toJson overrides),
    ("initial_full_state", BoundaryRegressions.fullState initial),
    ("trace", toJson result.trace), ("terminal_event", result.terminalEvent),
    ("final_full_state", BoundaryRegressions.fullState result.state),
    ("evidence_kind", toJson "actual Sail sparse-runtime regression"),
    ("memory_model", toJson "Fixed image and snapshotWords extents plus explicit overrides; absent bytes retain Sail zero-default behavior"),
    ("dense_memory_evaluated", toJson false),
    ("replay_establishes_dense_loaded_execution", toJson false),
    ("complete_contract_validation", toJson false)]
  IO.FS.writeFile outputPath (report.compress ++ "\n")
  IO.println (Json.mkObj [("case", toJson fixture.id), ("status", toJson result.status),
    ("steps", toJson result.steps), ("output", toJson (Vsa.Machine.output result.state))]).compress
  return if result.status == "fuel_exhausted" then 2 else 0
