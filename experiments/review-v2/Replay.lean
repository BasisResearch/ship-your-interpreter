import VsaBoot
import Vsa.ElfRun

/-!
# REVIEW2 native replay (lane V2): is the witness configuration the machine's?

Run: `lake env lean --run experiments/review-v2/Replay.lean <name>|all [fuel]`
(`VSA_BOOT_WORK`: the `gen_boot_witness.py` work directory holding the corpus ELFs).
For each generated witness `Gen.<Name>`, this parses the ELF (the embedded
`Vsa.elfHex` for `proof`, B3's corpus ELF otherwise), checks `ElfLoads`
natively, runs `Vsa.setupElf` + `Vsa.stepOnce` (the theorem's own step
function) for `entrySteps` steps, and compares the reached Sail state with the
witness `bootConfig (bootMem script log) regs entrySteps`: every byte of both
memories (so the entry view is a partial view of the reached memory), and
exactly the register facts `EntryRegs` names (`Vsa/Sim/Boot/Entry.lean`: the
pinned `GoodState` CSRs, PC, `htif_payload_writes`, `x1 … x31`) plus the empty
console. These are the hypotheses of `Gen.<Prog>.loadedEntry_fill`, so a
passing run means the kernel-checked witness covers the reached state. Then it
runs BOTH states to halt and prints their output and exit code. This is
native evaluation (not kernel-checked); it is the evidence that the
kernel-checked witness state is the state the binary reaches. Exit status 0
iff every check passes for every requested witness.
-/

open Vsa Vsa.Sim Vsa.Sim.Boot LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Vsa.Machine

/-- Exactly `n` iterations of `stepOnce`, reporting an early halt. -/
def stepN : Nat → Nat → Nat → SailM (Option (Nat × Nat))
  | 0, i, u => pure (some (i, u))
  | n + 1, i, u => do
    match ← Vsa.stepOnce i u with
    | .inl _ => pure none
    | .inr (i', u') => stepN n i' u'

structure Witness where
  name : String
  script : Nat
  log : PackedLog
  runs : RunTree
  regs : Nat → BitVec 64
  entrySteps : Nat
  expected : String

def witnesses : List Witness := [
  ⟨"proof", Gen.Proof.script, Gen.Proof.log, Gen.Proof.runs, Gen.Proof.regs, Gen.Proof.entrySteps, "55\n2500\n36\n"⟩,
  ⟨"while", Gen.While.script, Gen.While.log, Gen.While.runs, Gen.While.regs, Gen.While.entrySteps, "55\n2500\n36\n"⟩,
  ⟨"arithmetic", Gen.Arithmetic.script, Gen.Arithmetic.log, Gen.Arithmetic.runs, Gen.Arithmetic.regs, Gen.Arithmetic.entrySteps,
    "7\n9\n3\n1\n-2\n26\n1000000000000\n4\nfalse true false\ntrue true false true\ntrue true true false\nfalse true true false\n"⟩,
  ⟨"for", Gen.For.script, Gen.For.log, Gen.For.runs, Gen.For.regs, Gen.For.entrySteps,
    "1\n2\nFizz\n4\nBuzz\nFizz\n7\n8\nFizz\nBuzz\n11\nFizz\n13\n14\nFizzBuzz\n5050\n37\n3\n01234\n"⟩,
  ⟨"scope", Gen.Scope.script, Gen.Scope.log, Gen.Scope.runs, Gen.Scope.regs, Gen.Scope.entrySteps, "2\n3\n1\n20\n14 5\n3\nasserts ok\n"⟩,
  ⟨"strings", Gen.Strings.script, Gen.Strings.log, Gen.Strings.runs, Gen.Strings.regs, Gen.Strings.entrySteps,
    "hello world\nvalue: 42\n12\ntrue true\ntrue true\nline1\nline2\ntab\there\nquote: \"hi\"\n"⟩,
  ⟨"functions1", Gen.Functions1.script, Gen.Functions1.log, Gen.Functions1.runs, Gen.Functions1.regs, Gen.Functions1.entrySteps, "15\n11\n81\n3\n1\n"⟩,
  ⟨"functions2", Gen.Functions2.script, Gen.Functions2.log, Gen.Functions2.runs, Gen.Functions2.regs, Gen.Functions2.entrySteps, "true\n<fn make_adder>\n<fn>\n21\n"⟩,
  ⟨"err_divzero", Gen.ErrDivzero.script, Gen.ErrDivzero.log, Gen.ErrDivzero.runs, Gen.ErrDivzero.regs, Gen.ErrDivzero.entrySteps, "runtime error [line 1]: division by zero\n"⟩,
  ⟨"err_undefined", Gen.ErrUndefined.script, Gen.ErrUndefined.log, Gen.ErrUndefined.runs, Gen.ErrUndefined.regs, Gen.ErrUndefined.entrySteps, "runtime error [line 1]: undefined variable 'nope'\n"⟩]

def loadElf (name : String) : IO ELF64File := do
  if name == "proof" then
    match Vsa.whileElf? with
    | .ok elf => pure elf
    | .error e => throw (IO.userError e)
  else
    let work := (← IO.getEnv "VSA_BOOT_WORK").getD "/Users/kirancodes/vsa-b3-work"
    let bytes ← IO.FS.readBinFile (work ++ "/elfs/" ++ name ++ ".elf")
    match mkRawELFFile? bytes with
    | .ok (.elf64 elf) => pure elf
    | _ => throw (IO.userError "not a 64-bit ELF")

/-- Candidate key set of the witness memory: the loader pieces and the run tree. -/
def witnessKeys (t : RunTree) : List (Nat × Nat) :=
  bootPieces ++ t.runs.map fun r => (r.base, r.len)

def check (label : String) (ok : Bool) : IO Bool := do
  IO.println s!"  [{if ok then "OK " else "BAD"}] {label}"
  pure ok

def rangesAll (rs : List (Nat × Nat)) (f : Nat → Bool) : Bool :=
  rs.all fun (b, n) => (List.range n).all fun i => f (b + i)

def runToHalt (σ : MState) (i u fuel : Nat) : IO (Option (Nat × Nat) × String × Bool) := do
  match (Vsa.runSteps fuel i u).run σ with
  | .ok (e?, n) s => pure ((e?.map (·, n)), Vsa.Machine.output s, true)
  | .error err _ => do IO.println s!"  machine error: {err.print}"; pure (none, "", false)

def checkOne (w : Witness) (fuel : Nat) : IO Bool := do
  IO.println s!"== {w.name} (entrySteps = {w.entrySteps}, stores = {w.log.len})"
  let elf ← loadElf w.name
  let mut ok := true
  ok := (← check "ElfLoads: the parsed ELF's loader pieces are imagePieces script"
    (decide (elfPieces elf = imagePieces w.script))) && ok
  let wmem := bootMem w.script w.log
  let ρ : SailM (Option (Nat × Nat)) := do Vsa.setupElf elf; stepN w.entrySteps 0 0
  match ρ.run (Vsa.initState elf) with
  | .error e _ => do IO.println s!"  replay error: {e.print}"; pure false
  | .ok none _ => do IO.println "  replay: halted before entrySteps"; pure false
  | .ok (some (i, u)) σ => do
    ok := (← check s!"tick/steps after replay: i = {i} (witness {w.entrySteps % 2}), used = {u}"
      (i == w.entrySteps % 2 && u == w.entrySteps)) && ok
    ok := (← check "PC = 0x800043ec" ((σ.regs.get? Register.PC).map (· == (0x800043ec : BitVec 64)) == some true)) && ok
    ok := (← check "no console output before entry" (σ.sailOutput.size == 0)) && ok
    -- memory: size + pointwise on the witness key set (⇒ equality of the maps)
    let keys := witnessKeys w.runs
    let same := rangesAll keys fun a => σ.mem[a]? == wmem[a]?
    ok := (← check s!"memory: reached.size = {σ.mem.size}, witness.size = {wmem.size}, pointwise on {keys.length} ranges"
      (same && σ.mem.size == wmem.size)) && ok
    -- registers
    let gprsOk := (List.range 31).all fun j => gprGet σ (j + 1) == some (w.regs (j + 1))
    ok := (← check "x1..x31 = witness regs" gprsOk) && ok
    let bs := bootState wmem w.regs
    -- GoodState-pinned CSRs of the reached state vs the witness (bootRegs = physicalAssignments)
    let eq64 (r : Register) (h : RegisterType r = BitVec 64) : Bool :=
      (h ▸ σ.regs.get? r : Option (BitVec 64)) == (h ▸ bs.regs.get? r : Option (BitVec 64))
    ok := (← check "cur_privilege" ((σ.regs.get? Register.cur_privilege : Option Privilege) == (bs.regs.get? Register.cur_privilege : Option Privilege))) && ok
    ok := (← check "misa" (eq64 Register.misa rfl)) && ok
    ok := (← check "mstatus" (eq64 Register.mstatus rfl)) && ok
    ok := (← check "mie" (eq64 Register.mie rfl)) && ok
    ok := (← check "mseccfg" (eq64 Register.mseccfg rfl)) && ok
    ok := (← check "satp" (eq64 Register.satp rfl)) && ok
    ok := (← check "mtvec" (eq64 Register.mtvec rfl)) && ok
    ok := (← check "mideleg" (eq64 Register.mideleg rfl)) && ok
    ok := (← check "medeleg" (eq64 Register.medeleg rfl)) && ok
    ok := (← check "menvcfg" (eq64 Register.menvcfg rfl)) && ok
    ok := (← check "mcyclecfg" (eq64 Register.mcyclecfg rfl)) && ok
    ok := (← check "minstretcfg" (eq64 Register.minstretcfg rfl)) && ok
    ok := (← check "mcountinhibit" ((σ.regs.get? Register.mcountinhibit : Option (BitVec 32)) == (bs.regs.get? Register.mcountinhibit : Option (BitVec 32)))) && ok
    ok := (← check "elp" ((σ.regs.get? Register.elp : Option (BitVec 1)) == (bs.regs.get? Register.elp : Option (BitVec 1)))) && ok
    ok := (← check "hart_state" ((σ.regs.get? Register.hart_state : Option HartState) == (bs.regs.get? Register.hart_state : Option HartState))) && ok
    ok := (← check "htif_done = false" ((σ.regs.get? Register.htif_done : Option Bool) == some false)) && ok
    ok := (← check "htif_tohost_base" ((σ.regs.get? Register.htif_tohost_base : Option (Option (BitVec 64))) == (bs.regs.get? Register.htif_tohost_base : Option (Option (BitVec 64))))) && ok
    ok := (← check "htif_payload_writes" ((σ.regs.get? Register.htif_payload_writes : Option (BitVec 4)) == (bs.regs.get? Register.htif_payload_writes : Option (BitVec 4)))) && ok
    ok := (← check "pmpcfg_n" ((σ.regs.get? Register.pmpcfg_n : Option (Vector Pmpcfg_ent 64)) == (bs.regs.get? Register.pmpcfg_n : Option (Vector Pmpcfg_ent 64)))) && ok
    ok := (← check "pmpaddr_n" ((σ.regs.get? Register.pmpaddr_n : Option (Vector (BitVec 64) 64)) == (bs.regs.get? Register.pmpaddr_n : Option (Vector (BitVec 64) 64)))) && ok
    ok := (← check "pma_regions" ((σ.regs.get? Register.pma_regions : Option (List PMA_Region)) == (bs.regs.get? Register.pma_regions : Option (List PMA_Region)))) && ok
    -- the counters the witness resets (informational)
    let show64 (r : Register) (h : RegisterType r = BitVec 64) : String :=
      s!"{(h ▸ σ.regs.get? r : Option (BitVec 64))}"
    IO.println s!"  [info] htif_tohost (not pinned by GoodState): reached {show64 Register.htif_tohost rfl}, witness `bootState` 0"
    IO.println s!"  reached counters (witness has setup values 0): mtime={show64 Register.mtime rfl} mcycle={show64 Register.mcycle rfl} minstret={show64 Register.minstret rfl} mip={show64 Register.mip rfl} mtimecmp={show64 Register.mtimecmp rfl} cycleCount={σ.cycleCount} (witness 0)"
    -- run both to halt
    let (r1, out1, ok1) ← runToHalt σ i u fuel
    IO.println s!"  reached state → halt: {r1} output = {repr out1}"
    let (r2, out2, ok2) ← runToHalt bs (w.entrySteps % 2) w.entrySteps fuel
    IO.println s!"  witness state → halt: {r2} output = {repr out2}"
    ok := (← check s!"both halt with the same (exit, output) as the emulator; expected output {repr w.expected}"
      (ok1 && ok2 && (r1.map (·.1)) == (r2.map (·.1)) && out1 == out2 && out1 == w.expected && r1.isSome)) && ok
    pure ok

def main (args : List String) : IO UInt32 := do
  let names := match args with | [] => ["proof"] | n :: _ => if n == "all" then witnesses.map Witness.name else [n]
  let fuel := match args with | [_, f] => f.toNat! | _ => 200000000
  let mut bad := 0
  for w in witnesses do
    if names.contains w.name then
      if !(← checkOne w fuel) then bad := bad + 1
  IO.println s!"replay: {bad} failing witness(es)"
  pure (if bad == 0 then 0 else 1)
