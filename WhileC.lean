import Vsa.Compiler.Parse
import Vsa.Compiler.Check
import Vsa.Compiler.Image
import Vsa.ElfRun

/-!
# `whilec`: the verified WHILE compiler as a command-line tool

`whilec prog.wl -o prog.elf` parses `prog.wl` (the interpreter's grammar,
`Vsa/Compiler/Parse.lean`), checks the premises of `compileG_correct`
(`supportedGB`, `fitsB`), compiles with `compileG`, and writes an RV64 ELF
(`buildImage`) that runs bare-metal with HTIF console output, e.g. under
`spike prog.elf`. `--run` also executes the binary on the Sail RV64 model and
prints its console output and exit code.
-/

open Vsa Vsa.Compiler

structure Opts where
  input : Option String := none
  output : Option String := none
  run : Bool := false
  fuel : Nat := 200000000

def usage : String :=
  "usage: whilec <input.wl> [-o <output.elf>] [--run] [--fuel <steps>]"

def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | "-o" :: f :: r, o => parseArgs r { o with output := some f }
  | "--run" :: r, o => parseArgs r { o with run := true }
  | "--fuel" :: n :: r, o => match n.toNat? with
    | some k => parseArgs r { o with fuel := k }
    | none => .error s!"--fuel expects a number, got {n}"
  | a :: r, o =>
    if a.startsWith "-" then .error s!"unknown option {a}"
    else if o.input.isSome then .error "more than one input file"
    else parseArgs r { o with input := some a }

/-- Why a parsed program is outside the verified fragment, if it is. -/
def unsupported (p : Vsa.While.Program) : Option String :=
  if !wfSeqB (strTab p) [globalNames p] p then
    some "a scope, parameter list or function body is too large (at most 120 names/temporaries), \
      or an integer literal is out of range"
  else if !(strTab p).all latin1B then some "a string is not Latin-1"
  else if !decide (strOff (strTab p) (strTab p).length ≤ 0x100000) then some "the string table exceeds 1 MiB"
  else if !decide ((globalNames p).length ≤ 120) then some "more than 120 global names"
  else if !decide (tSeq p ≤ 120) then some "a top-level expression needs more than 120 temporaries"
  else if !fitsB p then some "the compiled code does not fit below tohost (0x8001ad00)"
  else none

def defaultOutput (input : String) : String :=
  (if input.endsWith ".wl" then input.dropRight 3 else input) ++ ".elf"

def main (args : List String) : IO UInt32 := do
  let o ← match parseArgs args {} with
    | .ok o => pure o
    | .error e => IO.eprintln s!"whilec: {e}\n{usage}"; return 2
  let some input := o.input | IO.eprintln usage; return 2
  let src ← IO.FS.readBinFile input
  let p ← match Parse.parseBytes src with
    | .ok p => pure p
    | .error e => IO.eprintln s!"{input}: {e}"; return 1
  if let some why := unsupported p then
    IO.eprintln s!"{input}: outside the verified fragment: {why}"
    return 1
  -- `unsupported p = none` is `supportedGB p ∧ fitsB p`, so `checked_correct` applies.
  let img ← match buildImage elfBytes p with
    | .ok img => pure img
    | .error e => IO.eprintln s!"whilec: {e}"; return 1
  let out := o.output.getD (defaultOutput input)
  IO.FS.writeBinFile out img
  IO.eprintln s!"whilec: wrote {out} ({(compileG p).length} instructions at 0x80004800)"
  if o.run then
    match mkRawELFFile? img with
    | .ok (.elf64 elf) =>
      match runElf elf o.fuel with
      | .ok r =>
        IO.print r.output
        match r.exitCode with
        | some e => IO.eprintln s!"whilec: exit code {e} after {r.steps} steps"; return e.toUInt32
        | none => IO.eprintln s!"whilec: still running after {r.steps} steps"; return 3
      | .error e => IO.eprintln s!"whilec: simulation error: {e}"; return 1
    | _ => IO.eprintln "whilec: cannot read back the written image"; return 1
  return 0
