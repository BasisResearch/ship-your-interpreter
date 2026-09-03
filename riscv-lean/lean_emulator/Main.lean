import LeanRiscv

/-- Parse a trace-PC file: one hex address per line (`0x` prefix optional;
blank lines and `#` comments ignored). -/
def readTracePCs (p : System.FilePath) : IO (Std.HashSet (BitVec 64)) := do
  let txt ← IO.FS.readFile p
  let mut s : Std.HashSet (BitVec 64) := {}
  for line in txt.splitOn "\n" do
    let l := (line.splitOn "#").headD "" |>.trimAscii.toString
    if l.isEmpty then continue
    let h := if l.startsWith "0x" then (l.drop 2).toString else l
    let mut n : Nat := 0
    for c in h.toList do
      let d := if c.isDigit then c.toNat - 48
               else if 'a' ≤ c && c ≤ 'f' then c.toNat - 87
               else if 'A' ≤ c && c ≤ 'F' then c.toNat - 55
               else 99
      if d ≥ 16 then throw (IO.userError s!"bad trace-pc line: {line}")
      n := n * 16 + d
    s := s.insert (BitVec.ofNat 64 n)
  pure s

def usage : String :=
  "usage: lean_riscv_emulator <elf_file>\n" ++
  "       lean_riscv_emulator <elf_file> --trace-all [--max-steps N]\n" ++
  "       lean_riscv_emulator <elf_file> --trace-pcs <file> [--max-steps N]\n" ++
  "\n" ++
  "  Trace rows go to stderr, one per traced step (see LeanRiscv.traceLoop)."

structure Opts where
  elf : String := ""
  traceAll : Bool := false
  tracePCs : Option String := none
  maxSteps : Nat := 200000000

partial def parseArgs (as : List String) (o : Opts) : Except String Opts :=
  match as with
  | [] => .ok o
  | "--trace-all" :: rest => parseArgs rest { o with traceAll := true }
  | "--trace-pcs" :: f :: rest => parseArgs rest { o with tracePCs := some f }
  | "--max-steps" :: n :: rest =>
    match n.toNat? with
    | some k => parseArgs rest { o with maxSteps := k }
    | none => .error s!"bad --max-steps: {n}"
  | a :: rest =>
    if a.startsWith "--" then .error s!"unknown flag: {a}"
    else if o.elf.isEmpty then parseArgs rest { o with elf := a }
    else .error "more than one ELF given"

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e => do IO.eprintln e; IO.println usage; pure 255
  | .ok o =>
    if o.elf.isEmpty then do IO.println usage; pure 255 else
    let pcs ← match o.tracePCs with
      | some f => readTracePCs f
      | none => pure {}
    let tracing := o.traceAll || o.tracePCs.isSome
    match (← readElf o.elf) with
    | Except.error err => do
      IO.println "Failed to parse ELF file:"
      IO.println err
      pure 255
    | Except.ok (.elf64 elf) =>
      if tracing then traceElf64 elf o.traceAll pcs o.maxSteps
      else runElf64 elf
    | Except.ok (.elf32 _elf) => do
      IO.println "32 bit ELF file not supported"
      pure 255
