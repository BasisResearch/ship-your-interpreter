import Vsa.Elf
import Vsa.ElfRun

/-- Run the embedded ELF natively and report its observable behavior.
Sanity harness for `Vsa.runWhileElf` — the same pure function used in
theorem statements. -/
def main (args : List String) : IO UInt32 := do
  let fuel := match args with
    | [n] => n.toNat!
    | _ => 100_000_000
  match Vsa.runWhileElf fuel with
  | .error e => do
    IO.eprintln s!"error: {e}"
    pure 1
  | .ok r => do
    IO.println s!"exit code: {r.exitCode}"
    IO.println s!"steps:     {r.steps}"
    IO.println "--- console output ---"
    IO.print r.output
    pure 0
