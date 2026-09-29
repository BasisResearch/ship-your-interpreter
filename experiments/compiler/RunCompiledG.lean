import Vsa.Compiler.CorrectG
import Vsa.ElfRun
import Vsa.While.Programs

/-! Native harness for the full compiler: run `compileG` output on the
executable Sail model (the interpreter ELF supplies libgcc and the reset state;
the compiled code is written at `codeBase` and the PC set there).
Run: `lake env lean experiments/compiler/RunCompiledG.lean`. -/
open Vsa Vsa.Compiler Vsa.While LeanRV64DExecutable Sail ConcurrencyInterfaceV1 PreSail

def runG (p : Program) (fuel : Nat) : Except String RunResult := do
  let elf ← whileElf?
  let bytes := compileGBytes p
  let prog : SailM (Option Nat × Nat) := do
    setupElf elf
    modify fun s =>
      let m' := (List.range bytes.length).foldl (fun m k => m.insert (codeBase + k) (bytes.getD k 0)) s.mem
      { s with mem := m' }
    LeanRV64DExecutable.writeReg Register.PC (BitVec.ofNat 64 codeBase)
    runSteps fuel 0 0
  match prog.run (initState elf) with
  | .ok (exit?, steps) s => .ok ⟨exit?, String.join s.sailOutput.toList, steps⟩
  | .error e _ => .error e.print

#eval runG Programs.whileWl 2000000
#eval runG Programs.functionsWl 2000000
#eval runG Programs.forWl 2000000
#eval runG Programs.scopeWl 2000000
#eval runG Programs.stringsWl 2000000
-- a runtime error (division by zero) exits with 70
#eval runG [.expr (.call (.var "println") [.binary .div (.int 1) (.int 0)])] 2000000
