import Vsa.Compiler.Compile
import Vsa.ElfRun
import Vsa.While.Programs

/-! Native harness: run compiled WHILE programs on the executable Sail model
(the interpreter ELF supplies libgcc and the reset state; the compiled code is
written at `codeBase` and the PC set there). Run: `lake env lean experiments/compiler/RunCompiled.lean`. -/
open Vsa Vsa.Compiler Vsa.While LeanRV64DExecutable Sail ConcurrencyInterfaceV1 PreSail

def codeBytes (code : List Ins) : List (BitVec 8) :=
  code.flatMap fun i => [byte i.encode 0, byte i.encode 1, byte i.encode 2, byte i.encode 3]

def runCompiled (p : Program) (fuel : Nat) : Except String RunResult := do
  let elf ← whileElf?
  let code := compile p
  let bytes := codeBytes code
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


def pl (es : List Expr) : Stmt := .expr (.call (.var "println") es)
def t1 : Program := [pl [.int 0, .int (-7), .int 1234567890123, .int (-9223372036854775808), .int 9223372036854775807],
  .varDecl "x" (some (.int 5)), .ifStmt (.binary .ge (.var "x") (.int 5)) (pl [.binary .div (.int (-17)) (.int 5), .binary .mod (.int (-17)) (.int 5)]) (some (pl [.int 1])),
  .expr (.call (.var "print") [.int 3, .int 4]), pl [.unary .neg (.var "x")],
  .expr (.assign "x" (.binary .mul (.var "x") (.int 3))), pl [.var "x"]]
def t2 : Program := [pl [.int 1], pl [.binary .div (.int 1) (.int 0)], pl [.int 2]]
#eval runCompiled t1 2000000
#eval runCompiled t2 2000000
#eval (Vsa.While.intToString (-17 / 5), (-17 : Int).tdiv 5, (-17:Int).tmod 5)
#eval runCompiled Programs.whileWl 2000000
