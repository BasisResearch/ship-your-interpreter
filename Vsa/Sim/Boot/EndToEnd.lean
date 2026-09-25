import VsaIris.Interp.EndToEnd
import Vsa.While.Validation
import Vsa.Sim.Boot.Gen.Proof
import Vsa.Sim.Boot.Gen.While
import Vsa.Sim.Boot.Gen.Arithmetic
import Vsa.Sim.Boot.Gen.For
import Vsa.Sim.Boot.Gen.Scope
import Vsa.Sim.Boot.Gen.Strings

/-!
# The final theorem at the binary's real entry states

`endToEnd_refinement` applied to the loader-derived witnesses: the machine
state the emulator reaches at `interp_run`'s entry (ELF loader memory plus the
traced store log, `Gen/<Prog>.lean`) halts with exactly the output the source
semantics derives (`Vsa/While/Validation.lean`), from `IrisHoles` alone. The
witnesses are stated at the state's zero fill (`fillZero`, REVIEW.md P3),
which is what `endToEnd_refinement` takes; the conclusion is about the real,
sparse state.
-/

namespace Vsa.Sim.Boot

open Vsa.Machine Vsa.While Vsa.While.Validation

/-- The proof ELF (`c/while-riscv-htif.elf`, embedded `while.wl`), run from its
real `interp_run` entry state, prints `55 2500 36` and exits 0. -/
theorem proofElf_halts (h : VsaIris.Interp.IrisHoles) :
    Halts (bootConfig (bootMem Gen.Proof.script Gen.Proof.log) Gen.Proof.regs
      Gen.Proof.entrySteps) "55\n2500\n36\n" 0 := by
  have hl := Gen.Proof.prog_eq ▸ Gen.Proof.loaded
  exact ((Vsa.Sim.EndToEnd.endToEnd_refinement h _ _ hl).1 _).mp whileWl_valid

theorem while_halts (h : VsaIris.Interp.IrisHoles) :
    Halts (bootConfig (bootMem Gen.While.script Gen.While.log) Gen.While.regs
      Gen.While.entrySteps) "55\n2500\n36\n" 0 := by
  have hl := Gen.While.prog_eq ▸ Gen.While.loaded
  exact ((Vsa.Sim.EndToEnd.endToEnd_refinement h _ _ hl).1 _).mp whileWl_valid

theorem arithmetic_halts (h : VsaIris.Interp.IrisHoles) :
    Halts (bootConfig (bootMem Gen.Arithmetic.script Gen.Arithmetic.log) Gen.Arithmetic.regs
      Gen.Arithmetic.entrySteps)
      "7\n9\n3\n1\n-2\n26\n1000000000000\n4\nfalse true false\ntrue true false true\ntrue true true false\nfalse true true false\n"
      0 := by
  have hl := Gen.Arithmetic.prog_eq ▸ Gen.Arithmetic.loaded
  exact ((Vsa.Sim.EndToEnd.endToEnd_refinement h _ _ hl).1 _).mp arithmetic_valid

theorem for_halts (h : VsaIris.Interp.IrisHoles) :
    Halts (bootConfig (bootMem Gen.For.script Gen.For.log) Gen.For.regs Gen.For.entrySteps)
      "1\n2\nFizz\n4\nBuzz\nFizz\n7\n8\nFizz\nBuzz\n11\nFizz\n13\n14\nFizzBuzz\n5050\n37\n3\n01234\n"
      0 := by
  have hl := Gen.For.prog_eq ▸ Gen.For.loaded
  exact ((Vsa.Sim.EndToEnd.endToEnd_refinement h _ _ hl).1 _).mp for_valid

theorem scope_halts (h : VsaIris.Interp.IrisHoles) :
    Halts (bootConfig (bootMem Gen.Scope.script Gen.Scope.log) Gen.Scope.regs
      Gen.Scope.entrySteps) "2\n3\n1\n20\n14 5\n3\nasserts ok\n" 0 := by
  have hl := Gen.Scope.prog_eq ▸ Gen.Scope.loaded
  exact ((Vsa.Sim.EndToEnd.endToEnd_refinement h _ _ hl).1 _).mp scope_valid

theorem strings_halts (h : VsaIris.Interp.IrisHoles) :
    Halts (bootConfig (bootMem Gen.Strings.script Gen.Strings.log) Gen.Strings.regs
      Gen.Strings.entrySteps)
      "hello world\nvalue: 42\n12\ntrue true\ntrue true\nline1\nline2\ntab\there\nquote: \"hi\"\n"
      0 := by
  have hl := Gen.Strings.prog_eq ▸ Gen.Strings.loaded
  exact ((Vsa.Sim.EndToEnd.endToEnd_refinement h _ _ hl).1 _).mp strings_valid

#print axioms proofElf_halts
#print axioms strings_halts

end Vsa.Sim.Boot
