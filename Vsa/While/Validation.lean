import Vsa.While.Derive
import Vsa.While.Programs

/-!
# Validation of the big-step semantics against the binary

Each theorem states that the inductive big-step relation derives, for a
deep-embedded test program, exactly the output the interpreter binary
produced on the corresponding source script (`c/tests/*.expected`,
reproduced by running `c/while` on the scripts; `recursion_small` was run
on the binary directly). The derivations are constructed syntax-directedly
and checked by the kernel; the expected strings are the binary's output,
byte for byte.

The full `recursion.wl` (with `fib(20)` — tens of thousands of calls) is
validated on a smaller binary-generated example instead; its derivation
tree is prohibitively large to kernel-check, which is a practical limit,
not a semantic one.
-/

namespace Vsa.While.Validation

open Vsa.While Vsa.While.Programs

set_option maxRecDepth 4000000

/-- `tests/while.wl` (the ELF's embedded script). -/
theorem whileWl_valid : BigStep whileWl "55\n2500\n36\n" := by
  bigstep_derive

/-- `tests/arithmetic.wl` -/
theorem arithmetic_valid : BigStep arithmeticWl
    "7\n9\n3\n1\n-2\n26\n1000000000000\n4\nfalse true false\ntrue true false true\ntrue true true false\nfalse true true false\n" := by
  bigstep_derive

/-- `tests/for.wl` -/
theorem for_valid : BigStep forWl
    "1\n2\nFizz\n4\nBuzz\nFizz\n7\n8\nFizz\nBuzz\n11\nFizz\n13\n14\nFizzBuzz\n5050\n37\n3\n01234\n" := by
  bigstep_derive

/-- `tests/functions.wl` -/
theorem functions_valid : BigStep functionsWl
    "15\n11\n81\n3\n1\ntrue\n<fn make_adder>\n<fn>\n21\n" := by
  bigstep_derive

/-- `tests/scope.wl` -/
theorem scope_valid : BigStep scopeWl "2\n3\n1\n20\n14 5\n3\nasserts ok\n" := by
  bigstep_derive

/-- `tests/strings.wl` -/
theorem strings_valid : BigStep stringsWl
    "hello world\nvalue: 42\n12\ntrue true\ntrue true\nline1\nline2\ntab\there\nquote: \"hi\"\n" := by
  bigstep_derive

/-- Small-input recursion (fact, fib, mutual recursion), output obtained by
running the binary on the script. -/
def recursionSmall : Program := [
  .varDecl "fact" (some (.fn (some "fact") ["n"] [
    .ifStmt (.binary .le (.var "n") (.int 1)) (.block [.ret (some (.int 1))]) none,
    .ret (some (.binary .mul (.var "n") (.call (.var "fact")
      [.binary .sub (.var "n") (.int 1)])))])),
  .expr (.call (.var "println") [.call (.var "fact") [.int 5]]),
  .varDecl "fib" (some (.fn (some "fib") ["n"] [
    .ifStmt (.binary .lt (.var "n") (.int 2)) (.block [.ret (some (.var "n"))]) none,
    .ret (some (.binary .add
      (.call (.var "fib") [.binary .sub (.var "n") (.int 1)])
      (.call (.var "fib") [.binary .sub (.var "n") (.int 2)])))])),
  .expr (.call (.var "println") [.call (.var "fib") [.int 8]]),
  .varDecl "is_even" (some (.fn (some "is_even") ["n"] [
    .ifStmt (.binary .eq (.var "n") (.int 0)) (.block [.ret (some (.bool true))]) none,
    .ret (some (.call (.var "is_odd") [.binary .sub (.var "n") (.int 1)]))])),
  .varDecl "is_odd" (some (.fn (some "is_odd") ["n"] [
    .ifStmt (.binary .eq (.var "n") (.int 0)) (.block [.ret (some (.bool false))]) none,
    .ret (some (.call (.var "is_even") [.binary .sub (.var "n") (.int 1)]))])),
  .expr (.call (.var "println")
    [.call (.var "is_even") [.int 6], .call (.var "is_odd") [.int 6]])]

theorem recursion_small_valid : BigStep recursionSmall "120\n21\ntrue false\n" := by
  bigstep_derive

end Vsa.While.Validation
