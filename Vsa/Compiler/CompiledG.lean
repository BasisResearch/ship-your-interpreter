import Vsa.Compiler.CorrectG
import Vsa.While.Validation
import Vsa.While.CostEval

/-!
# Test programs, compiled by the full compiler

`functionsWl` (closures, captured state, returns), `forWl` (`for` loops with
`continue`), `scopeWl` (blocks, shadowing, `assert`) and `stringsWl` (string
concatenation, comparison and printing) are supported,
fit below `tohost` and stay within the heap budget, so every machine
configuration holding their compiled code prints their validated output and
exits with `0` (`*_compiledG_halts`, from `compileG_correct`).
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable
open Vsa.Machine (Config Halts output)

private def i (n : Int) : Expr := .int n
private def v (x : String) : Expr := .var x
private def pl (args : List Expr) : Stmt := .expr (.call (v "println") args)
private def set (x : String) (e : Expr) : Stmt := .expr (.assign x e)

/-- A program with a bounded evaluator cost stays within the heap budget. -/
theorem budget_of_normalCost {p : Program} {f n0 : Nat}
    (h : (execSeqEval f initSt 0 0 p).normalCost? = some n0) (hn : n0 ≤ heapUnits) :
    ∀ out, BigStep p out → BigStepBudget p out heapUnits := by
  rintro out ⟨st', D, hout⟩
  obtain ⟨n, C⟩ := ExecSeqCost.exists D
  exact ⟨st', n, C, hout, by rw [execSeqCost_eq_of_normalCost h C]; exact hn⟩

/-- A supported, fitting program within budget: every machine configuration
holding its compiled code halts with its big-step output. -/
theorem compiledG_halts {p : Program} {out : String} (hsup : SupportedG p)
    (hfit : 0x80004800 + 4 * (compileG p).length ≤ 0x8001ad00)
    (hcap : ∀ out, BigStep p out → BigStepBudget p out heapUnits) (hb : BigStep p out) (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (compileGBytes p).length →
      c.σ.mem[0x80004800 + k]? = (compileGBytes p)[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    Halts c out 0 :=
  ((compileG_correct p hsup hfit hcap c hgood htick hpc hpw hout hcode hlib).1 out).mp hb

theorem functionsWl_eq : Programs.functionsWl = [
    -- fn make_adder(n) { return fn (x) { return x + n; }; }
    .varDecl "make_adder" (some (.fn (some "make_adder") ["n"] [
      .ret (some (.fn none ["x"] [.ret (some (.binary .add (v "x") (v "n")))]))])),
    .varDecl "add5" (some (.call (v "make_adder") [i 5])),
    pl [.call (v "add5") [i 10]],
    -- fn apply_twice(f, x) { return f(f(x)); }
    .varDecl "apply_twice" (some (.fn (some "apply_twice") ["f", "x"] [
      .ret (some (.call (v "f") [.call (v "f") [v "x"]]))])),
    pl [.call (v "apply_twice") [v "add5", i 1]],
    pl [.call (v "apply_twice")
      [.fn none ["x"] [.ret (some (.binary .mul (v "x") (v "x")))], i 3]],
    -- fn make_counter() { var count = 0; return fn () { ... }; }
    .varDecl "make_counter" (some (.fn (some "make_counter") [] [
      .varDecl "count" (some (i 0)),
      .ret (some (.fn none [] [
        set "count" (.binary .add (v "count") (i 1)),
        .ret (some (v "count"))]))])),
    .varDecl "c" (some (.call (v "make_counter") [])),
    .expr (.call (v "c") []),
    .expr (.call (v "c") []),
    pl [.call (v "c") []],
    .varDecl "c2" (some (.call (v "make_counter") [])),
    pl [.call (v "c2") []],
    .varDecl "f" (some (v "add5")),
    pl [.binary .eq (v "f") (v "add5")],
    pl [v "make_adder"],
    pl [.fn none ["x"] [.ret (some (v "x"))]],
    -- fn compose(f, g) { return fn (x) { return f(g(x)); }; }
    .varDecl "compose" (some (.fn (some "compose") ["f", "g"] [
      .ret (some (.fn none ["x"] [
        .ret (some (.call (v "f") [.call (v "g") [v "x"]]))]))])),
    .varDecl "inc" (some (.fn none ["x"] [.ret (some (.binary .add (v "x") (i 1)))])),
    .varDecl "dbl" (some (.fn none ["x"] [.ret (some (.binary .mul (v "x") (i 2)))])),
    pl [.call (.call (v "compose") [v "inc", v "dbl"]) [i 10]]] := rfl

theorem functionsWl_supportedG : SupportedG Programs.functionsWl := by
  refine ⟨?_, ⟨by unfold Latin1; decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩
  rw [functionsWl_eq]
  simp only [WfSeq, WfS, WfE, WfArgs, WfOE, WfOS, Latin1, i, v, pl, set, and_true, true_and]
  repeat' apply And.intro
  all_goals decide +kernel

theorem functionsWl_fitsG : 0x80004800 + 4 * (compileG Programs.functionsWl).length ≤ 0x8001ad00 := by decide +kernel

/-- **The compiled `functionsWl` prints its validated output and exits 0** on every
machine configuration that holds its code (and libgcc's routines) at the entry. -/
theorem functionsWl_compiledG_halts (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (compileGBytes Programs.functionsWl).length →
      c.σ.mem[0x80004800 + k]? = (compileGBytes Programs.functionsWl)[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    Halts c "15\n11\n81\n3\n1\ntrue\n<fn make_adder>\n<fn>\n21\n" 0 :=
  compiledG_halts functionsWl_supportedG functionsWl_fitsG
    (budget_of_normalCost (f := 1000) (n0 := 5296) (by decide +kernel) (by decide)) Validation.functions_valid c hgood htick hpc hpw
    hout hcode hlib

theorem forWl_eq : Programs.forWl = [
    -- fizzbuzz
    .forStmt (some (.varDecl "i" (some (i 1))))
      (some (.binary .le (v "i") (i 15)))
      (some (.assign "i" (.binary .add (v "i") (i 1))))
      (.block [
        .ifStmt (.binary .eq (.binary .mod (v "i") (i 15)) (i 0))
          (.block [pl [.str "FizzBuzz"]])
          (some (.ifStmt (.binary .eq (.binary .mod (v "i") (i 3)) (i 0))
            (.block [pl [.str "Fizz"]])
            (some (.ifStmt (.binary .eq (.binary .mod (v "i") (i 5)) (i 0))
              (.block [pl [.str "Buzz"]])
              (some (.block [pl [v "i"]]))))))]),
    .varDecl "sum" (some (i 0)),
    .forStmt (some (.varDecl "i" (some (i 1))))
      (some (.binary .le (v "i") (i 100)))
      (some (.assign "i" (.binary .add (v "i") (i 1))))
      (.block [set "sum" (.binary .add (v "sum") (v "i"))]),
    pl [v "sum"],
    .varDecl "s" (some (i 0)),
    .forStmt (some (.varDecl "i" (some (i 1))))
      (some (.binary .le (v "i") (i 10)))
      (some (.assign "i" (.binary .add (v "i") (i 1))))
      (.block [
        .ifStmt (.binary .eq (.binary .mod (v "i") (i 3)) (i 0))
          (.block [.cont]) none,
        set "s" (.binary .add (v "s") (v "i"))]),
    pl [v "s"],
    .varDecl "j" (some (i 0)),
    .forStmt none (some (.binary .lt (v "j") (i 3))) none
      (.block [set "j" (.binary .add (v "j") (i 1))]),
    pl [v "j"],
    .varDecl "line" (some (.str "")),
    .forStmt (some (.varDecl "i" (some (i 0))))
      (some (.binary .lt (v "i") (i 5)))
      (some (.assign "i" (.binary .add (v "i") (i 1))))
      (.block [set "line" (.binary .add (v "line") (v "i"))]),
    pl [v "line"]] := rfl

theorem forWl_supportedG : SupportedG Programs.forWl := by
  refine ⟨?_, ⟨by unfold Latin1; decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩
  rw [forWl_eq]
  simp only [WfSeq, WfS, WfE, WfArgs, WfOE, WfOS, Latin1, i, v, pl, set, and_true, true_and]
  repeat' apply And.intro
  all_goals decide +kernel

theorem forWl_fitsG : 0x80004800 + 4 * (compileG Programs.forWl).length ≤ 0x8001ad00 := by decide +kernel

/-- **The compiled `forWl` prints its validated output and exits 0** on every
machine configuration that holds its code (and libgcc's routines) at the entry. -/
theorem forWl_compiledG_halts (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (compileGBytes Programs.forWl).length →
      c.σ.mem[0x80004800 + k]? = (compileGBytes Programs.forWl)[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    Halts c "1\n2\nFizz\n4\nBuzz\nFizz\n7\n8\nFizz\nBuzz\n11\nFizz\n13\n14\nFizzBuzz\n5050\n37\n3\n01234\n" 0 :=
  compiledG_halts forWl_supportedG forWl_fitsG
    (budget_of_normalCost (f := 1000) (n0 := 6384) (by decide +kernel) (by decide)) Validation.for_valid c hgood htick hpc hpw
    hout hcode hlib

theorem scopeWl_eq : Programs.scopeWl = [
    .varDecl "x" (some (i 1)),
    .block [
      .varDecl "x" (some (i 2)),
      pl [v "x"],
      set "x" (i 3),
      pl [v "x"]],
    pl [v "x"],
    .varDecl "y" (some (i 10)),
    .block [set "y" (i 20)],
    pl [v "y"],
    .varDecl "g" (some (i 5)),
    .varDecl "shadow" (some (.fn (some "shadow") ["g"] [
      .ret (some (.binary .mul (v "g") (i 2)))])),
    pl [.call (v "shadow") [i 7], v "g"],
    .varDecl "count" (some (i 0)),
    .whileStmt (.binary .lt (v "count") (i 3)) (.block [
      .varDecl "local" (some (.binary .mul (v "count") (i 10))),
      set "count" (.binary .add (v "count") (i 1))]),
    pl [v "count"],
    .expr (.call (v "assert") [.binary .eq (.binary .add (i 1) (i 1)) (i 2),
      .str "math is broken"]),
    pl [.str "asserts ok"]] := rfl

theorem scopeWl_supportedG : SupportedG Programs.scopeWl := by
  refine ⟨?_, ⟨by unfold Latin1; decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩
  rw [scopeWl_eq]
  simp only [WfSeq, WfS, WfE, WfArgs, WfOE, WfOS, Latin1, i, v, pl, set, and_true, true_and]
  repeat' apply And.intro
  all_goals decide +kernel

theorem scopeWl_fitsG : 0x80004800 + 4 * (compileG Programs.scopeWl).length ≤ 0x8001ad00 := by decide +kernel

/-- **The compiled `scopeWl` prints its validated output and exits 0** on every
machine configuration that holds its code (and libgcc's routines) at the entry. -/
theorem scopeWl_compiledG_halts (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (compileGBytes Programs.scopeWl).length →
      c.σ.mem[0x80004800 + k]? = (compileGBytes Programs.scopeWl)[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    Halts c "2\n3\n1\n20\n14 5\n3\nasserts ok\n" 0 :=
  compiledG_halts scopeWl_supportedG scopeWl_fitsG
    (budget_of_normalCost (f := 1000) (n0 := 1648) (by decide +kernel) (by decide)) Validation.scope_valid c hgood htick hpc hpw
    hout hcode hlib

theorem stringsWl_eq : Programs.stringsWl = [
    pl [.binary .add (.binary .add (.str "hello") (.str " ")) (.str "world")],
    pl [.binary .add (.str "value: ") (i 42)],
    pl [.binary .add (i 1) (.str "2")],
    .varDecl "s" (some (.str "abc")),
    pl [.binary .eq (v "s") (.str "abc"), .binary .ne (v "s") (.str "def")],
    pl [.binary .lt (.str "a") (.str "b"), .binary .le (.str "abc") (.str "abc")],
    pl [.str "line1\nline2"],
    pl [.str "tab\there"],
    pl [.str "quote: \"hi\""]] := rfl

theorem stringsWl_supportedG : SupportedG Programs.stringsWl := by
  refine ⟨?_, ⟨by unfold Latin1; decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩⟩
  rw [stringsWl_eq]
  simp only [WfSeq, WfS, WfE, WfArgs, WfOE, WfOS, Latin1, i, v, pl, set, and_true, true_and]
  repeat' apply And.intro
  all_goals decide +kernel

theorem stringsWl_fitsG : 0x80004800 + 4 * (compileG Programs.stringsWl).length ≤ 0x8001ad00 := by decide +kernel

/-- **The compiled `stringsWl` prints its validated output and exits 0** on every
machine configuration that holds its code (and libgcc's routines) at the entry. -/
theorem stringsWl_compiledG_halts (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (compileGBytes Programs.stringsWl).length →
      c.σ.mem[0x80004800 + k]? = (compileGBytes Programs.stringsWl)[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    Halts c "hello world\nvalue: 42\n12\ntrue true\ntrue true\nline1\nline2\ntab\there\nquote: \"hi\"\n" 0 :=
  compiledG_halts stringsWl_supportedG stringsWl_fitsG
    (budget_of_normalCost (f := 1000) (n0 := 208) (by decide +kernel) (by decide)) Validation.strings_valid c hgood
    htick hpc hpw hout hcode hlib

#print axioms functionsWl_compiledG_halts
#print axioms forWl_compiledG_halts
#print axioms scopeWl_compiledG_halts
#print axioms stringsWl_compiledG_halts

end Vsa.Compiler
