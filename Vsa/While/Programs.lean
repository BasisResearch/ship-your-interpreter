import Vsa.While.Ast

/-!
# Deep-embedded WHILE programs

Hand translations of the `c/tests/*.wl` scripts into the deep embedding.
`whileWl` is the script linked into `while-riscv-htif.elf` — the program the
refinement theorem is about. The others are validation inputs: the binary's
output on each script is compared against the Lean semantics' output.
-/

namespace Vsa.While.Programs

open Expr Stmt

/-- Shorthand: integer literal. -/
private def i (n : Int) : Expr := .int n
/-- Shorthand: variable reference. -/
private def v (x : String) : Expr := .var x
/-- Shorthand: `println(...)` statement. -/
private def pl (args : List Expr) : Stmt := .expr (.call (v "println") args)
/-- Shorthand: assignment statement `x = e;`. -/
private def set (x : String) (e : Expr) : Stmt := .expr (.assign x e)

/-- `tests/while.wl` — the script embedded in the ELF. -/
def whileWl : Program := [
  -- var i = 0; var sum = 0;
  .varDecl "i" (some (i 0)),
  .varDecl "sum" (some (i 0)),
  -- while (i < 10) { i = i + 1; sum = sum + i; }
  .whileStmt (.binary .lt (v "i") (i 10)) (.block [
    set "i" (.binary .add (v "i") (i 1)),
    set "sum" (.binary .add (v "sum") (v "i"))]),
  pl [v "sum"],
  -- var n = 0; var total = 0;
  .varDecl "n" (some (i 0)),
  .varDecl "total" (some (i 0)),
  -- while (true) { n = n + 1; if (n > 100) { break; }
  --                if (n % 2 == 0) { continue; } total = total + n; }
  .whileStmt (.bool true) (.block [
    set "n" (.binary .add (v "n") (i 1)),
    .ifStmt (.binary .gt (v "n") (i 100)) (.block [.brk]) none,
    .ifStmt (.binary .eq (.binary .mod (v "n") (i 2)) (i 0))
      (.block [.cont]) none,
    set "total" (.binary .add (v "total") (v "n"))]),
  pl [v "total"],
  -- var acc = 0; var a = 1;
  .varDecl "acc" (some (i 0)),
  .varDecl "a" (some (i 1)),
  -- while (a <= 3) { var b = 1;
  --   while (b <= 3) { acc = acc + a * b; b = b + 1; } a = a + 1; }
  .whileStmt (.binary .le (v "a") (i 3)) (.block [
    .varDecl "b" (some (i 1)),
    .whileStmt (.binary .le (v "b") (i 3)) (.block [
      set "acc" (.binary .add (v "acc") (.binary .mul (v "a") (v "b"))),
      set "b" (.binary .add (v "b") (i 1))]),
    set "a" (.binary .add (v "a") (i 1))]),
  pl [v "acc"]]

/-- `tests/arithmetic.wl` -/
def arithmeticWl : Program := [
  pl [.binary .add (i 1) (.binary .mul (i 2) (i 3))],
  pl [.binary .mul (.binary .add (i 1) (i 2)) (i 3)],
  pl [.binary .div (i 10) (i 3)],
  pl [.binary .mod (i 10) (i 3)],
  pl [.binary .add (.unary .neg (i 5)) (i 3)],
  pl [.binary .add (.binary .mul (i 2) (i 3)) (.binary .mul (i 4) (i 5))],
  pl [.binary .mul (i 1000000) (i 1000000)],
  pl [.binary .sub (.binary .sub (i 7) (i 2)) (i 1)],
  pl [.unary .not (.bool true), .unary .not (i 0), .unary .not (i 1)],
  pl [.binary .lt (i 3) (i 5), .binary .le (i 5) (i 5),
      .binary .gt (i 7) (i 9), .binary .ge (i 2) (i 2)],
  pl [.binary .eq (i 1) (i 1), .binary .ne (i 1) (i 2),
      .binary .eq (.str "a") (.str "a"), .binary .eq (.str "a") (.str "b")],
  pl [.logical .and (.bool true) (.bool false),
      .logical .or (.bool true) (.bool false),
      .logical .and (i 1) (i 2), .logical .or (i 0) (i 0)]]

/-- `tests/for.wl` -/
def forWl : Program := [
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
  pl [v "line"]]

/-- `tests/functions.wl` -/
def functionsWl : Program := [
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
  pl [.call (.call (v "compose") [v "inc", v "dbl"]) [i 10]]]

/-- `tests/recursion.wl` -/
def recursionWl : Program := [
  .varDecl "fact" (some (.fn (some "fact") ["n"] [
    .ifStmt (.binary .le (v "n") (i 1)) (.block [.ret (some (i 1))]) none,
    .ret (some (.binary .mul (v "n") (.call (v "fact")
      [.binary .sub (v "n") (i 1)])))])),
  pl [.call (v "fact") [i 10]],
  .varDecl "fib" (some (.fn (some "fib") ["n"] [
    .ifStmt (.binary .lt (v "n") (i 2)) (.block [.ret (some (v "n"))]) none,
    .ret (some (.binary .add
      (.call (v "fib") [.binary .sub (v "n") (i 1)])
      (.call (v "fib") [.binary .sub (v "n") (i 2)])))])),
  pl [.call (v "fib") [i 20]],
  .varDecl "is_even" (some (.fn (some "is_even") ["n"] [
    .ifStmt (.binary .eq (v "n") (i 0)) (.block [.ret (some (.bool true))]) none,
    .ret (some (.call (v "is_odd") [.binary .sub (v "n") (i 1)]))])),
  .varDecl "is_odd" (some (.fn (some "is_odd") ["n"] [
    .ifStmt (.binary .eq (v "n") (i 0)) (.block [.ret (some (.bool false))]) none,
    .ret (some (.call (v "is_even") [.binary .sub (v "n") (i 1)]))])),
  pl [.call (v "is_even") [i 10], .call (v "is_odd") [i 10]],
  .varDecl "ack" (some (.fn (some "ack") ["m", "n"] [
    .ifStmt (.binary .eq (v "m") (i 0))
      (.block [.ret (some (.binary .add (v "n") (i 1)))]) none,
    .ifStmt (.binary .eq (v "n") (i 0))
      (.block [.ret (some (.call (v "ack") [.binary .sub (v "m") (i 1), i 1]))])
      none,
    .ret (some (.call (v "ack") [.binary .sub (v "m") (i 1),
      .call (v "ack") [v "m", .binary .sub (v "n") (i 1)]]))])),
  pl [.call (v "ack") [i 2, i 3]]]

/-- `tests/scope.wl` -/
def scopeWl : Program := [
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
  pl [.str "asserts ok"]]

/-- `tests/strings.wl` -/
def stringsWl : Program := [
  pl [.binary .add (.binary .add (.str "hello") (.str " ")) (.str "world")],
  pl [.binary .add (.str "value: ") (i 42)],
  pl [.binary .add (i 1) (.str "2")],
  .varDecl "s" (some (.str "abc")),
  pl [.binary .eq (v "s") (.str "abc"), .binary .ne (v "s") (.str "def")],
  pl [.binary .lt (.str "a") (.str "b"), .binary .le (.str "abc") (.str "abc")],
  pl [.str "line1\nline2"],
  pl [.str "tab\there"],
  pl [.str "quote: \"hi\""]]

/-- All validation programs with their source names. -/
def all : List (String × Program) := [
  ("while", whileWl),
  ("arithmetic", arithmeticWl),
  ("for", forWl),
  ("functions", functionsWl),
  ("recursion", recursionWl),
  ("scope", scopeWl),
  ("strings", stringsWl)]

end Vsa.While.Programs
