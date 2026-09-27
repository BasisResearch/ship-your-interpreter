import Vsa.While.Ast

namespace Vsa.While.Programs

open Expr Stmt

private def i (n : Int) : Expr := .int n

private def v (x : String) : Expr := .var x

private def pl (args : List Expr) : Stmt := .expr (.call (v "println") args)

private def set (x : String) (e : Expr) : Stmt := .expr (.assign x e)

def whileWl : Program := [

  .varDecl "i" (some (i 0)),
  .varDecl "sum" (some (i 0)),

  .whileStmt (.binary .lt (v "i") (i 10)) (.block [
    set "i" (.binary .add (v "i") (i 1)),
    set "sum" (.binary .add (v "sum") (v "i"))]),
  pl [v "sum"],

  .varDecl "n" (some (i 0)),
  .varDecl "total" (some (i 0)),

  .whileStmt (.bool true) (.block [
    set "n" (.binary .add (v "n") (i 1)),
    .ifStmt (.binary .gt (v "n") (i 100)) (.block [.brk]) none,
    .ifStmt (.binary .eq (.binary .mod (v "n") (i 2)) (i 0))
      (.block [.cont]) none,
    set "total" (.binary .add (v "total") (v "n"))]),
  pl [v "total"],

  .varDecl "acc" (some (i 0)),
  .varDecl "a" (some (i 1)),

  .whileStmt (.binary .le (v "a") (i 3)) (.block [
    .varDecl "b" (some (i 1)),
    .whileStmt (.binary .le (v "b") (i 3)) (.block [
      set "acc" (.binary .add (v "acc") (.binary .mul (v "a") (v "b"))),
      set "b" (.binary .add (v "b") (i 1))]),
    set "a" (.binary .add (v "a") (i 1))]),
  pl [v "acc"]]

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

def forWl : Program := [

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

end Vsa.While.Programs
