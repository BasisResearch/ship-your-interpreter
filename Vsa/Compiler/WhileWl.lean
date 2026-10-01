import Vsa.Compiler.Correct
import Vsa.Compiler.CompileSize
import Vsa.While.Validation

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable
open Vsa.Machine (Config Halts output)

private def i (n : Int) : Expr := .int n
private def v (x : String) : Expr := .var x
private def pl (args : List Expr) : Stmt := .expr (.call (v "println") args)
private def set (x : String) (e : Expr) : Stmt := .expr (.assign x e)

theorem whileWl_eq : Programs.whileWl = [
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
      .ifStmt (.binary .eq (.binary .mod (v "n") (i 2)) (i 0)) (.block [.cont]) none,
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
    pl [v "acc"]] := rfl

theorem whileWl_supported : Supported Programs.whileWl := by
  rw [whileWl_eq]
  simp [Supported, SupSeq, SupS, IntE, BoolE, CondE, NScope.declare, NScope.Mem, IsNative, InRange,
    ArithOp, CmpOp, SupArgs, maxArgs, i, v, set, pl]

theorem whileWl_fits : 0x80004800 + 4 * (compile Programs.whileWl).length ≤ 0x8001ad00 := by
  have := compile_length_le Programs.whileWl
  have hs : seqSize Programs.whileWl ≤ 2000 := by rw [whileWl_eq]; decide
  omega

theorem whileWl_compiled_halts (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (compileBytes Programs.whileWl).length →
      c.σ.mem[0x80004800 + k]? = (compileBytes Programs.whileWl)[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    Halts c "55\n2500\n36\n" 0 :=
  ((compile_correct _ whileWl_supported whileWl_fits c hgood htick hpc hpw hout hcode hlib).1 _).mp
    Validation.whileWl_valid

#print axioms whileWl_compiled_halts

end Vsa.Compiler
