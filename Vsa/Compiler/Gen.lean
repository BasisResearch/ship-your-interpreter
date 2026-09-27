import Vsa.Compiler.Machine
import Vsa.While.Semantics

/-!
# Code-generation helpers

Registers, constants (`li`), console output (`putc`), the exit sequence, libgcc
calls, and the fixed code image prefix: the error exit at `errPos` and the
integer print subroutine at `printPos`. The subroutine uses `s2`–`s6`
(x18–x22), saves `ra` in `s11` (x27), and buffers digits at `bufBase`.
-/

namespace Vsa.Compiler

open Vsa.While

/-! ## Registers and memory layout -/

def a0 : Nat := 10
def a1 : Nat := 11
def s2 : Nat := 18
def s3 : Nat := 19
def s4 : Nat := 20
def s5 : Nat := 21
def s6 : Nat := 22
def s11 : Nat := 27
def ra : Nat := 1

def tohostW : BitVec 64 := BitVec.ofNat 64 Vsa.Sim.tohostAddr
def tempBase : Nat := 0x80100000
def varBase : Nat := 0x80200000
def bufBase : Nat := 0x80080000

def tempAddr (k : Nat) : Nat := tempBase + 8 * k
def varAddr (i : Nat) : Nat := varBase + 8 * i

/-! ## Constants -/

/-- The 11-bit chunk `j` (from the top) of a 64-bit word: `n = Σ chunk j * 2^(11(5-j))`. -/
def chunk (n : BitVec 64) (j : Nat) : BitVec 12 :=
  BitVec.ofNat 12 (n.toNat / 2 ^ (11 * (5 - j)) % 2048)

/-- Load a 64-bit constant: `addi` for 12-bit signed values, otherwise six
11-bit chunks joined by `slli 11`/`ori`. -/
def li (rd : Nat) (n : BitVec 64) : List Ins :=
  if n.toInt < 2048 ∧ -2048 ≤ n.toInt then [.addi rd 0 (BitVec.ofInt 12 n.toInt)]
  else
    [.addi rd 0 (chunk n 0)] ++
    ((List.range 5).flatMap fun j => [.slli rd rd 11#6, .ori rd rd (chunk n (j + 1))])

def liN (rd : Nat) (n : Nat) : List Ins := li rd (BitVec.ofNat 64 n)

/-- `mv rd, rs`. -/
def mv (rd rs : Nat) : Ins := .addi rd rs 0

/-- Byte offset of a jump from instruction `from` to instruction `to`. -/
def jOff (src dst : Nat) : BitVec 21 := BitVec.ofInt 21 (4 * ((dst : Int) - src))

/-- Byte offset of a branch skipping `n` instructions forward (`n = 1`: to the
instruction after next). -/
def bSkip (n : Nat) : BitVec 13 := BitVec.ofNat 13 (4 * (n + 1))

/-- `putchar c`: store the console command word to `tohost`. -/
def putc (c : Char) : List Ins :=
  li s3 (putcWord (BitVec.ofNat 8 c.toNat)) ++ li s2 tohostW ++ [.sd s3 s2]

/-- `exit(e)`. -/
def exitCode (e : Nat) : List Ins :=
  li s3 (exitWord (BitVec.ofNat 64 e)) ++ li s2 tohostW ++ [.sd s3 s2]

/-- Call a libgcc routine on `a0`, `a1` from instruction `pos`. -/
def libc (pos tgt : Nat) : List Ins :=
  [.addi 12 0 0, .addi 13 0 0,
   .jal ra (BitVec.ofInt 21 ((tgt : Int) - (codeBase + 4 * (pos + 2))))]

/-! ## Fixed code: entry jump, error exit, print subroutine -/

def errPos : Nat := 1
def errCode : List Ins := exitCode 70
def printPos : Nat := errPos + errCode.length

/-- `print_int(a0)`: prints the decimal rendering of the signed integer in `a0`
and returns to `ra`. Digits come from signed `%`/`/` by 10 (`|n % 10|` is the last
digit of `|n|` for every `n`, including `INT64_MIN`), are buffered, and printed in
reverse. -/
def printCode : List Ins :=
  let minus := putc '-'
  let p0 := printPos
  -- prologue
  let pro : List Ins := [mv s11 ra, mv s4 a0, .br .ge s4 0 (bSkip minus.length)]
  let setup : List Ins := liN s6 bufBase ++ [.addi s5 0 0]
  let loopPos := p0 + pro.length + minus.length + setup.length
  let d1 : List Ins := [mv a0 s4, .addi a1 0 10] ++ libc (loopPos + 2) modPC
  let d2 : List Ins := [.br .ge a0 0 (bSkip 1), .sub a0 0 a0, .addi a0 a0 48, .sd a0 s6,
    .addi s6 s6 8, .addi s5 s5 1, mv a0 s4, .addi a1 0 10]
  let d3pos := loopPos + d1.length + d2.length
  let d3 : List Ins := libc d3pos divPC ++ [mv s4 a0]
  let bodyLen := d1.length + d2.length + d3.length
  let back : Ins := .br .ne s4 0 (BitVec.ofInt 13 (-4 * (bodyLen : Int)))
  let outPos := loopPos + bodyLen + 1
  let o1 : List Ins := [.addi s6 s6 (-8), .ld a0 s6] ++ li s3 (putcWord 0) ++ [.add s3 s3 a0] ++
    li s2 tohostW ++ [.sd s3 s2, .addi s5 s5 (-1)]
  let oback : Ins := .br .ne s5 0 (BitVec.ofInt 13 (-4 * (o1.length : Int)))
  let _ := outPos
  pro ++ minus ++ setup ++ d1 ++ d2 ++ d3 ++ [back] ++ o1 ++ [oback, mv ra s11, .jalr ra]

end Vsa.Compiler
