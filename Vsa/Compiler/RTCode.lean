import Vsa.Compiler.WP

/-!
# The runtime of compiled WHILE programs

Values are pairs of words `(tag, payload)`: `null` is `(0, 0)`, a boolean is
`(1, 0/1)`, an integer `(2, n)`, a string `(3, pointer)`, a closure
`(4, pointer)`, a native `(5, id)`. A frame slot holding tag `6` is unbound.

A string object is its length followed by one word per character. A closure
object holds the captured frame, the code address of its body, and its print
and concatenation renderings as string objects. A frame holds its parent and
two words per slot.

Memory: frames are bump-allocated in `[frameBase, frameEnd)` (pointer in
`s7`), string and closure objects in `[objBase, objEnd)` (pointer in `s0`),
the stack grows down from `stackHi` (`sp`), `s1` holds the current frame and
`s8` the call depth. Runtime routines preserve these five registers and
return to `ra`; a routine called from compiled code saves `ra` in `s10`, one
called from such a routine in `s11`, and `itos` in `s9`.
-/

namespace Vsa.Compiler

open Vsa.Sim

/-! ## Registers -/

def spR : Nat := 2
def t0 : Nat := 5
def t1 : Nat := 6
def t2 : Nat := 7
def hpO : Nat := 8
def envR : Nat := 9
def a2 : Nat := 12
def a3 : Nat := 13
def a4 : Nat := 14
def a5 : Nat := 15
def a6 : Nat := 16
def a7 : Nat := 17
def hpF : Nat := 23
def depR : Nat := 24
def s9 : Nat := 25
def s10 : Nat := 26
def t3 : Nat := 28
def t4 : Nat := 29
def t5 : Nat := 30
def t6 : Nat := 31

/-! ## Memory layout -/

def frameBase : Nat := 0x80100000
def frameEnd : Nat := 0x90000000
def objBase : Nat := 0x90000000
def objEnd : Nat := 0xE0000000
def stackLo : Nat := 0xE0000000
def stackHi : Nat := 0x100000000
/-- Where `display` renders an integer before printing it. -/
def scratchStr : Nat := 0x80090000

/-- Value tags. -/
def tagNull : Nat := 0
def tagBool : Nat := 1
def tagInt : Nat := 2
def tagStr : Nat := 3
def tagClo : Nat := 4
def tagNat : Nat := 5
def tagUndef : Nat := 6

/-- The fixed strings at the start of the object heap. -/
def fixedStrs : List String :=
  ["null", "true", "false", "<native fn print>", "<native fn println>", "<native fn assert>",
   "<native fn>", "<fn>"]

/-- Size of a string object. -/
def strSize (s : String) : Nat := 8 + 8 * s.length

/-- Offset of string `i` of a table from the table start. -/
def strOff : List String → Nat → Nat
  | [], _ => 0
  | _, 0 => 0
  | s :: ss, i + 1 => strSize s + strOff ss i

/-- Address of fixed string `i`. -/
def fixedAddr (i : Nat) : Nat := objBase + strOff fixedStrs i

/-! ## Code helpers -/

def Br (op : BrOp) (r1 r2 src dst : Nat) : Ins := .br op r1 r2 (bOff src dst)
def J (src dst : Nat) : Ins := .jal 0 (jOff src dst)
def Call (src dst : Nat) : Ins := .jal 1 (jOff src dst)
def mvi (rd : Nat) (n : Int) : Ins := .addi rd 0 (BitVec.ofInt 12 n)
def addi (rd rs : Nat) (n : Int) : Ins := .addi rd rs (BitVec.ofInt 12 n)
/-- `addi` with a computed non-negative immediate. -/
def addiN (rd rs n : Nat) : Ins := .addi rd rs (BitVec.ofNat 12 n)
def ret : Ins := .jalr ra

/-- Print the byte in `r`. -/
def putcR (r : Nat) : List Ins :=
  li s3 (putcWord 0) ++ [.add s3 s3 r] ++ li s2 tohostW ++ [.sd s3 s2]

/-! ## The routines

Each routine is a function of its first instruction index `b`. -/

/-- `printstr`: print the string object at `a1`. -/
def psCode (b : Nat) : List Ins :=
  [.ld t0 a1, addi t1 a1 8,
   Br .eq t0 0 (b + 2) (b + 31),
   .ld t2 t1] ++ putcR t2 ++
  [addi t1 t1 8, addi t0 t0 (-1), J (b + 30) (b + 2),
   ret]

/-- `itos`: write the string object of the integer in `a1` at `a2`; `a3` is its end. -/
def itCode (b : Nat) : List Ins :=
  [mv s9 ra, mv a6 a1, mv a7 a2, mv s4 a1] ++ liN s6 bufBase ++ [mvi s5 0] ++
  -- digit loop at b + 16
  [mv a0 s4, mvi a1 10] ++ libc (b + 18) modPC ++
  [Br .ge a0 0 (b + 21) (b + 23), .sub a0 0 a0,
   addi a0 a0 48, .sd a0 s6, addi s6 s6 8, addi s5 s5 1,
   mv a0 s4, mvi a1 10] ++ libc (b + 29) divPC ++
  [mv s4 a0, Br .ne s4 0 (b + 33) (b + 16),
   -- header
   addi t1 a7 8, mv t0 s5,
   Br .ge a6 0 (b + 36) (b + 41),
   addi t0 t0 1, mvi t2 45, .sd t2 t1, addi t1 t1 8,
   .sd t0 a7,
   -- copy loop at b + 42
   Br .eq s5 0 (b + 42) (b + 49),
   addi s6 s6 (-8), .ld t2 s6, .sd t2 t1, addi t1 t1 8, addi s5 s5 (-1),
   J (b + 48) (b + 42),
   mv a3 t1, mv ra s9, ret]

/-- `copy`: copy `a7` words from `a6` to `a5`, advancing both pointers. -/
def cpCode (b : Nat) : List Ins :=
  [Br .eq a7 0 (b + 0) (b + 7),
   .ld t0 a6, .sd t0 a5, addi a6 a6 8, addi a5 a5 8, addi a7 a7 (-1),
   J (b + 6) (b + 0),
   ret]

/-- `strcmp`: compare the strings at `a1` and `a3`; `a0` is `-1`, `0` or `1`. -/
def scCode (b : Nat) : List Ins :=
  [.ld t0 a1, .ld t1 a3, addi t2 a1 8, addi t3 a3 8,
   -- loop at b + 4
   Br .eq t0 0 (b + 4) (b + 15),
   Br .eq t1 0 (b + 5) (b + 18),
   .ld t4 t2, .ld t5 t3,
   Br .lt t4 t5 (b + 8) (b + 16),
   Br .lt t5 t4 (b + 9) (b + 18),
   addi t2 t2 8, addi t3 t3 8, addi t0 t0 (-1), addi t1 t1 (-1),
   J (b + 14) (b + 4),
   -- b + 15: left exhausted
   Br .eq t1 0 (b + 15) (b + 20),
   mvi a0 (-1), ret,
   mvi a0 1, ret,
   mvi a0 0, ret]

/-- `truthy`: `a0 := 1` if the value `(a0, a1)` is truthy, else `0`. -/
def trCode (b : Nat) : List Ins :=
  [Br .eq a0 0 (b + 0) (b + 8),
   mvi t0 3, Br .lt a0 t0 (b + 2) (b + 5),
   mvi a0 1, ret,
   Br .eq a1 0 (b + 5) (b + 8),
   mvi a0 1, ret,
   mvi a0 0, ret]

/-- `newframe`: allocate a frame with `a5` unbound slots and parent `a6`; `a4` is the frame. -/
def nfCode (b : Nat) : List Ins :=
  [.slli t0 a5 4, addi t0 t0 8, .add t0 hpF t0] ++ liN t1 frameEnd ++
  [Br .lt t1 t0 (b + 14) errPos,
   mv a4 hpF, .sd a6 a4, addi t2 a4 8, mvi t3 6, mv t4 a5,
   -- loop at b + 20
   Br .eq t4 0 (b + 20) (b + 25),
   .sd t3 t2, addi t2 t2 16, addi t4 t4 (-1),
   J (b + 24) (b + 20),
   mv hpF t0, ret]

/-! ## Positions -/

def psPos : Nat := 14
def itPos : Nat := psPos + 32
def cpPos : Nat := itPos + 52
def scPos : Nat := cpPos + 8
def trPos : Nat := scPos + 22
def nfPos : Nat := trPos + 10
def dpPos : Nat := nfPos + 27
def csPos : Nat := dpPos + 126
def ccPos : Nat := csPos + 83
def addPos : Nat := ccPos + 32
def subPos : Nat := addPos + 23
def mulPos : Nat := subPos + 5
def divPos : Nat := mulPos + 13
def modPos : Nat := divPos + 14
def cmpPos : Nat := modPos + 14
def eqPos : Nat := cmpPos + 35
def rtEnd : Nat := eqPos + 13

/-- `display`: print the value `(a0, a1)` as `Value.display` renders it. -/
def dpCode (b : Nat) : List Ins :=
  [mv s10 ra,
   mvi t0 2, Br .eq a0 t0 (b + 2) (b + 24),
   mvi t0 3, Br .eq a0 t0 (b + 4) (b + 49),
   mvi t0 4, Br .eq a0 t0 (b + 6) (b + 51),
   mvi t0 1, Br .eq a0 t0 (b + 8) (b + 55),
   mvi t0 5, Br .eq a0 t0 (b + 10) (b + 82)] ++
  liN a1 (fixedAddr 0) ++ [Call (b + 22) psPos, J (b + 23) (b + 124)] ++
  -- b + 24: integer
  liN a2 scratchStr ++ [Call (b + 35) itPos] ++ liN a1 scratchStr ++
  [Call (b + 47) psPos, J (b + 48) (b + 124),
   -- b + 49: string
   Call (b + 49) psPos, J (b + 50) (b + 124),
   -- b + 51: closure
   addi a1 a1 16, .ld a1 a1, Call (b + 53) psPos, J (b + 54) (b + 124),
   -- b + 55: boolean
   Br .eq a1 0 (b + 55) (b + 69)] ++
  liN a1 (fixedAddr 1) ++ [Call (b + 67) psPos, J (b + 68) (b + 124)] ++
  liN a1 (fixedAddr 2) ++ [Call (b + 80) psPos, J (b + 81) (b + 124),
   -- b + 82: native
   Br .eq a1 0 (b + 82) (b + 98), mvi t0 1, Br .eq a1 t0 (b + 84) (b + 111)] ++
  liN a1 (fixedAddr 5) ++ [Call (b + 96) psPos, J (b + 97) (b + 124)] ++
  liN a1 (fixedAddr 3) ++ [Call (b + 109) psPos, J (b + 110) (b + 124)] ++
  liN a1 (fixedAddr 4) ++ [Call (b + 122) psPos, J (b + 123) (b + 124),
   -- b + 124
   mv ra s10, ret]

/-- `catstr`: `a1 :=` the string object of `Value.catDisplay` of `(a0, a1)`,
allocating an integer's rendering on the object heap. -/
def csCode (b : Nat) : List Ins :=
  [mv s11 ra,
   mvi t0 3, Br .eq a0 t0 (b + 2) (b + 81),
   mvi t0 2, Br .eq a0 t0 (b + 4) (b + 23),
   mvi t0 4, Br .eq a0 t0 (b + 6) (b + 41),
   mvi t0 1, Br .eq a0 t0 (b + 8) (b + 44),
   mvi t0 5, Br .eq a0 t0 (b + 10) (b + 69)] ++
  liN a1 (fixedAddr 0) ++ [J (b + 22) (b + 81),
   -- b + 23: integer
   addi t1 hpO 168] ++ liN t2 objEnd ++
  [Br .lt t2 t1 (b + 35) errPos,
   mv a2 hpO, Call (b + 37) itPos, mv a1 hpO, mv hpO a3, J (b + 40) (b + 81),
   -- b + 41: closure
   addi a1 a1 24, .ld a1 a1, J (b + 43) (b + 81),
   -- b + 44: boolean
   Br .eq a1 0 (b + 44) (b + 57)] ++
  liN a1 (fixedAddr 1) ++ [J (b + 56) (b + 81)] ++
  liN a1 (fixedAddr 2) ++ [J (b + 68) (b + 81)] ++
  -- b + 69: native
  liN a1 (fixedAddr 6) ++ [J (b + 80) (b + 81),
   -- b + 81
   mv ra s11, ret]

/-- `concat`: `a1 :=` a fresh string object holding the string at `a1` followed
by the string at `a3`. -/
def ccCode (b : Nat) : List Ins :=
  [mv s11 ra, .ld t3 a1, .ld t4 a3, .add t5 t3 t4,
   .slli t6 t5 3, addi t6 t6 8, .add t6 hpO t6] ++ liN t2 objEnd ++
  [Br .lt t2 t6 (b + 18) errPos,
   mv a4 hpO, .sd t5 a4, addi a5 a4 8,
   addi a6 a1 8, mv a7 t3, Call (b + 24) cpPos,
   addi a6 a3 8, mv a7 t4, Call (b + 27) cpPos,
   mv hpO a5, mv a1 a4, mv ra s11, ret]

/-- `+` on values `(a0, a1)` and `(a2, a3)`. -/
def addCode (b : Nat) : List Ins :=
  [mv s10 ra,
   mvi t0 3, Br .eq a0 t0 (b + 2) (b + 9), Br .eq a2 t0 (b + 3) (b + 9),
   mvi t0 2, Br .ne a0 t0 (b + 5) errPos, Br .ne a2 t0 (b + 6) errPos,
   .add a1 a1 a3, J (b + 8) (b + 21),
   -- b + 9: concatenation
   mv t5 a2, mv t6 a3, Call (b + 11) csPos, mv s2 a1,
   mv a0 t5, mv a1 t6, Call (b + 15) csPos, mv a3 a1, mv a1 s2,
   Call (b + 18) ccPos, mvi a0 3, J (b + 20) (b + 21),
   -- b + 21
   mv ra s10, ret]

/-- `-` on integers. -/
def subCode (b : Nat) : List Ins :=
  [mvi t0 2, Br .ne a0 t0 (b + 1) errPos, Br .ne a2 t0 (b + 2) errPos,
   .sub a1 a1 a3, ret]

/-- `*` on integers (libgcc `__muldi3`). -/
def mulCode (b : Nat) : List Ins :=
  [mvi t0 2, Br .ne a0 t0 (b + 1) errPos, Br .ne a2 t0 (b + 2) errPos,
   mv s10 ra, mv a0 a1, mv a1 a3] ++ libc (b + 6) mulPC ++
  [mv a1 a0, mvi a0 2, mv ra s10, ret]

/-- `/` on integers (libgcc `__divdi3`). -/
def divCode (b : Nat) : List Ins :=
  [mvi t0 2, Br .ne a0 t0 (b + 1) errPos, Br .ne a2 t0 (b + 2) errPos,
   Br .eq a3 0 (b + 3) errPos,
   mv s10 ra, mv a0 a1, mv a1 a3] ++ libc (b + 7) divPC ++
  [mv a1 a0, mvi a0 2, mv ra s10, ret]

/-- `%` on integers (libgcc `__moddi3`). -/
def modCode (b : Nat) : List Ins :=
  [mvi t0 2, Br .ne a0 t0 (b + 1) errPos, Br .ne a2 t0 (b + 2) errPos,
   Br .eq a3 0 (b + 3) errPos,
   mv s10 ra, mv a0 a1, mv a1 a3] ++ libc (b + 7) modPC ++
  [mv a1 a0, mvi a0 2, mv ra s10, ret]

/-- Ordering comparisons on two integers or two strings; `a4` selects
`<` (0), `<=` (1), `>` (2), `>=` (3). -/
def cmpCode (b : Nat) : List Ins :=
  [mv s10 ra,
   mvi t0 2, Br .ne a0 t0 (b + 2) (b + 12), Br .ne a2 t0 (b + 3) errPos,
   Br .lt a1 a3 (b + 4) (b + 8), Br .lt a3 a1 (b + 5) (b + 10),
   mvi a0 0, J (b + 7) (b + 16),
   mvi a0 (-1), J (b + 9) (b + 16),
   mvi a0 1, J (b + 11) (b + 16),
   -- b + 12: strings
   mvi t0 3, Br .ne a0 t0 (b + 13) errPos, Br .ne a2 t0 (b + 14) errPos,
   Call (b + 15) scPos,
   -- b + 16: select on the sign in a0
   mvi a1 0,
   mvi t1 0, Br .eq a4 t1 (b + 18) (b + 24),
   mvi t1 1, Br .eq a4 t1 (b + 20) (b + 26),
   mvi t1 2, Br .eq a4 t1 (b + 22) (b + 28),
   J (b + 23) (b + 30),
   Br .ge a0 0 (b + 24) (b + 32), J (b + 25) (b + 31),
   Br .lt 0 a0 (b + 26) (b + 32), J (b + 27) (b + 31),
   Br .ge 0 a0 (b + 28) (b + 32), J (b + 29) (b + 31),
   Br .lt a0 0 (b + 30) (b + 32),
   mvi a1 1,
   mvi a0 1, mv ra s10, ret]

/-- `==` on values: `(a0, a1) := (1, 1)` if equal, else `(1, 0)`. -/
def eqCode (b : Nat) : List Ins :=
  [mv s10 ra,
   Br .ne a0 a2 (b + 1) (b + 9),
   mvi t0 3, Br .eq a0 t0 (b + 3) (b + 7),
   Br .ne a1 a3 (b + 4) (b + 9),
   mvi a1 1, J (b + 6) (b + 10),
   Call (b + 7) scPos, Br .eq a0 0 (b + 8) (b + 5),
   mvi a1 0,
   mvi a0 1, mv ra s10, ret]

/-- The runtime, from `psPos` to `rtEnd`. -/
def rtCode : List Ins :=
  psCode psPos ++ itCode itPos ++ cpCode cpPos ++ scCode scPos ++ trCode trPos ++
  nfCode nfPos ++ dpCode dpPos ++ csCode csPos ++ ccCode ccPos ++ addCode addPos ++
  subCode subPos ++ mulCode mulPos ++ divCode divPos ++ modCode modPos ++ cmpCode cmpPos ++
  eqCode eqPos

end Vsa.Compiler
