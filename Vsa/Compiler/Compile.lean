import Vsa.Compiler.Machine
import Vsa.While.Semantics

/-!
# The WHILE → RV64 compiler

Every variable declaration site gets a static memory slot (programs in the
supported subset have no closures, so each scope has at most one live instance).
Name resolution follows the semantics' frame chain: a scope is the list of names
declared so far in one frame, innermost first. Expression temporaries live in
static slots indexed by nesting depth.

Register use: `a0` (x10) result, `a1` (x11) second operand, `s2` (x18)
addresses, `s3` (x19) scratch, `x12`/`x13` zeroed before each libgcc call.
The print subroutine additionally uses `s4`–`s6` (x20–x22) and saves `ra` in
`s11` (x27).

Code layout (instruction indices from `codeBase`): `0` jumps to the program;
`errPos` is the runtime-error exit (`exit(70)`); `printPos` is the integer print
subroutine; the program starts at `mainPos` and ends with `exit(0)`.
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

def mainPos : Nat := printPos + printCode.length

/-! ## Scopes -/

/-- Names declared so far in each frame, innermost first, with their slots. -/
abbrev Scope := List (List (String × Nat))

def Scope.resolve : Scope → String → Option Nat
  | [], _ => none
  | f :: g, x => match f.lookup x with
    | some i => some i
    | none => Scope.resolve g x

/-! ## Expressions -/

/-- Comparison as a branch that fires when the result is true, on operands `a0`
(left) and `a1` (right). -/
def cmpBranch : BinOp → Option (BrOp × Nat × Nat)
  | .lt => some (.lt, a0, a1)
  | .le => some (.ge, a1, a0)
  | .gt => some (.lt, a1, a0)
  | .ge => some (.ge, a0, a1)
  | .eq => some (.eq, a0, a1)
  | .ne => some (.ne, a0, a1)
  | _ => none

/-- `a0 := a0 op a1` for an operator, emitted at instruction `pos`. -/
def cbin (pos : Nat) : BinOp → List Ins
  | .add => [.add a0 a0 a1]
  | .sub => [.sub a0 a0 a1]
  | .mul => libc pos mulPC
  | .div => [.br .ne a1 0 (bSkip 1), .jal 0 (jOff (pos + 1) errPos)] ++ libc (pos + 2) divPC
  | .mod => [.br .ne a1 0 (bSkip 1), .jal 0 (jOff (pos + 1) errPos)] ++ libc (pos + 2) modPC
  | op => match cmpBranch op with
    | some (b, r1, r2) => [.addi s3 0 1, .br b r1 r2 (bSkip 1), .addi s3 0 0, mv a0 s3]
    | none => []

/-- Evaluate `e` into `a0`; `k` is the temporary depth, `pos` the position of
the first emitted instruction. -/
def cexpr (Γ : Scope) (k pos : Nat) : Expr → List Ins
  | .int n => li a0 (BitVec.ofInt 64 n)
  | .bool b => [.addi a0 0 (if b then 1 else 0)]
  | .var x => liN s2 (varAddr ((Γ.resolve x).getD 0)) ++ [.ld a0 s2]
  | .assign x e =>
    let c := cexpr Γ k pos e
    c ++ liN s2 (varAddr ((Γ.resolve x).getD 0)) ++ [.sd a0 s2]
  | .binary op l r =>
    let cl := cexpr Γ k pos l
    let st := liN s2 (tempAddr k) ++ [.sd a0 s2]
    let p1 := pos + cl.length + st.length
    let cr := cexpr Γ (k + 1) p1 r
    let ld := [mv a1 a0] ++ liN s2 (tempAddr k) ++ [.ld a0 s2]
    cl ++ st ++ cr ++ ld ++ cbin (p1 + cr.length + ld.length) op
  | .unary .neg e => cexpr Γ k pos e ++ [.sub a0 0 a0]
  | .unary .not e =>
    cexpr Γ k pos e ++ [.addi s3 0 1, .br .eq a0 0 (bSkip 1), .addi s3 0 0, mv a0 s3]
  | _ => []

/-! ## Statements -/

/-- Compilation context: the scope, the next fresh slot, and the break and
continue targets of the innermost loop. -/
structure Ctx where
  Γ : Scope
  next : Nat
  brk : Nat
  cont : Nat

/-- Printing code for arguments `k … k+n-1` placed at `pos`. -/
def printLoop (k pos : Nat) : Nat → List Ins
  | 0 => []
  | n + 1 =>
    let ld := liN s2 (tempAddr k) ++ [.ld a0 s2]
    let call := Ins.jal ra (jOff (pos + ld.length) printPos)
    let sep := if n = 0 then [] else putc ' '
    ld ++ [call] ++ sep ++ printLoop (k + 1) (pos + ld.length + 1 + sep.length) n


mutual

/-- Compile a statement at `pos`. Returns the code and the next fresh slot. -/
def cstmt (C : Ctx) (pos : Nat) : Stmt → List Ins × Nat
  | .expr (.call (.var f) args) =>
    let (ev, p) := cargs C.Γ 0 pos args
    let pr := printLoop 0 p args.length
    (ev ++ pr ++ (if f = "println" then putc '\n' else []), C.next)
  | .expr e => (cexpr C.Γ 0 pos e, C.next)
  | .block ss =>
    let (c, _, n) := cseq { C with Γ := [] :: C.Γ } pos ss
    (c, n)
  | .ifStmt c t e =>
    let cc := cexpr C.Γ 0 pos c
    let (ct, n1) := cstmt C (pos + cc.length + 2) t
    match e with
    | none =>
      let endPos := pos + cc.length + 2 + ct.length
      (cc ++ [.br .ne a0 0 (bSkip 1), .jal 0 (jOff (pos + cc.length + 1) endPos)] ++ ct, n1)
    | some e =>
      let elsePos := pos + cc.length + 2 + ct.length + 1
      let (ce, n2) := cstmt { C with next := n1 } elsePos e
      let endPos := elsePos + ce.length
      (cc ++ [.br .ne a0 0 (bSkip 1), .jal 0 (jOff (pos + cc.length + 1) elsePos)] ++ ct ++
        [.jal 0 (jOff (elsePos - 1) endPos)] ++ ce, n2)
  | .whileStmt c b =>
    let cc := cexpr C.Γ 0 pos c
    let bpos := pos + cc.length + 2
    let blen := (cstmt { C with brk := 0, cont := 0 } bpos b).1.length
    let endPos := bpos + blen + 1
    let (cb, n) := cstmt { C with brk := endPos, cont := pos } bpos b
    (cc ++ [.br .ne a0 0 (bSkip 1), .jal 0 (jOff (pos + cc.length + 1) endPos)] ++ cb ++
      [.jal 0 (jOff (bpos + cb.length) pos)], n)
  | .brk => ([.jal 0 (jOff pos C.brk)], C.next)
  | .cont => ([.jal 0 (jOff pos C.cont)], C.next)
  | _ => ([], C.next)

/-- Compile a statement list; declarations extend the innermost scope. -/
def cseq (C : Ctx) (pos : Nat) : List Stmt → List Ins × Scope × Nat
  | [] => ([], C.Γ, C.next)
  | .varDecl x (some e) :: ss =>
    let ce := cexpr C.Γ 0 pos e
    let (Γ', slot, n) := match C.Γ with
      | f :: g => match f.lookup x with
        | some i => (C.Γ, i, C.next)
        | none => (((x, C.next) :: f) :: g, C.next, C.next + 1)
      | [] => ([[(x, C.next)]], C.next, C.next + 1)
    let st := ce ++ liN s2 (varAddr slot) ++ [.sd a0 s2]
    let (cr, Γ'', n') := cseq { C with Γ := Γ', next := n } (pos + st.length) ss
    (st ++ cr, Γ'', n')
  | s :: ss =>
    let (c, n) := cstmt C pos s
    let (cr, Γ', n') := cseq { C with next := n } (pos + c.length) ss
    (c ++ cr, Γ', n')

/-- Evaluate call arguments into temporaries `k, k+1, …`. Returns the code and
the position after it. -/
def cargs (Γ : Scope) (k pos : Nat) : List Expr → List Ins × Nat
  | [] => ([], pos)
  | e :: es =>
    let ce := cexpr Γ k pos e
    let st := ce ++ liN s2 (tempAddr k) ++ [.sd a0 s2]
    let (cr, p) := cargs Γ (k + 1) (pos + st.length) es
    (st ++ cr, p)

end

/-- The whole program. -/
def compile (p : Program) : List Ins :=
  let initΓ : Scope := [[]]
  let (body, _, _) := cseq ⟨initΓ, 0, 0, 0⟩ mainPos p
  [.jal 0 (jOff 0 mainPos)] ++ errCode ++ printCode ++ body ++ exitCode 0

end Vsa.Compiler
