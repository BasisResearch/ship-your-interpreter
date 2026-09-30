import Vsa.Compiler.Gen
import Vsa.While.Semantics

namespace Vsa.Compiler

open Vsa.While

def mainPos₀ : Nat := printPos + printCode.length

abbrev Scope := List (List (String × Nat))

def Scope.resolve : Scope → String → Option Nat
  | [], _ => none
  | f :: g, x => match f.lookup x with
    | some i => some i
    | none => Scope.resolve g x

def cmpBranch : BinOp → Option (BrOp × Nat × Nat)
  | .lt => some (.lt, a0, a1)
  | .le => some (.ge, a1, a0)
  | .gt => some (.lt, a1, a0)
  | .ge => some (.ge, a0, a1)
  | .eq => some (.eq, a0, a1)
  | .ne => some (.ne, a0, a1)
  | _ => none

def cbin (pos : Nat) : BinOp → List Ins
  | .add => [.add a0 a0 a1]
  | .sub => [.sub a0 a0 a1]
  | .mul => libc pos mulPC
  | .div => [.br .ne a1 0 (bSkip 1), .jal 0 (jOff (pos + 1) errPos)] ++ libc (pos + 2) divPC
  | .mod => [.br .ne a1 0 (bSkip 1), .jal 0 (jOff (pos + 1) errPos)] ++ libc (pos + 2) modPC
  | op => match cmpBranch op with
    | some (b, r1, r2) => [.addi s3 0 1, .br b r1 r2 (bSkip 1), .addi s3 0 0, mv a0 s3]
    | none => []

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

structure Ctx where
  Γ : Scope
  next : Nat
  brk : Nat
  cont : Nat

def printLoop (k pos : Nat) : Nat → List Ins
  | 0 => []
  | n + 1 =>
    let ld := liN s2 (tempAddr k) ++ [.ld a0 s2]
    let call := Ins.jal ra (jOff (pos + ld.length) printPos)
    let sep := if n = 0 then [] else putc ' '
    ld ++ [call] ++ sep ++ printLoop (k + 1) (pos + ld.length + 1 + sep.length) n

mutual

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

def cargs (Γ : Scope) (k pos : Nat) : List Expr → List Ins × Nat
  | [] => ([], pos)
  | e :: es =>
    let ce := cexpr Γ k pos e
    let st := ce ++ liN s2 (tempAddr k) ++ [.sd a0 s2]
    let (cr, p) := cargs Γ (k + 1) (pos + st.length) es
    (st ++ cr, p)

end

def compile (p : Program) : List Ins :=
  let initΓ : Scope := [[]]
  let (body, _, _) := cseq ⟨initΓ, 0, 0, 0⟩ mainPos₀ p
  [.jal 0 (jOff 0 mainPos₀)] ++ errCode ++ printCode ++ body ++ exitCode 0

end Vsa.Compiler
