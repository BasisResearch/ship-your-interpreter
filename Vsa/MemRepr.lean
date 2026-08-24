import Vsa.Machine
import Vsa.While.Ast

/-!
# Inductive representation of WHILE programs in RISC-V memory

`ExprRepr`/`StmtRepr` characterize, as inductive relations, when an address
in the machine's memory holds the C struct representation (`c/src/ast.h`,
LP64 ABI, little-endian) of a deep-embedded WHILE expression/statement:

```c
struct Expr { ExprKind kind; int line; union {...} as; };   // kind@0 line@4 union@8
struct Stmt { StmtKind kind; int line; union {...} as; };
```

Pointers are 8 bytes little-endian; `int` 4 bytes; `long long` 8 bytes
two's-complement. Operator fields store `TokType` codes (`c/src/lexer.h`).
A program is represented by a NULL-free array of `Stmt*` (as produced by
`parse_program`). These relations are the interface between "a WHILE
program" (syntax) and "the machine about to interpret it" (a memory
image) in the ∀-program refinement statement.
-/

namespace Vsa.MemRepr

open Vsa.While

/-- Machine memory: byte-addressed, as in the Sail model. -/
abbrev Mem := Std.ExtHashMap Nat (BitVec 8)

/-- Little-endian read of `n` bytes as a natural number. -/
def readLE (m : Mem) (a : Nat) : Nat → Option Nat
  | 0 => some 0
  | k + 1 => do
    let b ← m[a]?
    let rest ← readLE m (a + 1) k
    pure (b.toNat + 256 * rest)

/-- 4-byte little-endian read (C `int`, enum tags). -/
def read32 (m : Mem) (a : Nat) : Option Nat := readLE m a 4

/-- 8-byte little-endian read (pointers, `long long`). -/
def read64 (m : Mem) (a : Nat) : Option Nat := readLE m a 8

/-- C `long long` read: 64-bit two's complement. -/
def readI64 (m : Mem) (a : Nat) : Option Int :=
  (read64 m a).map fun n => (BitVec.ofNat 64 n).toInt

/-- A NUL-terminated ASCII string at address `a` (C `char *`). -/
inductive CStr (m : Mem) : Nat → List Char → Prop where
  | nil {a : Nat} : m[a]? = some 0 → CStr m a []
  | cons {a : Nat} {b : BitVec 8} {cs : List Char} :
    m[a]? = some b → b ≠ 0 → b.toNat < 128 →
    CStr m (a + 1) cs →
    CStr m a (Char.ofNat b.toNat :: cs)

/-- String-valued wrapper for `CStr`. -/
def CString (m : Mem) (a : Nat) (s : String) : Prop :=
  ∃ cs, CStr m a cs ∧ s = String.ofList cs

/-- `TokType` codes stored in binary-operator AST nodes (`lexer.h`). -/
def binOpTok : BinOp → Nat
  | .add => 11 | .sub => 12 | .mul => 13 | .div => 14 | .mod => 15
  | .ne => 17 | .eq => 19 | .lt => 20 | .le => 21 | .gt => 22 | .ge => 23

def logOpTok : LogOp → Nat
  | .and => 24 | .or => 25

def unOpTok : UnOp → Nat
  | .neg => 12 | .not => 16

mutual

/-- `Expr` struct at address `a` represents the deep-embedded expression.
Constructor per `ExprKind` (`EX_INT = 0 … EX_FN = 10`). -/
inductive ExprRepr (m : Mem) : Nat → Expr → Prop where
  | int {a : Nat} {n : Int} :
    read32 m a = some 0 → readI64 m (a + 8) = some n →
    ExprRepr m a (.int n)
  | str {a p : Nat} {s : String} :
    read32 m a = some 1 → read64 m (a + 8) = some p → CString m p s →
    ExprRepr m a (.str s)
  | boolTrue {a : Nat} {b : Nat} :
    read32 m a = some 2 → read32 m (a + 8) = some b → b ≠ 0 →
    ExprRepr m a (.bool true)
  | boolFalse {a : Nat} :
    read32 m a = some 2 → read32 m (a + 8) = some 0 →
    ExprRepr m a (.bool false)
  | null {a : Nat} :
    read32 m a = some 3 →
    ExprRepr m a .null
  | var {a p : Nat} {x : String} :
    read32 m a = some 4 → read64 m (a + 8) = some p → CString m p x →
    ExprRepr m a (.var x)
  | assign {a p q : Nat} {x : String} {e : Expr} :
    read32 m a = some 5 →
    read64 m (a + 8) = some p → CString m p x →
    read64 m (a + 16) = some q → ExprRepr m q e →
    ExprRepr m a (.assign x e)
  | binary {a l r : Nat} {op : BinOp} {el er : Expr} :
    read32 m a = some 6 →
    read32 m (a + 8) = some (binOpTok op) →
    read64 m (a + 16) = some l → ExprRepr m l el →
    read64 m (a + 24) = some r → ExprRepr m r er →
    ExprRepr m a (.binary op el er)
  | logical {a l r : Nat} {op : LogOp} {el er : Expr} :
    read32 m a = some 7 →
    read32 m (a + 8) = some (logOpTok op) →
    read64 m (a + 16) = some l → ExprRepr m l el →
    read64 m (a + 24) = some r → ExprRepr m r er →
    ExprRepr m a (.logical op el er)
  | unary {a p : Nat} {op : UnOp} {e : Expr} :
    read32 m a = some 8 →
    read32 m (a + 8) = some (unOpTok op) →
    read64 m (a + 16) = some p → ExprRepr m p e →
    ExprRepr m a (.unary op e)
  | call {a f args argc : Nat} {ef : Expr} {es : List Expr} :
    read32 m a = some 9 →
    read64 m (a + 8) = some f → ExprRepr m f ef →
    read64 m (a + 16) = some args →
    read32 m (a + 24) = some argc →
    ExprArrayRepr m args argc es →
    ExprRepr m a (.call ef es)
  | fnNamed {a p params paramc body : Nat} {x : String} {ps : List String}
      {ss : List Stmt} :
    read32 m a = some 10 →
    read64 m (a + 8) = some p → p ≠ 0 → CString m p x →
    read64 m (a + 16) = some params →
    read32 m (a + 24) = some paramc →
    ParamsRepr m params paramc ps →
    read64 m (a + 32) = some body → StmtRepr m body (.block ss) →
    ExprRepr m a (.fn (some x) ps ss)
  | fnAnon {a params paramc body : Nat} {ps : List String} {ss : List Stmt} :
    read32 m a = some 10 →
    read64 m (a + 8) = some 0 →
    read64 m (a + 16) = some params →
    read32 m (a + 24) = some paramc →
    ParamsRepr m params paramc ps →
    read64 m (a + 32) = some body → StmtRepr m body (.block ss) →
    ExprRepr m a (.fn none ps ss)

/-- `Expr **` array of `n` expression pointers. -/
inductive ExprArrayRepr (m : Mem) : Nat → Nat → List Expr → Prop where
  | nil {a : Nat} : ExprArrayRepr m a 0 []
  | cons {a p n : Nat} {e : Expr} {es : List Expr} :
    read64 m a = some p → ExprRepr m p e →
    ExprArrayRepr m (a + 8) n es →
    ExprArrayRepr m a (n + 1) (e :: es)

/-- `char **` array of `n` parameter names. -/
inductive ParamsRepr (m : Mem) : Nat → Nat → List String → Prop where
  | nil {a : Nat} : ParamsRepr m a 0 []
  | cons {a p n : Nat} {x : String} {xs : List String} :
    read64 m a = some p → CString m p x →
    ParamsRepr m (a + 8) n xs →
    ParamsRepr m a (n + 1) (x :: xs)

/-- `Stmt` struct at address `a` (`ST_EXPR = 0 … ST_CONTINUE = 8`). -/
inductive StmtRepr (m : Mem) : Nat → Stmt → Prop where
  | expr {a p : Nat} {e : Expr} :
    read32 m a = some 0 → read64 m (a + 8) = some p → ExprRepr m p e →
    StmtRepr m a (.expr e)
  | varInit {a p q : Nat} {x : String} {e : Expr} :
    read32 m a = some 1 →
    read64 m (a + 8) = some p → CString m p x →
    read64 m (a + 16) = some q → q ≠ 0 → ExprRepr m q e →
    StmtRepr m a (.varDecl x (some e))
  | varNull {a p : Nat} {x : String} :
    read32 m a = some 1 →
    read64 m (a + 8) = some p → CString m p x →
    read64 m (a + 16) = some 0 →
    StmtRepr m a (.varDecl x none)
  | block {a stmts count : Nat} {ss : List Stmt} :
    read32 m a = some 2 →
    read64 m (a + 8) = some stmts →
    read32 m (a + 16) = some count →
    StmtArrayRepr m stmts count ss →
    StmtRepr m a (.block ss)
  | ifElse {a c t e : Nat} {ec : Expr} {st se : Stmt} :
    read32 m a = some 3 →
    read64 m (a + 8) = some c → ExprRepr m c ec →
    read64 m (a + 16) = some t → StmtRepr m t st →
    read64 m (a + 24) = some e → e ≠ 0 → StmtRepr m e se →
    StmtRepr m a (.ifStmt ec st (some se))
  | ifNoElse {a c t : Nat} {ec : Expr} {st : Stmt} :
    read32 m a = some 3 →
    read64 m (a + 8) = some c → ExprRepr m c ec →
    read64 m (a + 16) = some t → StmtRepr m t st →
    read64 m (a + 24) = some 0 →
    StmtRepr m a (.ifStmt ec st none)
  | whileS {a c b : Nat} {ec : Expr} {sb : Stmt} :
    read32 m a = some 4 →
    read64 m (a + 8) = some c → ExprRepr m c ec →
    read64 m (a + 16) = some b → StmtRepr m b sb →
    StmtRepr m a (.whileStmt ec sb)
  | forS {a b : Nat} {oinit : Option Stmt} {ocond ostep : Option Expr}
      {sb : Stmt} :
    read32 m a = some 5 →
    OptStmtRepr m (a + 8) oinit →
    OptExprRepr m (a + 16) ocond →
    OptExprRepr m (a + 24) ostep →
    read64 m (a + 32) = some b → StmtRepr m b sb →
    StmtRepr m a (.forStmt oinit ocond ostep sb)
  | retSome {a p : Nat} {e : Expr} :
    read32 m a = some 6 → read64 m (a + 8) = some p → p ≠ 0 →
    ExprRepr m p e →
    StmtRepr m a (.ret (some e))
  | retNone {a : Nat} :
    read32 m a = some 6 → read64 m (a + 8) = some 0 →
    StmtRepr m a (.ret none)
  | brk {a : Nat} : read32 m a = some 7 → StmtRepr m a .brk
  | cont {a : Nat} : read32 m a = some 8 → StmtRepr m a .cont

/-- An optional statement pointer field (NULL ↔ `none`). -/
inductive OptStmtRepr (m : Mem) : Nat → Option Stmt → Prop where
  | none {a : Nat} : read64 m a = some 0 → OptStmtRepr m a none
  | some {a p : Nat} {s : Stmt} :
    read64 m a = some p → p ≠ 0 → StmtRepr m p s →
    OptStmtRepr m a (some s)

/-- An optional expression pointer field (NULL ↔ `none`). -/
inductive OptExprRepr (m : Mem) : Nat → Option Expr → Prop where
  | none {a : Nat} : read64 m a = some 0 → OptExprRepr m a none
  | some {a p : Nat} {e : Expr} :
    read64 m a = some p → p ≠ 0 → ExprRepr m p e →
    OptExprRepr m a (some e)

/-- `Stmt **` array of `n` statement pointers (the shape `parse_program`
returns and `interp_run` consumes). -/
inductive StmtArrayRepr (m : Mem) : Nat → Nat → List Stmt → Prop where
  | nil {a : Nat} : StmtArrayRepr m a 0 []
  | cons {a p n : Nat} {s : Stmt} {ss : List Stmt} :
    read64 m a = some p → StmtRepr m p s →
    StmtArrayRepr m (a + 8) n ss →
    StmtArrayRepr m a (n + 1) (s :: ss)

end

/-- **A WHILE program represented in machine memory**: an array of `n`
statement pointers at `a`, exactly the arguments `interp_run` receives. -/
def ProgramRepr (m : Mem) (a n : Nat) (p : Program) : Prop :=
  StmtArrayRepr m a n p ∧ n = p.length

end Vsa.MemRepr
