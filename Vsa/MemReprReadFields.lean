import Vsa.MemReprWithin

namespace Vsa.MemRepr
open Vsa.While

structure ReadField where
  offset : Nat
  width : Nat
  positive : 0 < width

def ReadField.word32 (offset : Nat) : ReadField := ⟨offset, 4, by decide⟩
def ReadField.word64 (offset : Nat) : ReadField := ⟨offset, 8, by decide⟩

def exprReadFields (e : Expr) : List ReadField :=
  .word32 0 :: match e with
  | .int _ | .str _ | .var _ => [.word64 8]
  | .bool _ => [.word32 8]
  | .null => []
  | .assign _ _ => [.word64 8, .word64 16]
  | .binary _ _ _ | .logical _ _ _ => [.word32 8, .word64 16, .word64 24]
  | .unary _ _ => [.word32 8, .word64 16]
  | .call _ _ => [.word64 8, .word64 16, .word32 24]
  | .fn _ _ _ => [.word64 8, .word64 16, .word32 24, .word64 32]

def stmtReadFields (s : Stmt) : List ReadField :=
  .word32 0 :: match s with
  | .expr _ | .ret _ => [.word64 8]
  | .varDecl _ _ | .whileStmt _ _ => [.word64 8, .word64 16]
  | .block _ => [.word64 8, .word32 16]
  | .ifStmt _ _ _ => [.word64 8, .word64 16, .word64 24]
  | .forStmt _ _ _ _ => [.word64 8, .word64 16, .word64 24, .word64 32]
  | .brk | .cont => []

theorem OptExprReprWithin.covers {m : Mem} {P : Nat → Prop} {a : Nat}
    {e : Option Expr} (h : OptExprReprWithin m P a e) : Covers P a 8 := by
  cases h <;> assumption

theorem OptStmtReprWithin.covers {m : Mem} {P : Nat → Prop} {a : Nat}
    {s : Option Stmt} (h : OptStmtReprWithin m P a s) : Covers P a 8 := by
  cases h <;> assumption

theorem ExprReprWithin.fieldCovers {m : Mem} {P : Nat → Prop} {a : Nat}
    {e : Expr} (h : ExprReprWithin m P a e) :
    ∀ f ∈ exprReadFields e, Covers P (a + f.offset) f.width := by
  cases h <;> simp_all [exprReadFields, ReadField.word32, ReadField.word64]

theorem StmtReprWithin.fieldCovers {m : Mem} {P : Nat → Prop} {a : Nat}
    {s : Stmt} (h : StmtReprWithin m P a s) :
    ∀ f ∈ stmtReadFields s, Covers P (a + f.offset) f.width := by
  cases h <;> simp_all [stmtReadFields, ReadField.word32, ReadField.word64]
  exact ⟨OptStmtReprWithin.covers (by assumption),
    OptExprReprWithin.covers (by assumption), OptExprReprWithin.covers (by assumption)⟩

theorem ExprReprWithin.tagCovers {m : Mem} {P : Nat → Prop} {a : Nat}
    {e : Expr} (h : ExprReprWithin m P a e) : Covers P a 4 := by
  simpa [ReadField.word32] using h.fieldCovers (.word32 0) (by simp [exprReadFields])

theorem StmtReprWithin.tagCovers {m : Mem} {P : Nat → Prop} {a : Nat}
    {s : Stmt} (h : StmtReprWithin m P a s) : Covers P a 4 := by
  simpa [ReadField.word32] using h.fieldCovers (.word32 0) (by simp [stmtReadFields])

end Vsa.MemRepr
