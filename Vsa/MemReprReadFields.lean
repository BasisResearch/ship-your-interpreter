import Vsa.MemReprWithin

namespace Vsa.MemRepr
open Vsa.While

/-- Offset and positive width of one represented AST read. -/
structure ReadField where
  offset : Nat
  width : Nat
  positive : 0 < width

def ReadField.word32 (offset : Nat) : ReadField := ⟨offset, 4, by decide⟩
def ReadField.word64 (offset : Nat) : ReadField := ⟨offset, 8, by decide⟩

/-- Fields read by the expression representation, excluding unused payload bytes. -/
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

/-- Fields read by the statement representation, including optional pointer slots. -/
def stmtReadFields (s : Stmt) : List ReadField :=
  .word32 0 :: match s with
  | .expr _ | .ret _ => [.word64 8]
  | .varDecl _ _ | .whileStmt _ _ => [.word64 8, .word64 16]
  | .block _ => [.word64 8, .word32 16]
  | .ifStmt _ _ _ => [.word64 8, .word64 16, .word64 24]
  | .forStmt _ _ _ _ => [.word64 8, .word64 16, .word64 24, .word64 32]
  | .brk | .cont => []

/-- Optional expression fields cover their pointer, including NULL. -/
theorem OptExprReprWithin.covers {m : Mem} {P : Nat → Prop} {a : Nat}
    {e : Option Expr} (h : OptExprReprWithin m P a e) : Covers P a 8 := by
  cases h <;> assumption

/-- Optional statement fields cover their pointer, including NULL. -/
theorem OptStmtReprWithin.covers {m : Mem} {P : Nat → Prop} {a : Nat}
    {s : Option Stmt} (h : OptStmtReprWithin m P a s) : Covers P a 8 := by
  cases h <;> assumption

/-- Every constructor-specific expression field has its declared coverage. -/
theorem ExprReprWithin.fieldCovers {m : Mem} {P : Nat → Prop} {a : Nat}
    {e : Expr} (h : ExprReprWithin m P a e) :
    ∀ f ∈ exprReadFields e, Covers P (a + f.offset) f.width := by
  cases h <;> simp_all [exprReadFields, ReadField.word32, ReadField.word64]

/-- Every constructor-specific statement field has its declared coverage. -/
theorem StmtReprWithin.fieldCovers {m : Mem} {P : Nat → Prop} {a : Nat}
    {s : Stmt} (h : StmtReprWithin m P a s) :
    ∀ f ∈ stmtReadFields s, Covers P (a + f.offset) f.width := by
  cases h <;> simp_all [stmtReadFields, ReadField.word32, ReadField.word64]
  exact ⟨OptStmtReprWithin.covers (by assumption),
    OptExprReprWithin.covers (by assumption), OptExprReprWithin.covers (by assumption)⟩

/-- All represented expression constructors cover their four-byte tag. -/
theorem ExprReprWithin.tagCovers {m : Mem} {P : Nat → Prop} {a : Nat}
    {e : Expr} (h : ExprReprWithin m P a e) : Covers P a 4 := by
  simpa [ReadField.word32] using h.fieldCovers (.word32 0) (by simp [exprReadFields])

/-- All represented statement constructors cover their four-byte tag. -/
theorem StmtReprWithin.tagCovers {m : Mem} {P : Nat → Prop} {a : Nat}
    {s : Stmt} (h : StmtReprWithin m P a s) : Covers P a 4 := by
  simpa [ReadField.word32] using h.fieldCovers (.word32 0) (by simp [stmtReadFields])

#print axioms ExprReprWithin.fieldCovers
#print axioms StmtReprWithin.fieldCovers
#print axioms ExprReprWithin.tagCovers
#print axioms StmtReprWithin.tagCovers
#print axioms OptExprReprWithin.covers
#print axioms OptStmtReprWithin.covers

/-- A represented expression field fits in the legacy node extent. -/
theorem exprReadFields.bounded (e : Expr) :
    ∀ f ∈ exprReadFields e, f.offset + f.width ≤ 40 := by
  cases e <;> simp [exprReadFields, ReadField.word32, ReadField.word64]

/-- A represented statement field fits in the legacy node extent. -/
theorem stmtReadFields.bounded (s : Stmt) :
    ∀ f ∈ stmtReadFields s, f.offset + f.width ≤ 40 := by
  cases s <;> simp [stmtReadFields, ReadField.word32, ReadField.word64]

/-- Expression child fields used by recursive evaluation. -/
inductive ExprChild : Expr → Nat → Expr → Prop where
  | assign (x e) : ExprChild (.assign x e) 16 e
  | binaryLeft (op l r) : ExprChild (.binary op l r) 16 l
  | binaryRight (op l r) : ExprChild (.binary op l r) 24 r
  | logicalLeft (op l r) : ExprChild (.logical op l r) 16 l
  | logicalRight (op l r) : ExprChild (.logical op l r) 24 r
  | unary (op e) : ExprChild (.unary op e) 16 e
  | callee (f es) : ExprChild (.call f es) 8 f

local macro "select_owned_pointer" h:ident : tactic =>
  `(tactic| (cases ($h) <;> simp_all only [Option.some.injEq]))

/-- A recursive expression read selects the same hereditarily covered child. -/
theorem ExprReprWithin.child {m : Mem} {P : Nat → Prop} {a p off : Nat}
    {e child : Expr} (h : ExprReprWithin m P a e) (edge : ExprChild e off child)
    (hp : read64 m (a + off) = Option.some p) : ExprReprWithin m P p child := by
  cases edge <;> select_owned_pointer h

/-- Optional expression children retain their coverage after pointer selection. -/
theorem OptExprReprWithin.child {m : Mem} {P : Nat → Prop} {a p : Nat}
    {e : Expr} (h : OptExprReprWithin m P a (Option.some e))
    (hp : read64 m a = Option.some p) : ExprReprWithin m P p e := by
  select_owned_pointer h

/-- Optional statement children retain their coverage after pointer selection. -/
theorem OptStmtReprWithin.child {m : Mem} {P : Nat → Prop} {a p : Nat}
    {s : Stmt} (h : OptStmtReprWithin m P a (Option.some s))
    (hp : read64 m a = Option.some p) : StmtReprWithin m P p s := by
  select_owned_pointer h

#print axioms exprReadFields.bounded
#print axioms stmtReadFields.bounded
#print axioms ExprReprWithin.child
#print axioms OptExprReprWithin.child
#print axioms OptStmtReprWithin.child

end Vsa.MemRepr
