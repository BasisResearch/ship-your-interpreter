import Vsa.Sim.ReprSurvival

open Vsa.MemRepr Vsa.While

namespace Vsa.Sim

structure NodeIn (lo hi a : Nat) : Prop where
  lo_le : lo ≤ a
  hi_ge : a + 40 ≤ hi

structure CellIn (lo hi a : Nat) : Prop where
  lo_le : lo ≤ a
  hi_ge : a + 8 ≤ hi

structure StrIn (lo hi p : Nat) (s : String) : Prop where
  ne_zero : p ≠ 0
  lo_le : lo ≤ p
  hi_ge : p + s.length + 1 ≤ hi

def ParamsIn (m : Mem) (lo hi : Nat) : Nat → List String → Prop
  | _, [] => True
  | a, x :: xs =>
    CellIn lo hi a ∧
    (∀ p, read64 m a = some p → StrIn lo hi p x) ∧
    ParamsIn m lo hi (a + 8) xs

mutual

def ExprIn (m : Mem) (lo hi : Nat) : Nat → Expr → Prop
  | a, .int _ => NodeIn lo hi a
  | a, .str s => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p s)
  | a, .bool _ => NodeIn lo hi a
  | a, .null => NodeIn lo hi a
  | a, .var x => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p x)
  | a, .assign x e => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p x) ∧
      (∀ q, read64 m (a + 16) = some q → ExprIn m lo hi q e)
  | a, .binary _ l r => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p l) ∧
      (∀ p, read64 m (a + 24) = some p → ExprIn m lo hi p r)
  | a, .logical _ l r => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p l) ∧
      (∀ p, read64 m (a + 24) = some p → ExprIn m lo hi p r)
  | a, .unary _ e => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 16) = some p → ExprIn m lo hi p e)
  | a, .call f args => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p f) ∧
      (∀ q, read64 m (a + 16) = some q → ExprsIn m lo hi q args)
  | a, .fn ox ps ss => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p →
        ∀ x, ox = some x → StrIn lo hi p x) ∧
      (∀ q, read64 m (a + 16) = some q → ParamsIn m lo hi q ps) ∧

      (∀ b, read64 m (a + 32) = some b → NodeIn lo hi b ∧
        (∀ q, read64 m (b + 8) = some q → StmtsIn m lo hi q ss))

def ExprsIn (m : Mem) (lo hi : Nat) : Nat → List Expr → Prop
  | _, [] => True
  | a, e :: es =>
    CellIn lo hi a ∧
    (∀ p, read64 m a = some p → ExprIn m lo hi p e) ∧
    ExprsIn m lo hi (a + 8) es

def OptExprIn (m : Mem) (lo hi addr : Nat) : Option Expr → Prop
  | none => CellIn lo hi addr
  | some e => CellIn lo hi addr ∧
      (∀ p, read64 m addr = some p → ExprIn m lo hi p e)

def StmtIn (m : Mem) (lo hi : Nat) : Nat → Stmt → Prop
  | a, .expr e => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p e)
  | a, .varDecl x oe => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StrIn lo hi p x) ∧
      OptExprIn m lo hi (a + 16) oe
  | a, .block ss => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → StmtsIn m lo hi p ss)
  | a, .ifStmt c t oe => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p c) ∧
      (∀ p, read64 m (a + 16) = some p → StmtIn m lo hi p t) ∧
      OptStmtIn m lo hi (a + 24) oe
  | a, .whileStmt c b => NodeIn lo hi a ∧
      (∀ p, read64 m (a + 8) = some p → ExprIn m lo hi p c) ∧
      (∀ p, read64 m (a + 16) = some p → StmtIn m lo hi p b)
  | a, .forStmt oi oc os b => NodeIn lo hi a ∧
      OptStmtIn m lo hi (a + 8) oi ∧
      OptExprIn m lo hi (a + 16) oc ∧
      OptExprIn m lo hi (a + 24) os ∧
      (∀ p, read64 m (a + 32) = some p → StmtIn m lo hi p b)
  | a, .ret oe => NodeIn lo hi a ∧ OptExprIn m lo hi (a + 8) oe
  | a, .brk => NodeIn lo hi a
  | a, .cont => NodeIn lo hi a

def StmtsIn (m : Mem) (lo hi : Nat) : Nat → List Stmt → Prop
  | _, [] => True
  | a, s :: ss =>
    CellIn lo hi a ∧
    (∀ p, read64 m a = some p → StmtIn m lo hi p s) ∧
    StmtsIn m lo hi (a + 8) ss

def OptStmtIn (m : Mem) (lo hi addr : Nat) : Option Stmt → Prop
  | none => CellIn lo hi addr
  | some s => CellIn lo hi addr ∧
      (∀ p, read64 m addr = some p → StmtIn m lo hi p s)

end

end Vsa.Sim
