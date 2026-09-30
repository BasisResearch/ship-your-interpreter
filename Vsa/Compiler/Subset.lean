import Vsa.While.Semantics

namespace Vsa.Compiler

open Vsa.While

abbrev NScope := List (List String)

def NScope.Mem (Γ : NScope) (x : String) : Prop := ∃ f ∈ Γ, x ∈ f

def IsNative (x : String) : Prop := x = "print" ∨ x = "println" ∨ x = "assert"

def InRange (n : Int) : Prop := -2^63 ≤ n ∧ n < 2^63

def ArithOp (op : BinOp) : Prop :=
  op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod

def CmpOp (op : BinOp) : Prop :=
  op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge ∨ op = .eq ∨ op = .ne

mutual

def IntE (Γ : NScope) : Expr → Prop
  | .int n => InRange n
  | .var x => Γ.Mem x
  | .assign x e => Γ.Mem x ∧ IntE Γ e
  | .binary op l r => ArithOp op ∧ IntE Γ l ∧ IntE Γ r
  | .unary .neg e => IntE Γ e
  | _ => False

def BoolE (Γ : NScope) : Expr → Prop
  | .bool _ => True
  | .binary op l r => CmpOp op ∧ IntE Γ l ∧ IntE Γ r
  | .unary .not e => IntE Γ e ∨ BoolE Γ e
  | _ => False

end

def CondE (Γ : NScope) (e : Expr) : Prop := IntE Γ e ∨ BoolE Γ e

def NScope.declare : NScope → String → NScope
  | f :: g, x => (if x ∈ f then f else x :: f) :: g
  | [], x => [[x]]

mutual

def SupS (Γ : NScope) (loop : Bool) : Stmt → Prop
  | .expr (.call (.var f) args) =>
    (f = "print" ∨ f = "println") ∧ args.length ≤ maxArgs ∧ SupArgs Γ args
  | .expr e => CondE Γ e
  | .block ss => SupSeq ([] :: Γ) loop ss
  | .ifStmt c t none => CondE Γ c ∧ SupS Γ loop t
  | .ifStmt c t (some e) => CondE Γ c ∧ SupS Γ loop t ∧ SupS Γ loop e
  | .whileStmt c b => CondE Γ c ∧ SupS Γ true b
  | .brk => loop = true
  | .cont => loop = true
  | _ => False

def SupSeq (Γ : NScope) (loop : Bool) : List Stmt → Prop
  | [] => True
  | .varDecl x (some e) :: ss =>
    ¬ IsNative x ∧ IntE Γ e ∧
      SupSeq (NScope.declare Γ x) loop ss
  | s :: ss => SupS Γ loop s ∧ SupSeq Γ loop ss

def SupArgs (Γ : NScope) : List Expr → Prop
  | [] => True
  | e :: es => IntE Γ e ∧ SupArgs Γ es

end

def Supported (p : Program) : Prop := SupSeq [[]] false p

end Vsa.Compiler
