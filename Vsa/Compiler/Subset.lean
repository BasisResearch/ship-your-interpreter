import Vsa.While.Semantics

/-!
# The supported WHILE subset

A predicate on `Program`, built from the existing syntax: integer and boolean
expressions over statically resolved variables, `if`/`while`/blocks,
`break`/`continue` inside loops, variable declarations with an initializer as
elements of a statement list, and `print`/`println` of integers.

Name resolution is static and follows the semantics' frames: a name scope is the
list of names declared so far in each enclosing frame, innermost first. A
declaration only extends the innermost frame, and only as an element of a
statement list, so every run of the program's statements defines exactly the
names the scope lists.
-/

namespace Vsa.Compiler

open Vsa.While

/-- Names declared so far in each enclosing frame, innermost first. -/
abbrev NScope := List (List String)

def NScope.Mem (Γ : NScope) (x : String) : Prop := ∃ f ∈ Γ, x ∈ f

/-- The interpreter's built-in names. -/
def IsNative (x : String) : Prop := x = "print" ∨ x = "println" ∨ x = "assert"

/-- 64-bit integer literal. -/
def InRange (n : Int) : Prop := -2^63 ≤ n ∧ n < 2^63

def ArithOp (op : BinOp) : Prop :=
  op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div ∨ op = .mod

def CmpOp (op : BinOp) : Prop :=
  op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge ∨ op = .eq ∨ op = .ne

mutual

/-- Integer-valued expressions. -/
def IntE (Γ : NScope) : Expr → Prop
  | .int n => InRange n
  | .var x => Γ.Mem x
  | .assign x e => Γ.Mem x ∧ IntE Γ e
  | .binary op l r => ArithOp op ∧ IntE Γ l ∧ IntE Γ r
  | .unary .neg e => IntE Γ e
  | _ => False

/-- Boolean-valued expressions. -/
def BoolE (Γ : NScope) : Expr → Prop
  | .bool _ => True
  | .binary op l r => CmpOp op ∧ IntE Γ l ∧ IntE Γ r
  | .unary .not e => IntE Γ e ∨ BoolE Γ e
  | _ => False

end

/-- Conditions and expression statements: integer or boolean. -/
def CondE (Γ : NScope) (e : Expr) : Prop := IntE Γ e ∨ BoolE Γ e

mutual

/-- A supported statement in statement position (not a declaration). `loop`
says whether a `while` encloses it. -/
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

/-- A supported statement list; declarations extend the innermost frame. -/
def SupSeq (Γ : NScope) (loop : Bool) : List Stmt → Prop
  | [] => True
  | .varDecl x (some e) :: ss =>
    ¬ IsNative x ∧ IntE Γ e ∧
      SupSeq (match Γ with | f :: g => (x :: f) :: g | [] => [[x]]) loop ss
  | s :: ss => SupS Γ loop s ∧ SupSeq Γ loop ss

/-- Integer call arguments. -/
def SupArgs (Γ : NScope) : List Expr → Prop
  | [] => True
  | e :: es => IntE Γ e ∧ SupArgs Γ es

end

/-- **The supported subset**: a program whose top-level statement list is
supported in the global frame, outside any loop. -/
def Supported (p : Program) : Prop := SupSeq [[]] false p

end Vsa.Compiler
