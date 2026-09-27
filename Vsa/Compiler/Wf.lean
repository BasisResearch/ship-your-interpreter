import Vsa.Compiler.SUpd

/-!
# Static well-formedness of compiled programs

`WfE T Γ e`/`WfS T Γ s`: the code generator's static assumptions about a
subterm compiled under the chain of layouts `Γ` with string table `T`: integer
literals are 64-bit, strings and function names are Latin-1 and in the table,
declarations name slots of the current layout, scopes have at most 120 slots,
and function bodies at most 120 temporaries.
-/

namespace Vsa.Compiler

open Vsa.While

/-- Every character is a byte. -/
def Latin1 (s : String) : Prop := ∀ c ∈ s.toList, c.toNat < 256

mutual
def WfE (T : List String) (Γ : List (List String)) : Expr → Prop
  | .int n => I64 n
  | .str s => Latin1 s ∧ s ∈ T
  | .bool _ => True
  | .null => True
  | .var _ => True
  | .assign _ e => WfE T Γ e
  | .binary _ l r => WfE T Γ l ∧ WfE T Γ r
  | .logical _ l r => WfE T Γ l ∧ WfE T Γ r
  | .unary _ e => WfE T Γ e
  | .call f args => WfE T Γ f ∧ WfArgs T Γ args
  | .fn name params body =>
    Latin1 (dispName name) ∧ Latin1 (catName name) ∧ dispName name ∈ T ∧ catName name ∈ T ∧
      (frameNames params body).length ≤ 120 ∧ tSeq body ≤ 120 ∧
      WfSeq T (frameNames params body :: Γ) body

def WfArgs (T : List String) (Γ : List (List String)) : List Expr → Prop
  | [] => True
  | e :: es => WfE T Γ e ∧ WfArgs T Γ es

def WfOE (T : List String) (Γ : List (List String)) : Option Expr → Prop
  | none => True
  | some e => WfE T Γ e

def WfS (T : List String) (Γ : List (List String)) : Stmt → Prop
  | .expr e => WfE T Γ e
  | .varDecl x i => x ∈ Γ.headD [] ∧ WfOE T Γ i
  | .block ss => (frameNames [] ss).length ≤ 120 ∧ WfSeq T (frameNames [] ss :: Γ) ss
  | .ifStmt c t e => WfE T Γ c ∧ WfS T Γ t ∧ WfOS T Γ e
  | .whileStmt c b => WfE T Γ c ∧ WfS T Γ b
  | .forStmt i c st b =>
    (forNames i b).length ≤ 120 ∧ WfOS T (forNames i b :: Γ) i ∧ WfOE T (forNames i b :: Γ) c ∧
      WfOE T (forNames i b :: Γ) st ∧ WfS T (forNames i b :: Γ) b
  | .ret e => WfOE T Γ e
  | .brk => True
  | .cont => True

def WfOS (T : List String) (Γ : List (List String)) : Option Stmt → Prop
  | none => True
  | some s => WfS T Γ s

def WfSeq (T : List String) (Γ : List (List String)) : List Stmt → Prop
  | [] => True
  | s :: ss => WfS T Γ s ∧ WfSeq T Γ ss
end

end Vsa.Compiler
