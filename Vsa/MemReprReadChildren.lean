import Vsa.MemReprReadFields

namespace Vsa.MemRepr
open Vsa.While

/-- Expression fields selected by recursive statement execution. -/
inductive StmtExprChild : Stmt → Nat → Expr → Prop where
  | expr (e) : StmtExprChild (.expr e) 8 e
  | varInit (x e) : StmtExprChild (.varDecl x (some e)) 16 e
  | ifCond (e t f) : StmtExprChild (.ifStmt e t f) 8 e
  | whileCond (e b) : StmtExprChild (.whileStmt e b) 8 e
  | forCond (i e s b) : StmtExprChild (.forStmt i (some e) s b) 16 e
  | forStep (i c e b) : StmtExprChild (.forStmt i c (some e) b) 24 e
  | ret (e) : StmtExprChild (.ret (some e)) 8 e

/-- Statement fields selected by recursive statement execution. -/
inductive StmtChild : Stmt → Nat → Stmt → Prop where
  | ifThen (c t f) : StmtChild (.ifStmt c t f) 16 t
  | ifElse (c t f) : StmtChild (.ifStmt c t (some f)) 24 f
  | whileBody (c b) : StmtChild (.whileStmt c b) 16 b
  | forInit (i c s b) : StmtChild (.forStmt (some i) c s b) 8 i
  | forBody (i c s b) : StmtChild (.forStmt i c s b) 32 b

local macro "select_owned_pointer" h:ident : tactic =>
  `(tactic| (cases ($h) <;> try simp_all only [Option.some.injEq]))

/-- A statement's expression pointer retains hereditary ownership. -/
theorem StmtReprWithin.exprChild {m : Mem} {P : Nat → Prop} {a p off : Nat}
    {s : Stmt} {e : Expr} (h : StmtReprWithin m P a s)
    (edge : StmtExprChild s off e) (hp : read64 m (a + off) = some p) :
    ExprReprWithin m P p e := by
  cases edge <;> select_owned_pointer h
  all_goals exact OptExprReprWithin.child (by assumption) hp

/-- A statement's statement pointer retains hereditary ownership. -/
theorem StmtReprWithin.child {m : Mem} {P : Nat → Prop} {a p off : Nat}
    {s child : Stmt} (h : StmtReprWithin m P a s)
    (edge : StmtChild s off child) (hp : read64 m (a + off) = some p) :
    StmtReprWithin m P p child := by
  cases edge <;> select_owned_pointer h
  exact OptStmtReprWithin.child (by assumption) hp

/-- A function's body pointer selects its represented block. -/
theorem ExprReprWithin.fnBody {m : Mem} {P : Nat → Prop} {a p : Nat}
    {name : Option String} {ps : List String} {ss : List Stmt}
    (h : ExprReprWithin m P a (.fn name ps ss))
    (hp : read64 m (a + 32) = some p) : StmtReprWithin m P p (.block ss) := by
  select_owned_pointer h

/-- A function's parameter pointer and count select its owned name array. -/
theorem ExprReprWithin.fnParams {m : Mem} {P : Nat → Prop} {a p n : Nat}
    {name : Option String} {ps : List String} {ss : List Stmt}
    (h : ExprReprWithin m P a (.fn name ps ss))
    (hp : read64 m (a + 16) = some p) (hn : read32 m (a + 24) = some n) :
    ParamsReprWithin m P p n ps := by
  select_owned_pointer h

/-- A call's argument pointer and count select its owned expression array. -/
theorem ExprReprWithin.callArgs {m : Mem} {P : Nat → Prop} {a p n : Nat}
    {f : Expr} {es : List Expr} (h : ExprReprWithin m P a (.call f es))
    (hp : read64 m (a + 16) = some p) (hn : read32 m (a + 24) = some n) :
    ExprArrayReprWithin m P p n es := by
  select_owned_pointer h

/-- A block's pointer and count select its owned statement array. -/
theorem StmtReprWithin.blockArray {m : Mem} {P : Nat → Prop} {a p n : Nat}
    {ss : List Stmt} (h : StmtReprWithin m P a (.block ss))
    (hp : read64 m (a + 8) = some p) (hn : read32 m (a + 16) = some n) :
    StmtArrayReprWithin m P p n ss := by
  select_owned_pointer h

#print axioms StmtReprWithin.exprChild
#print axioms StmtReprWithin.child
#print axioms ExprReprWithin.fnBody
#print axioms ExprReprWithin.fnParams
#print axioms ExprReprWithin.callArgs
#print axioms StmtReprWithin.blockArray
end Vsa.MemRepr
