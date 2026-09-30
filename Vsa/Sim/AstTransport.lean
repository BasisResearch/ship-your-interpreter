import Vsa.Sim.MemRegion

namespace Vsa.Sim

open Vsa.MemRepr
open Vsa.While

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

mutual

inductive ExprStrAt8 : Expr → String → Prop where
  | str (s) : ExprStrAt8 (.str s) s
  | var (x) : ExprStrAt8 (.var x) x
  | assign (x) (e) : ExprStrAt8 (.assign x e) x
  | fnNamed (x) (ps) (ss) : ExprStrAt8 (.fn (some x) ps ss) x

inductive ExprChildAt8 : Expr → Expr → Prop where
  | call (f) (args) : ExprChildAt8 (.call f args) f

inductive ExprChildAt16 : Expr → Expr → Prop where
  | assign (x) (e) : ExprChildAt16 (.assign x e) e
  | binary (op) (l) (r) : ExprChildAt16 (.binary op l r) l
  | logical (op) (l) (r) : ExprChildAt16 (.logical op l r) l
  | unary (op) (e) : ExprChildAt16 (.unary op e) e

inductive ExprChildAt24 : Expr → Expr → Prop where
  | binary (op) (l) (r) : ExprChildAt24 (.binary op l r) r
  | logical (op) (l) (r) : ExprChildAt24 (.logical op l r) r

inductive ExprArgsAt16 : Expr → List Expr → Prop where
  | call (f) (args) : ExprArgsAt16 (.call f args) args

inductive ExprParamsAt16 : Expr → List String → Prop where
  | fn (name) (ps) (ss) : ExprParamsAt16 (.fn name ps ss) ps

inductive ExprBodyAt32 : Expr → List Stmt → Prop where
  | fn (name) (ps) (ss) : ExprBodyAt32 (.fn name ps ss) ss

inductive StmtStrAt8 : Stmt → String → Prop where
  | varDecl (x) (oe) : StmtStrAt8 (.varDecl x oe) x

inductive StmtExprAt8 : Stmt → Expr → Prop where
  | expr (e) : StmtExprAt8 (.expr e) e
  | ifStmt (c) (t) (oe) : StmtExprAt8 (.ifStmt c t oe) c
  | whileStmt (c) (b) : StmtExprAt8 (.whileStmt c b) c
  | ret (e) : StmtExprAt8 (.ret (some e)) e

inductive StmtExprAt16 : Stmt → Expr → Prop where
  | varDecl (x) (e) : StmtExprAt16 (.varDecl x (some e)) e

inductive StmtChildAt16 : Stmt → Stmt → Prop where
  | ifStmt (c) (t) (oe) : StmtChildAt16 (.ifStmt c t oe) t
  | whileStmt (c) (b) : StmtChildAt16 (.whileStmt c b) b

inductive StmtChildAt24 : Stmt → Stmt → Prop where
  | ifStmt (c) (t) (e) : StmtChildAt24 (.ifStmt c t (some e)) e

inductive StmtChildAt32 : Stmt → Stmt → Prop where
  | forStmt (oi) (oc) (os) (b) : StmtChildAt32 (.forStmt oi oc os b) b

inductive StmtBlockAt8 : Stmt → List Stmt → Prop where
  | block (ss) : StmtBlockAt8 (.block ss) ss

inductive StmtOptStmtAt8 : Stmt → Option Stmt → Prop where
  | forStmt (oi) (oc) (os) (b) : StmtOptStmtAt8 (.forStmt oi oc os b) oi

inductive StmtOptExprAt16 : Stmt → Option Expr → Prop where
  | forStmt (oi) (oc) (os) (b) : StmtOptExprAt16 (.forStmt oi oc os b) oc

inductive StmtOptExprAt24 : Stmt → Option Expr → Prop where
  | forStmt (oi) (oc) (os) (b) : StmtOptExprAt24 (.forStmt oi oc os b) os

end

mutual

inductive ExprFp (m : Mem) : Nat → Expr → Nat → Prop where
  | tag {a : Nat} {e : Expr} {k : Nat} : k < 4 → ExprFp m a e (a + k)

  | off8 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 8 + k)
  | off16 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 16 + k)
  | off24 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 24 + k)
  | off32 {a : Nat} {e : Expr} {k : Nat} : k < 8 → ExprFp m a e (a + 32 + k)

  | str8 {a : Nat} {e : Expr} {s : String} {p k : Nat} :
    ExprStrAt8 e s → read64 m (a + 8) = some p → k ≤ s.length →
    ExprFp m a e (p + k)

  | child8 {a : Nat} {e ec : Expr} {p addr : Nat} :
    ExprChildAt8 e ec → read64 m (a + 8) = some p →
    ExprFp m p ec addr → ExprFp m a e addr
  | child16 {a : Nat} {e ec : Expr} {p addr : Nat} :
    ExprChildAt16 e ec → read64 m (a + 16) = some p →
    ExprFp m p ec addr → ExprFp m a e addr
  | child24 {a : Nat} {e ec : Expr} {p addr : Nat} :
    ExprChildAt24 e ec → read64 m (a + 24) = some p →
    ExprFp m p ec addr → ExprFp m a e addr

  | argArr {a : Nat} {e : Expr} {args argc addr : Nat} {es : List Expr} :
    ExprArgsAt16 e es → read64 m (a + 16) = some args →
    ExprArrayFp m args argc es addr → ExprFp m a e addr

  | paramsArr {a : Nat} {e : Expr} {params paramc addr : Nat} {ps : List String} :
    ExprParamsAt16 e ps → read64 m (a + 16) = some params →
    ParamsFp m params paramc ps addr → ExprFp m a e addr
  | body32 {a : Nat} {e : Expr} {body addr : Nat} {ss : List Stmt} :
    ExprBodyAt32 e ss → read64 m (a + 32) = some body →
    StmtFp m body (.block ss) addr → ExprFp m a e addr

inductive ExprArrayFp (m : Mem) : Nat → Nat → List Expr → Nat → Prop where
  | slot {a n : Nat} {e : Expr} {es : List Expr} {k : Nat} : k < 8 →
    ExprArrayFp m a (n + 1) (e :: es) (a + k)
  | elem {a p n addr : Nat} {e : Expr} {es : List Expr} :
    read64 m a = some p → ExprFp m p e addr →
    ExprArrayFp m a (n + 1) (e :: es) addr
  | tail {a n addr : Nat} {e : Expr} {es : List Expr} :
    ExprArrayFp m (a + 8) n es addr → ExprArrayFp m a (n + 1) (e :: es) addr

inductive ParamsFp (m : Mem) : Nat → Nat → List String → Nat → Prop where
  | slot {a n : Nat} {x : String} {xs : List String} {k : Nat} : k < 8 →
    ParamsFp m a (n + 1) (x :: xs) (a + k)
  | str {a p n k : Nat} {x : String} {xs : List String} :
    read64 m a = some p → k ≤ x.length →
    ParamsFp m a (n + 1) (x :: xs) (p + k)
  | tail {a n addr : Nat} {x : String} {xs : List String} :
    ParamsFp m (a + 8) n xs addr → ParamsFp m a (n + 1) (x :: xs) addr

inductive StmtFp (m : Mem) : Nat → Stmt → Nat → Prop where
  | tag {a : Nat} {s : Stmt} {k : Nat} : k < 4 → StmtFp m a s (a + k)
  | off8 {a : Nat} {s : Stmt} {k : Nat} : k < 8 → StmtFp m a s (a + 8 + k)
  | off16 {a : Nat} {s : Stmt} {k : Nat} : k < 8 → StmtFp m a s (a + 16 + k)
  | off24 {a : Nat} {s : Stmt} {k : Nat} : k < 8 → StmtFp m a s (a + 24 + k)
  | off32 {a : Nat} {s : Stmt} {k : Nat} : k < 8 → StmtFp m a s (a + 32 + k)

  | str8 {a : Nat} {s : Stmt} {x : String} {p k : Nat} :
    StmtStrAt8 s x → read64 m (a + 8) = some p → k ≤ x.length →
    StmtFp m a s (p + k)

  | expr8 {a : Nat} {s : Stmt} {p addr : Nat} {e : Expr} :
    StmtExprAt8 s e → read64 m (a + 8) = some p →
    ExprFp m p e addr → StmtFp m a s addr
  | expr16 {a : Nat} {s : Stmt} {p addr : Nat} {e : Expr} :
    StmtExprAt16 s e → read64 m (a + 16) = some p →
    ExprFp m p e addr → StmtFp m a s addr

  | stmt16 {a : Nat} {s : Stmt} {p addr : Nat} {t : Stmt} :
    StmtChildAt16 s t → read64 m (a + 16) = some p →
    StmtFp m p t addr → StmtFp m a s addr
  | stmt24 {a : Nat} {s : Stmt} {p addr : Nat} {t : Stmt} :
    StmtChildAt24 s t → read64 m (a + 24) = some p →
    StmtFp m p t addr → StmtFp m a s addr
  | stmt32 {a : Nat} {s : Stmt} {p addr : Nat} {t : Stmt} :
    StmtChildAt32 s t → read64 m (a + 32) = some p →
    StmtFp m p t addr → StmtFp m a s addr

  | blockArr {a : Nat} {s : Stmt} {stmts count addr : Nat} {ss : List Stmt} :
    StmtBlockAt8 s ss → read64 m (a + 8) = some stmts →
    StmtArrayFp m stmts count ss addr → StmtFp m a s addr

  | optStmt8 {a : Nat} {s : Stmt} {os : Option Stmt} {addr : Nat} :
    StmtOptStmtAt8 s os → OptStmtFp m (a + 8) os addr → StmtFp m a s addr
  | optExpr16 {a : Nat} {s : Stmt} {oe : Option Expr} {addr : Nat} :
    StmtOptExprAt16 s oe → OptExprFp m (a + 16) oe addr → StmtFp m a s addr
  | optExpr24 {a : Nat} {s : Stmt} {oe : Option Expr} {addr : Nat} :
    StmtOptExprAt24 s oe → OptExprFp m (a + 24) oe addr → StmtFp m a s addr

inductive OptStmtFp (m : Mem) : Nat → Option Stmt → Nat → Prop where
  | ptr {a : Nat} {os : Option Stmt} {k : Nat} : k < 8 → OptStmtFp m a os (a + k)
  | child {a p addr : Nat} {s : Stmt} :
    read64 m a = some p → StmtFp m p s addr → OptStmtFp m a (some s) addr

inductive OptExprFp (m : Mem) : Nat → Option Expr → Nat → Prop where
  | ptr {a : Nat} {oe : Option Expr} {k : Nat} : k < 8 → OptExprFp m a oe (a + k)
  | child {a p addr : Nat} {e : Expr} :
    read64 m a = some p → ExprFp m p e addr → OptExprFp m a (some e) addr

inductive StmtArrayFp (m : Mem) : Nat → Nat → List Stmt → Nat → Prop where
  | slot {a n : Nat} {s : Stmt} {ss : List Stmt} {k : Nat} : k < 8 →
    StmtArrayFp m a (n + 1) (s :: ss) (a + k)
  | elem {a p n addr : Nat} {s : Stmt} {ss : List Stmt} :
    read64 m a = some p → StmtFp m p s addr →
    StmtArrayFp m a (n + 1) (s :: ss) addr
  | tail {a n addr : Nat} {s : Stmt} {ss : List Stmt} :
    StmtArrayFp m (a + 8) n ss addr → StmtArrayFp m a (n + 1) (s :: ss) addr

end

private def R2 (m : Mem) (lo hi : Nat) :
    (a n : Nat) → (es : List Expr) → (addr : Nat) → ExprArrayFp m a n es addr → Prop :=
  fun a _ es addr _ => ExprsIn m lo hi a es → lo ≤ addr ∧ addr < hi
private def R3 (m : Mem) (lo hi : Nat) :
    (a n : Nat) → (xs : List String) → (addr : Nat) → ParamsFp m a n xs addr → Prop :=
  fun a _ xs addr _ => ParamsIn m lo hi a xs → lo ≤ addr ∧ addr < hi

section Transport

variable {P : Nat → Prop} {m m' : Mem}

private def M1 (_h : AgreeP P m m') : (a : Nat) → (e : Expr) → ExprRepr m a e → Prop :=
  fun a e _ => (∀ addr, ExprFp m a e addr → P addr) → ExprRepr m' a e
private def M2 (_h : AgreeP P m m') : (a n : Nat) → (es : List Expr) → ExprArrayRepr m a n es → Prop :=
  fun a n es _ => (∀ addr, ExprArrayFp m a n es addr → P addr) → ExprArrayRepr m' a n es

end Transport

end Vsa.Sim
