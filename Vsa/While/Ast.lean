namespace Vsa.While

inductive BinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  deriving Repr, DecidableEq

inductive LogOp where
  | and | or
  deriving Repr, DecidableEq

inductive UnOp where
  | neg | not
  deriving Repr, DecidableEq

mutual

inductive Expr where
  | int (n : Int)
  | str (s : String)
  | bool (b : Bool)
  | null
  | var (x : String)
  | assign (x : String) (e : Expr)
  | binary (op : BinOp) (l r : Expr)
  | logical (op : LogOp) (l r : Expr)
  | unary (op : UnOp) (e : Expr)
  | call (f : Expr) (args : List Expr)

  | fn (name : Option String) (params : List String) (body : List Stmt)
  deriving Repr

inductive Stmt where
  | expr (e : Expr)
  | varDecl (x : String) (init : Option Expr)
  | block (ss : List Stmt)
  | ifStmt (cond : Expr) (thn : Stmt) (els : Option Stmt)
  | whileStmt (cond : Expr) (body : Stmt)
  | forStmt (init : Option Stmt) (cond : Option Expr) (step : Option Expr)
      (body : Stmt)
  | ret (e : Option Expr)
  | brk
  | cont
  deriving Repr

end

abbrev Program := List Stmt

end Vsa.While
