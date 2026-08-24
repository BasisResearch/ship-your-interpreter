/-!
# Deep embedding of the WHILE language

Abstract syntax mirroring `c/src/ast.h` of the C interpreter compiled into
`while-riscv-htif.elf`. The C AST is the parser's output; this embedding is
the same tree, so a WHILE source file corresponds to a `List Stmt` (the
program) exactly as in the binary.
-/

namespace Vsa.While

/-- Binary operators (`c/src/ast.h` EX_BINARY, ops are token types). -/
inductive BinOp where
  | add | sub | mul | div | mod
  | eq | ne | lt | le | gt | ge
  deriving Repr, DecidableEq

/-- Short-circuiting logical operators (EX_LOGICAL). -/
inductive LogOp where
  | and | or
  deriving Repr, DecidableEq

/-- Unary operators (EX_UNARY). -/
inductive UnOp where
  | neg | not
  deriving Repr, DecidableEq

mutual

/-- Expressions (`ExprKind` in ast.h). -/
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
  /-- Function literal; `fn f(x) {...}` declarations desugar to
  `var f = fn f(x) {...}` in the parser, so the AST only has literals.
  The body is always a block (list of statements). -/
  | fn (name : Option String) (params : List String) (body : List Stmt)
  deriving Repr

/-- Statements (`StmtKind` in ast.h). -/
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

/-- A WHILE program is a statement list, executed in the global scope. -/
abbrev Program := List Stmt

end Vsa.While
