import Vsa.While.Ast

/-!
# Front end: WHILE source text to `Program`

A lexer and recursive-descent parser mirroring the C interpreter's
(`c/src/lexer.c`, `c/src/parser.c`) rule for rule, so a source file denotes
the same `Program` the interpreter runs. The input is a byte string: each byte
is one character, as in the C code, so every string literal is Latin-1.

* Integer literals are unsigned digit sequences, saturated at `2^63 - 1` like
  `strtoll`; negative numbers are unary minus applied to a literal.
* String literals resolve the escapes `\n \t \r \\ \" \0`; the contents end at
  the first NUL, like a C string.
* `fn name(params) { ... }` in declaration position declares `name`; other
  function literals are anonymous.

This front end is not verified; the correctness theorem starts from the
`Program` it produces.
-/

namespace Vsa.Compiler.Parse

open Vsa.While

/-- Tokens (`TokType` in `lexer.h`). -/
inductive Tok where
  | ident (s : String)
  | num (n : Nat)
  | str (s : String)
  | sym (s : String)
  | kw (s : String)
  | eof
  deriving BEq, Repr, Inhabited

structure Token where
  tok : Tok
  line : Nat
  deriving Inhabited

def keywords : List String :=
  ["var", "fn", "if", "else", "while", "for", "return", "break", "continue", "true", "false", "null"]

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
def isIdentStart (c : Char) : Bool := isAlpha c || c == '_'
def isIdentChar (c : Char) : Bool := isAlpha c || isDigit c || c == '_'

def lexError (line : Nat) (msg : String) : Except String α :=
  .error s!"parse error [line {line}]: {msg}"

/-- Resolve the escapes of a string literal's contents; the result ends at the
first NUL (`unescape_string`). -/
def unescape (line : Nat) : List Char → Except String (List Char)
  | [] => pure []
  | '\\' :: c :: rest => do
    let r ← unescape line rest
    match c with
    | 'n' => pure ('\n' :: r)
    | 't' => pure ('\t' :: r)
    | 'r' => pure ('\r' :: r)
    | '\\' => pure ('\\' :: r)
    | '"' => pure ('"' :: r)
    | '0' => pure ((Char.ofNat 0) :: r)
    | _ => lexError line "invalid escape sequence in string"
  | c :: rest => do pure (c :: (← unescape line rest))

/-- Skip whitespace and comments (`skip_ws`). -/
partial def skipWs (line : Nat) : List Char → Except String (Nat × List Char)
  | ' ' :: r | '\t' :: r | '\r' :: r => skipWs line r
  | '\n' :: r => skipWs (line + 1) r
  | '/' :: '/' :: r => skipWs line (r.dropWhile (· != '\n'))
  | '/' :: '*' :: r =>
    let rec block (line : Nat) : List Char → Except String (Nat × List Char)
      | [] => lexError line "unterminated block comment"
      | '*' :: '/' :: r => pure (line, r)
      | '\n' :: r => block (line + 1) r
      | _ :: r => block line r
    do let (line, r) ← block line r; skipWs line r
  | r => pure (line, r)

/-- The body of a string literal after its opening quote: its raw contents and
the rest (the lexer skips the character after a backslash). -/
partial def strBody (line : Nat) : List Char → Except String (List Char × Nat × List Char)
  | [] => lexError line "unterminated string literal"
  | '"' :: r => pure ([], line, r)
  | '\\' :: c :: r => do
    let (b, l, r) ← strBody (if c == '\n' then line + 1 else line) r
    pure ('\\' :: c :: b, l, r)
  | c :: r => do
    let (b, l, r) ← strBody (if c == '\n' then line + 1 else line) r
    pure (c :: b, l, r)

def twoChar : List (Char × Char × String) :=
  [('!', '=', "!="), ('=', '=', "=="), ('<', '=', "<="), ('>', '=', ">="), ('&', '&', "&&"), ('|', '|', "||")]

def oneChar : List Char := ['(', ')', '{', '}', ',', ';', '+', '-', '*', '/', '%', '!', '=', '<', '>']

/-- The token stream of a source (`lexer_next`, iterated to the end). -/
partial def lex (line : Nat) (cs : List Char) (acc : Array Token) : Except String (Array Token) := do
  let (line, cs) ← skipWs line cs
  match cs with
  | [] => pure (acc.push ⟨.eof, line⟩)
  | c :: r =>
    if isDigit c then
      let ds := cs.takeWhile isDigit
      let n := ds.foldl (fun n d => 10 * n + (d.toNat - '0'.toNat)) 0
      lex line (cs.dropWhile isDigit) (acc.push ⟨.num n, line⟩)
    else if isIdentStart c then
      let w := String.ofList (cs.takeWhile isIdentChar)
      let t := if keywords.contains w then Tok.kw w else Tok.ident w
      lex line (cs.dropWhile isIdentChar) (acc.push ⟨t, line⟩)
    else if c == '"' then
      let (body, line', rest) ← strBody line r
      let s ← unescape line' body
      lex line' rest (acc.push ⟨.str (String.ofList (s.takeWhile (· != Char.ofNat 0))), line'⟩)
    else
      match r, twoChar.find? (fun (a, b, _) => a == c && r.head? == some b) with
      | _ :: r', some (_, _, s) => lex line r' (acc.push ⟨.sym s, line⟩)
      | _, _ =>
        if c == '&' then lexError line "unexpected character '&' (did you mean '&&'?)"
        else if c == '|' then lexError line "unexpected character '|' (did you mean '||'?)"
        else if oneChar.contains c then lex line r (acc.push ⟨.sym (String.singleton c), line⟩)
        else lexError line "unexpected character"

def tokName : Tok → String
  | .ident _ => "identifier"
  | .num _ => "number"
  | .str _ => "string"
  | .sym s => s!"'{s}'"
  | .kw s => s!"'{s}'"
  | .eof => "end of input"

/-- Parser state: the token array and the current position. -/
abbrev P := StateT Nat (ReaderT (Array Token) (Except String))

def cur : P Token := do return (← read)[← get]!
def peek2 : P Token := do return (← read)[(← get) + 1]!
def advance : P Unit := modify (· + 1)
def check (t : Tok) : P Bool := do return (← cur).tok == t
def failAt (line : Nat) (msg : String) : P α := throw s!"parse error [line {line}]: {msg}"

def accept (t : Tok) : P Bool := do
  if ← check t then advance; return true else return false

def expect (t : Tok) (what : String) : P Unit := do
  let c ← cur
  if c.tok == t then advance
  else failAt c.line s!"expected {what} but found {tokName c.tok}"

def expectIdent (what : String) : P String := do
  let c ← cur
  match c.tok with
  | .ident s => advance; return s
  | t => failAt c.line s!"expected {what} but found {tokName t}"

def sym (s : String) : Tok := .sym s
def kw (s : String) : Tok := .kw s

def binOps : List (List (String × BinOp)) :=
  [[("==", .eq), ("!=", .ne)], [("<", .lt), ("<=", .le), (">", .gt), (">=", .ge)],
   [("+", .add), ("-", .sub)], [("*", .mul), ("/", .div), ("%", .mod)]]

/-- `strtoll` on a digit string: saturates at `2^63 - 1`. -/
def clampInt (n : Nat) : Int := if n < 2 ^ 63 then n else 2 ^ 63 - 1

mutual

partial def expression : P Expr := assignment

partial def assignment : P Expr := do
  let e ← logicOr
  let c ← cur
  if c.tok == sym "=" then
    advance
    match e with
    | .var x => return .assign x (← assignment)
    | _ => failAt c.line "invalid assignment target"
  else return e

partial def logicOr : P Expr := do
  let mut e ← logicAnd
  while ← accept (sym "||") do
    e := .logical .or e (← logicAnd)
  return e

partial def logicAnd : P Expr := do
  let mut e ← binLevel 0
  while ← accept (sym "&&") do
    e := .logical .and e (← binLevel 0)
  return e

/-- One left-associative binary level: equality, comparison, term, factor. -/
partial def binLevel (k : Nat) : P Expr := do
  let next : P Expr := if k + 1 < binOps.length then binLevel (k + 1) else unary
  let ops := binOps[k]!
  let mut e ← next
  repeat
    let c ← cur
    match ops.find? (fun (s, _) => c.tok == sym s) with
    | some (_, op) => advance; e := .binary op e (← next)
    | none => break
  return e

partial def unary : P Expr := do
  if ← accept (sym "-") then return .unary .neg (← unary)
  if ← accept (sym "!") then return .unary .not (← unary)
  call

partial def call : P Expr := do
  let mut e ← primary
  while ← accept (sym "(") do
    let mut args : Array Expr := #[]
    unless ← check (sym ")") do
      args := args.push (← expression)
      while ← accept (sym ",") do
        args := args.push (← expression)
    expect (sym ")") "')' after arguments"
    e := .call e args.toList
  return e

partial def primary : P Expr := do
  let c ← cur
  match c.tok with
  | .num n => advance; return .int (clampInt n)
  | .str s => advance; return .str s
  | .kw "true" => advance; return .bool true
  | .kw "false" => advance; return .bool false
  | .kw "null" => advance; return .null
  | .ident x => advance; return .var x
  | .sym "(" =>
    advance
    let e ← expression
    expect (sym ")") "')' after expression"
    return e
  | .kw "fn" => advance; fnExpr none
  | t => failAt c.line s!"unexpected {tokName t} in expression"

/-- A function literal after `fn` (and its name, for declarations). -/
partial def fnExpr (name : Option String) : P Expr := do
  expect (sym "(") "'(' after 'fn'"
  let mut ps : Array String := #[]
  unless ← check (sym ")") do
    ps := ps.push (← expectIdent "parameter name")
    while ← accept (sym ",") do
      ps := ps.push (← expectIdent "parameter name")
  expect (sym ")") "')' after parameters"
  return .fn name ps.toList (← blockStmts)

/-- A braced statement list. -/
partial def blockStmts : P (List Stmt) := do
  expect (sym "{") "'{'"
  let mut ss : Array Stmt := #[]
  while !(← check (sym "}")) && !(← check .eof) do
    ss := ss.push (← declaration)
  expect (sym "}") "'}' after block"
  return ss.toList

partial def varDecl : P Stmt := do
  advance
  let x ← expectIdent "variable name"
  let init ← if ← accept (sym "=") then some <$> expression else pure none
  expect (sym ";") "';' after variable declaration"
  return .varDecl x init

partial def statement : P Stmt := do
  let c ← cur
  match c.tok with
  | .sym "{" => return .block (← blockStmts)
  | .kw "if" =>
    advance
    expect (sym "(") "'(' after 'if'"
    let cnd ← expression
    expect (sym ")") "')' after if condition"
    let t ← statement
    let e ← if ← accept (kw "else") then some <$> statement else pure none
    return .ifStmt cnd t e
  | .kw "while" =>
    advance
    expect (sym "(") "'(' after 'while'"
    let cnd ← expression
    expect (sym ")") "')' after while condition"
    return .whileStmt cnd (← statement)
  | .kw "for" =>
    advance
    expect (sym "(") "'(' after 'for'"
    let init ← if ← accept (sym ";") then pure none
      else if ← check (kw "var") then some <$> varDecl
      else do
        let e ← expression
        expect (sym ";") "';' after for-loop initializer"
        pure (some (.expr e))
    let cnd ← if ← check (sym ";") then pure none else some <$> expression
    expect (sym ";") "';' after for-loop condition"
    let step ← if ← check (sym ")") then pure none else some <$> expression
    expect (sym ")") "')' after for-loop clauses"
    return .forStmt init cnd step (← statement)
  | .kw "return" =>
    advance
    let e ← if ← check (sym ";") then pure none else some <$> expression
    expect (sym ";") "';' after return value"
    return .ret e
  | .kw "break" => advance; expect (sym ";") "';' after 'break'"; return .brk
  | .kw "continue" => advance; expect (sym ";") "';' after 'continue'"; return .cont
  | _ =>
    let e ← expression
    expect (sym ";") "';' after expression"
    return .expr e

partial def declaration : P Stmt := do
  if ← check (kw "var") then return ← varDecl
  if (← check (kw "fn")) && (match (← peek2).tok with | .ident _ => true | _ => false) then
    advance
    let x ← expectIdent "function name"
    return .varDecl x (some (← fnExpr (some x)))
  statement

end

partial def program : P (List Stmt) := do
  let mut ss : Array Stmt := #[]
  while !(← check .eof) do
    ss := ss.push (← declaration)
  return ss.toList

/-- Parse a source given as bytes (one character per byte). -/
def parseBytes (src : ByteArray) : Except String Program := do
  let cs := src.toList.map fun b => Char.ofNat b.toNat
  let toks ← lex 1 cs #[]
  (program.run' 0).run toks

end Vsa.Compiler.Parse
