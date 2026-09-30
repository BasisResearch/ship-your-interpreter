import Vsa.While.Ast

namespace Vsa.While.Parse

open Vsa.While

inductive Tok where
  | ident (s : String)
  | num (n : Nat)
  | str (s : String)
  | kw (s : String)
  | sym (s : String)
  | eof
  deriving Repr, BEq, Inhabited

structure Token where
  tok : Tok
  line : Nat
  deriving Inhabited

def keywords : List String :=
  ["var", "fn", "if", "else", "while", "for", "return", "break", "continue", "true", "false",
   "null"]

def Tok.describe : Tok → String
  | .ident _ => "identifier"
  | .num _ => "number"
  | .str _ => "string"
  | .kw k => s!"'{k}'"
  | .sym s => s!"'{s}'"
  | .eof => "end of input"

def err {α : Type} (line : Nat) (msg : String) : Except String α :=
  .error s!"parse error [line {line}]: {msg}"

def unescape (line : Nat) : List Char → Except String (List Char)
  | [] => pure []
  | '\\' :: c :: cs => do
    let d ← match c with
      | 'n' => pure '\n' | 't' => pure '\t' | 'r' => pure '\r'
      | '\\' => pure '\\' | '"' => pure '"' | '0' => pure (Char.ofNat 0)
      | _ => err line "invalid escape sequence in string"
    pure (d :: (← unescape line cs))
  | c :: cs => do pure (c :: (← unescape line cs))

partial def lex (cs : List Char) (line : Nat) (acc : Array Token) : Except String (Array Token) :=
  match cs with
  | [] => pure (acc.push ⟨.eof, line⟩)
  | '\n' :: cs => lex cs (line + 1) acc
  | ' ' :: cs | '\t' :: cs | '\r' :: cs => lex cs line acc
  | '/' :: '/' :: cs => lex (cs.dropWhile (· != '\n')) line acc
  | '/' :: '*' :: cs =>
    let rec skip (cs : List Char) (line : Nat) : Except String (List Char × Nat) :=
      match cs with
      | [] => err line "unterminated block comment"
      | '*' :: '/' :: cs => pure (cs, line)
      | '\n' :: cs => skip cs (line + 1)
      | _ :: cs => skip cs line
    do let (cs, line') ← skip cs line; lex cs line' acc
  | '"' :: cs =>
    let rec lit (cs : List Char) (line : Nat) (body : List Char) :
        Except String (List Char × List Char × Nat) :=
      match cs with
      | [] => err line "unterminated string literal"
      | '"' :: cs => pure (body.reverse, cs, line)
      | '\\' :: c :: cs => lit cs (if c == '\n' then line + 1 else line) (c :: '\\' :: body)
      | c :: cs => lit cs (if c == '\n' then line + 1 else line) (c :: body)
    do
      let (body, cs, line') ← lit cs line []
      let s ← unescape line body
      lex cs line' (acc.push ⟨.str (String.ofList s), line⟩)
  | c :: rest =>
    if c.isDigit then
      let ds := cs.takeWhile Char.isDigit
      let n := ds.foldl (fun n d => n * 10 + (d.toNat - '0'.toNat)) 0
      lex (cs.dropWhile Char.isDigit) line (acc.push ⟨.num n, line⟩)
    else if c.isAlpha || c == '_' then
      let w := cs.takeWhile fun d => d.isAlphanum || d == '_'
      let s := String.ofList w
      let t := if s ∈ keywords then Tok.kw s else Tok.ident s
      lex (cs.dropWhile fun d => d.isAlphanum || d == '_') line (acc.push ⟨t, line⟩)
    else
      match c, rest with
      | '!', '=' :: r => lex r line (acc.push ⟨.sym "!=", line⟩)
      | '=', '=' :: r => lex r line (acc.push ⟨.sym "==", line⟩)
      | '<', '=' :: r => lex r line (acc.push ⟨.sym "<=", line⟩)
      | '>', '=' :: r => lex r line (acc.push ⟨.sym ">=", line⟩)
      | '&', '&' :: r => lex r line (acc.push ⟨.sym "&&", line⟩)
      | '|', '|' :: r => lex r line (acc.push ⟨.sym "||", line⟩)
      | '&', _ => err line "unexpected character '&' (did you mean '&&'?)"
      | '|', _ => err line "unexpected character '|' (did you mean '||'?)"
      | c, r =>
        if "(){},;+-*/%!=<>".toList.contains c then
          lex r line (acc.push ⟨.sym (String.singleton c), line⟩)
        else err line "unexpected character"

abbrev P := StateT Nat (ReaderT (Array Token) (Except String))

def peek : P Token := do
  let i ← get
  let ts ← read
  pure (ts[i]?.getD ⟨.eof, 0⟩)

def peek2 : P Tok := do
  let i ← get
  let ts ← read
  pure ((ts[i + 1]?.map (·.tok)).getD .eof)

def advance : P Unit := modify (· + 1)

def isSym (s : String) : P Bool := do pure ((← peek).tok == .sym s)
def isKw (s : String) : P Bool := do pure ((← peek).tok == .kw s)

def fail {α : Type} (msg : String) : P α := do
  let t ← peek
  (err t.line msg : Except String α)

def expectSym (s : String) (what : String) : P Unit := do
  if ← isSym s then advance
  else fail s!"expected {what} but found {(← peek).tok.describe}"

def expectIdent (what : String) : P String := do
  match (← peek).tok with
  | .ident x => advance; pure x
  | t => fail s!"expected {what} but found {t.describe}"

def matchSym (s : String) : P Bool := do
  if ← isSym s then advance; pure true else pure false

def intLit (n : Nat) : Int := if n < 2 ^ 63 then n else 2 ^ 63 - 1

mutual

partial def expression : P Expr := assignment

partial def assignment : P Expr := do
  let e ← logicOr
  if ← isSym "=" then
    advance
    match e with
    | .var x => pure (.assign x (← assignment))
    | _ => fail "invalid assignment target"
  else pure e

partial def logicOr : P Expr := do
  let mut e ← logicAnd
  while ← isSym "||" do
    advance
    e := .logical .or e (← logicAnd)
  pure e

partial def logicAnd : P Expr := do
  let mut e ← binLevel 0
  while ← isSym "&&" do
    advance
    e := .logical .and e (← binLevel 0)
  pure e

partial def binLevel (lvl : Nat) : P Expr := do
  if lvl ≥ 4 then return ← unary
  let ops : List (String × BinOp) := match lvl with
    | 0 => [("==", .eq), ("!=", .ne)]
    | 1 => [("<", .lt), ("<=", .le), (">", .gt), (">=", .ge)]
    | 2 => [("+", .add), ("-", .sub)]
    | _ => [("*", .mul), ("/", .div), ("%", .mod)]
  let mut e ← binLevel (lvl + 1)
  repeat
    let t := (← peek).tok
    match ops.find? fun (s, _) => t == .sym s with
    | some (_, op) =>
      advance
      e := .binary op e (← binLevel (lvl + 1))
    | none => break
  pure e

partial def unary : P Expr := do
  if ← isSym "-" then advance; return .unary .neg (← unary)
  if ← isSym "!" then advance; return .unary .not (← unary)
  call

partial def call : P Expr := do
  let mut e ← primary
  while ← isSym "(" do
    advance
    let mut args : Array Expr := #[]
    unless ← isSym ")" do
      args := args.push (← expression)
      while ← matchSym "," do
        args := args.push (← expression)
    expectSym ")" "')' after arguments"
    e := .call e args.toList
  pure e

partial def primary : P Expr := do
  let t ← peek
  match t.tok with
  | .num n => advance; pure (.int (intLit n))
  | .str s => advance; pure (.str s)
  | .kw "true" => advance; pure (.bool true)
  | .kw "false" => advance; pure (.bool false)
  | .kw "null" => advance; pure .null
  | .ident x => advance; pure (.var x)
  | .sym "(" =>
    advance
    let e ← expression
    expectSym ")" "')' after expression"
    pure e
  | .kw "fn" => advance; fnRest none
  | tok => fail s!"unexpected {tok.describe} in expression"

partial def fnRest (name : Option String) : P Expr := do
  expectSym "(" "'(' after 'fn'"
  let mut params : Array String := #[]
  unless ← isSym ")" do
    params := params.push (← expectIdent "parameter name")
    while ← matchSym "," do
      params := params.push (← expectIdent "parameter name")
  expectSym ")" "')' after parameters"
  let body ← blockBody
  pure (.fn name params.toList body)

partial def blockBody : P (List Stmt) := do
  expectSym "{" "'{'"
  let mut ss : Array Stmt := #[]
  while !(← isSym "}") && (← peek).tok != .eof do
    ss := ss.push (← declaration)
  expectSym "}" "'}' after block"
  pure ss.toList

partial def varDecl : P Stmt := do
  advance
  let x ← expectIdent "variable name"
  let init ← if ← matchSym "=" then some <$> expression else pure none
  expectSym ";" "';' after variable declaration"
  pure (.varDecl x init)

partial def statement : P Stmt := do
  let t := (← peek).tok
  match t with
  | .sym "{" => .block <$> blockBody
  | .kw "if" =>
    advance
    expectSym "(" "'(' after 'if'"
    let c ← expression
    expectSym ")" "')' after if condition"
    let thn ← statement
    let els ← if (← isKw "else") then advance; some <$> statement else pure none
    pure (.ifStmt c thn els)
  | .kw "while" =>
    advance
    expectSym "(" "'(' after 'while'"
    let c ← expression
    expectSym ")" "')' after while condition"
    pure (.whileStmt c (← statement))
  | .kw "for" =>
    advance
    expectSym "(" "'(' after 'for'"
    let init ← if ← matchSym ";" then pure none
      else if ← isKw "var" then some <$> varDecl
      else do
        let e ← expression
        expectSym ";" "';' after for-loop initializer"
        pure (some (.expr e))
    let cnd ← if ← isSym ";" then pure none else some <$> expression
    expectSym ";" "';' after for-loop condition"
    let step ← if ← isSym ")" then pure none else some <$> expression
    expectSym ")" "')' after for-loop clauses"
    pure (.forStmt init cnd step (← statement))
  | .kw "return" =>
    advance
    let e ← if ← isSym ";" then pure none else some <$> expression
    expectSym ";" "';' after return value"
    pure (.ret e)
  | .kw "break" => advance; expectSym ";" "';' after 'break'"; pure .brk
  | .kw "continue" => advance; expectSym ";" "';' after 'continue'"; pure .cont
  | _ =>
    let e ← expression
    expectSym ";" "';' after expression"
    pure (.expr e)

partial def declaration : P Stmt := do
  if ← isKw "var" then return ← varDecl
  if (← isKw "fn") then
    if let .ident x ← peek2 then
      advance; advance
      return .varDecl x (some (← fnRest (some x)))
  statement

end

partial def program : P (List Stmt) := do
  let mut ss : Array Stmt := #[]
  while (← peek).tok != .eof do
    ss := ss.push (← declaration)
  pure ss.toList

def parse (src : String) : Except String Program := do
  let toks ← lex src.toList 1 #[]
  (program.run' 0).run toks

end Vsa.While.Parse
