/-
# Spec-side trace driver for the relational pilot (ANALYSIS ONLY)

`#eval` the WHILE spec semantics on the SAME `while.wl` program the machine-side
trace ran (`/tmp/wl-test/tests/while.wl`), dumping `(kindOfStmt s, store size,
depth)` at each executed statement.  Aligns by exec-event index with the
machine-side dispatch trace (`gen_trace.py` @ 0x80004014) so mining can pair
machine slot-word ↔ spec stmt-kind tag.

Nothing here enters a proof.  This is design-time mining input, the executable
mirror of the relation in `Vsa/While/Semantics.lean` restricted to the pilot's
statement subset (int/var/binary/assign/logical exprs; while/if/block/varDecl/
expr/brk/cont stmts) — enough to run `while.wl`.  It imports the REAL
`kindOfStmt` and `Stmt` so the emitted tags are the genuine spec tags, not a
re-encoding.

Run:  lake env lean experiments/spec_trace_brkcont.lean   (from repo root)
-/
import Vsa.While.Ast
import Vsa.Sim.ExecDispatch

open Vsa.While
open Vsa.Sim (kindOfStmt)

namespace SpecTrace

/-- Minimal runtime value for the pilot subset. -/
inductive V where
  | int (n : Int)
  | bool (b : Bool)
  | null
  deriving Repr, Inhabited

/-- A flat scope stack (list of frames); "store size" = number of frames ever
pushed, "depth" = current nesting (block/while frames), mirroring the machine
`exec_stmt` recursion depth we probe via sp. -/
abbrev Env := List (String × V)

def lookupV (env : Env) (x : String) : V :=
  (env.find? (·.1 == x)).map (·.2) |>.getD .null

def setV (env : Env) (x : String) (v : V) : Env :=
  if env.any (·.1 == x) then env.map (fun p => if p.1 == x then (x, v) else p)
  else (x, v) :: env

def truthy : V → Bool
  | .int n => n != 0
  | .bool b => b
  | .null => false

/-- Executable eval for the pilot expression subset. -/
partial def evalE (env : Env) : Expr → V
  | .int n => .int n
  | .bool b => .bool b
  | .null => .null
  | .var x => lookupV env x
  | .binary op l r =>
    match evalE env l, evalE env r with
    | .int a, .int b =>
      match op with
      | .add => .int (a + b) | .sub => .int (a - b) | .mul => .int (a * b)
      | .div => .int (if b == 0 then 0 else a / b)
      | .mod => .int (if b == 0 then 0 else a % b)
      | .eq => .bool (a == b) | .ne => .bool (a != b)
      | .lt => .bool (a < b) | .le => .bool (a <= b)
      | .gt => .bool (a > b) | .ge => .bool (a >= b)
    | _, _ => .null
  | .logical op l r =>
    match op with
    | .and => if truthy (evalE env l) then evalE env r else .bool false
    | .or  => if truthy (evalE env l) then .bool true else evalE env r
  | .unary op e =>
    match op, evalE env e with
    | .neg, .int n => .int (-n)
    | .not, v => .bool (!truthy v)
    | _, _ => .null
  | .assign _ e => evalE env e   -- assignment side effect handled at stmt level
  | _ => .null

/-- The exec trace: a mutable log of `(kindOfStmt, storeSize, depth)`. -/
structure TraceSt where
  env : Env
  frames : Nat        -- store size: total frames pushed (monotone)
  depth : Nat         -- current nesting depth
  log : List (Nat × Nat × Nat) := []
  deriving Inhabited

inductive Status where | normal | brk | cont deriving DecidableEq, Inhabited

/-- Emit one exec-event: the statement kind tag + geometry, BEFORE recursing
(mirrors probing at the `exec_stmt` dispatch entry). -/
def emit (t : TraceSt) (s : Stmt) : TraceSt :=
  { t with log := t.log ++ [(kindOfStmt s, t.frames, t.depth)] }

mutual
partial def execS (t : TraceSt) (s : Stmt) : TraceSt × Status :=
  let t := emit t s
  match s with
  | .expr (.assign x e) =>
      ({ t with env := setV t.env x (evalE t.env e) }, .normal)
  | .expr _ => (t, .normal)
  | .varDecl x init =>
      let v := (init.map (evalE t.env)).getD .null
      ({ t with env := setV t.env x v }, .normal)
  | .brk => (t, .brk)
  | .cont => (t, .cont)
  | .block ss =>
      -- a block pushes a frame (env_new): store grows, depth +1
      let t0 := { t with frames := t.frames + 1, depth := t.depth + 1 }
      let (t1, st) := execList t0 ss
      ({ t1 with depth := t.depth }, st)
  | .ifStmt c thn els =>
      if truthy (evalE t.env c) then execS t thn
      else match els with | some e => execS t e | none => (t, .normal)
  | .whileStmt c body =>
      execWhile t c body 100000
  | _ => (t, .normal)

partial def execList (t : TraceSt) : List Stmt → TraceSt × Status
  | [] => (t, .normal)
  | s :: rest =>
      let (t1, st) := execS t s
      if st == .normal then execList t1 rest else (t1, st)

partial def execWhile (t : TraceSt) (c : Expr) (body : Stmt) : Nat → TraceSt × Status
  | 0 => (t, .normal)
  | fuel + 1 =>
      if truthy (evalE t.env c) then
        let (t1, st) := execS t body
        match st with
        | .brk => (t1, .normal)
        | _ => execWhile t1 c body fuel   -- .cont and .normal both re-loop
      else (t, .normal)
end

/-- The `while (true) { n=n+1; if(n>100) break; if(n%2==0) continue; total=total+n }`
loop from `while.wl` (the brk/cont-bearing loop), transcribed to the real AST. -/
def brkContLoop : Stmt :=
  .whileStmt (.bool true) (.block [
    .expr (.assign "n" (.binary .add (.var "n") (.int 1))),
    .ifStmt (.binary .gt (.var "n") (.int 100)) .brk none,
    .ifStmt (.binary .eq (.binary .mod (.var "n") (.int 2)) (.int 0)) .cont none,
    .expr (.assign "total" (.binary .add (.var "total") (.var "n")))
  ])

def prog : Program := [
  .varDecl "n" (some (.int 0)),
  .varDecl "total" (some (.int 0)),
  brkContLoop
]

def run : TraceSt :=
  (execList { env := [], frames := 0, depth := 0 } prog).1

/-- Dump the exec-event trace as `SPEC kind=.. frames=.. depth=..` lines,
alignable to the machine dispatch trace by index. -/
def dump : String :=
  String.join (run.log.map (fun (k, f, d) =>
    s!"SPEC kind={k} frames={f} depth={d}\n"))

#eval IO.print dump

/-- Summary: histogram of stmt-kind tags in the spec exec trace. -/
def kindHist : List (Nat × Nat) :=
  let ks := run.log.map (·.1)
  (ks.foldl (fun m k => (m.filter (·.1 != k)) ++ [(k, (m.find? (·.1 == k)).map (·.2 + 1) |>.getD 1)]) [])
    |>.mergeSort (·.1 < ·.1)

#eval IO.println s!"SPEC-KIND-HIST {kindHist}"
#eval IO.println s!"SPEC brk(7) count = {run.log.filter (·.1 == 7) |>.length}"
#eval IO.println s!"SPEC cont(8) count = {run.log.filter (·.1 == 8) |>.length}"

end SpecTrace
