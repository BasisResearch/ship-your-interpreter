import Vsa.While.Ast

/-!
# Big-step operational semantics for WHILE

An inductive big-step semantics mirroring the C evaluator (`c/src/interp.c`,
`value.c`, `env.c`) of the binary. Environments are mutable and shared by
closures in C, so the semantics is store-based: a heap of frames (scopes)
addressed by `Nat`, each with a parent pointer, plus a heap of closures.

Abstractions relative to the binary (deliberate — the big-step semantics is
the *ideal* language; the refinement theorem is what ties it back):
* runtime errors have no derivations (the binary prints a message to the
  console and exits nonzero; derivations only exist for successful runs).

Integers are `Int`, but every arithmetic *result* is wrapped to the 64-bit
two's-complement range by `wrap64` (2026-08-25 user-approved amendment): the
compiled interpreter computes on C `long long`, so `+`/`-`/`*`/unary `-`
wrap natively on RV64 and `/`/`%` go through libgcc's soft division, which
wraps too (`INT64_MIN / -1 = INT64_MIN`, remainder `0`). The M4 pilot found
the unwrapped `EvalE.neg` unsatisfiable against the machine at `n = -2^63`
(`experiments/pctrace.md`); `wrap64_neg_min` below is that exact instance.

The call-depth cap, on the other hand, is mirrored *exactly*: a depth counter
`d` (the number of active nested closure calls) is threaded through every
relation, and `Call.closure` succeeds only when `d < maxCallDepth`, running
its body at depth `d + 1` (see `maxCallDepth` and `interp.c`'s `call_value`).

Constructor arguments are explicit (rather than auto-bound implicits) so
that derivation trees can be constructed directly, term by term, by the
syntax-directed tactic in `Derive.lean`.
-/

namespace Vsa.While

/-- Address of a frame (scope) in the store. -/
abbrev Addr := Nat

/-- The three built-in functions (`interp_init`). -/
inductive NativeFn where
  | print | println | assert
  deriving Repr, DecidableEq

/-- Runtime values (`c/src/value.h`). Closures point into the store so that
two closures over the same environment share mutations. -/
inductive Value where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | closure (a : Addr)
  | native (f : NativeFn)
  deriving Repr, DecidableEq

/-- Heap-allocated closure data (`Closure` in interp.h + the `EX_FN` node). -/
structure ClosureData where
  env : Addr
  name : Option String
  params : List String
  body : List Stmt
  deriving Repr

/-- One scope (`Env` in env.h): parent pointer + bindings. -/
structure Frame where
  parent : Option Addr
  vars : List (String × Value)
  deriving Repr

/-- The store: all frames and closures ever allocated (C never frees). -/
structure Store where
  frames : Array Frame
  closures : Array ClosureData
  deriving Repr

/-- Program state threaded through the semantics: the store plus everything
printed so far (the observable behavior). -/
structure St where
  store : Store
  out : String
  deriving Repr

/-- Result of executing a statement (`ExecStatus` in interp.c). -/
inductive Status where
  | normal | brk | cont | ret (v : Value)
  deriving Repr, DecidableEq

namespace Store

/-- Allocate a new frame, returning its address (`env_new`). -/
def allocFrame (s : Store) (parent : Option Addr) : Store × Addr :=
  ({ s with frames := s.frames.push ⟨parent, []⟩ }, s.frames.size)

/-- Allocate a closure (`EX_FN` evaluation). -/
def allocClosure (s : Store) (c : ClosureData) : Store × Addr :=
  ({ s with closures := s.closures.push c }, s.closures.size)

/-- `env_define`: bind in *this* frame, overwriting an existing binding. -/
def define (s : Store) (a : Addr) (x : String) (v : Value) : Store :=
  { s with
    frames := s.frames.modify a fun f =>
      { f with vars :=
          if f.vars.any (·.1 == x) then
            f.vars.map fun p => if p.1 == x then (x, v) else p
          else
            f.vars ++ [(x, v)] } }

/-- `env_get`: look up through the parent chain. `gas` bounds the chain walk
(frame parents always point to earlier frames, but keeping the function
total by construction is simpler than carrying that invariant). -/
def lookup (s : Store) : (gas : Nat) → Addr → String → Option Value
  | 0, _, _ => none
  | gas + 1, a, x => do
    let f ← s.frames[a]?
    match f.vars.find? (·.1 == x) with
    | some (_, v) => some v
    | none => match f.parent with
      | some p => s.lookup gas p x
      | none => none

/-- `env_set`: assign through the parent chain; `none` if unbound. -/
def set (s : Store) : (gas : Nat) → Addr → String → Value → Option Store
  | 0, _, _, _ => none
  | gas + 1, a, x, v => do
    let f ← s.frames[a]?
    if f.vars.any (·.1 == x) then
      some { s with
        frames := s.frames.modify a fun f =>
          { f with vars := f.vars.map fun p => if p.1 == x then (x, v) else p } }
    else match f.parent with
      | some p => s.set gas p x v
      | none => none

end Store

/-- `env_get` with the chain-walk gas set to the number of frames (a parent
chain can never be longer than the store). -/
def Store.get? (s : Store) (a : Addr) (x : String) : Option Value :=
  s.lookup s.frames.size a x

/-- `env_set` with maximal gas. -/
def Store.set? (s : Store) (a : Addr) (x : String) (v : Value) : Option Store :=
  s.set s.frames.size a x v

/-- `value_truthy`: `null`, `false` and `0` are falsy. -/
def Value.truthy : Value → Bool
  | .null => false
  | .bool b => b
  | .int n => n != 0
  | _ => true

/-- `value_equal`: same-kind comparison; closures by identity. -/
def Value.equal : Value → Value → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .str a, .str b => a == b
  | .closure a, .closure b => a == b
  | .native a, .native b => a == b
  | _, _ => false

/-- Decimal digits of a natural number, by structural fuel recursion (fuel
`n + 1` always suffices since the digit count is at most `n + 1`). `Nat.repr`
itself is avoided because `Int.repr` routes through the opaque
`String.Internal.append`, which kernel reduction cannot evaluate; this
definition reduces all the way for literal inputs. -/
def natDigits : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n =>
    if n < 10 then [Nat.digitChar n]
    else natDigits fuel (n / 10) ++ [Nat.digitChar (n % 10)]

/-- Decimal rendering of a natural number (agrees with `Nat.repr`). -/
def natToString (n : Nat) : String := (natDigits (n + 1) n).foldl .push ""

/-- Decimal rendering of an integer — C's `%lld` formatting (agrees with
`Int.repr`/`toString`, but reduces by kernel computation). -/
def intToString : Int → String
  | .ofNat m => natToString m
  | .negSucc m => "-" ++ natToString (m + 1)

/-- `value_print` / `stringify`: how values render on the console. Closure
display needs the store (for the function name). -/
def Value.display (s : Store) : Value → String
  | .null => "null"
  | .bool b => if b then "true" else "false"
  | .int n => intToString n
  | .str s0 => s0
  | .closure a =>
    match s.closures[a]? with
    | some c => match c.name with
      | some n => s!"<fn {n}>"
      | none => "<fn>"
    | none => "<fn>"
  | .native .print => "<native fn print>"
  | .native .println => "<native fn println>"
  | .native .assert => "<native fn assert>"

/-- `native_print`: arguments separated by single spaces. -/
def printArgs (s : Store) (args : List Value) : String :=
  String.intercalate " " (args.map (Value.display s))

/-! ## 64-bit wrapping arithmetic

The interpreter computes on C `long long` (RV64): `+`/`-`/`*` and unary `-`
are native two's-complement instructions, and `/`/`%` are libgcc's soft
division, which wraps the one overflowing case (`INT64_MIN / -1 = INT64_MIN`,
remainder `0`). Every arithmetic *result* below is therefore wrapped by
`wrap64`. Comparisons and equality need no wrapping: they compare stored
values, and stored values are in range by construction — arithmetic results
are wrapped here, and int literals arrive from the machine-resident AST
through `readI64` (`Vsa/MemRepr.lean`), i.e. as `(BitVec.ofNat 64 _).toInt`,
which is in `[-2^63, 2^63)` like any `BitVec.toInt`. -/

/-- Wrap an integer to the 64-bit two's-complement range `[-2^63, 2^63)`:
the canonical round trip through the machine representation (`BitVec 64`). -/
def wrap64 (z : Int) : Int := (BitVec.ofInt 64 z).toInt

/-- `wrap64` is the identity on in-range integers. -/
theorem wrap64_eq_self {z : Int} (h : -2^63 ≤ z ∧ z < 2^63) : wrap64 z = z :=
  BitVec.toInt_ofInt_eq_self (by decide) h.1 h.2

/-- `wrap64` always lands in the 64-bit range. -/
theorem wrap64_range (z : Int) : -2^63 ≤ wrap64 z ∧ wrap64 z < 2^63 :=
  ⟨BitVec.le_toInt _, BitVec.toInt_lt⟩

/-- Wrapping is idempotent. -/
theorem wrap64_idem (z : Int) : wrap64 (wrap64 z) = wrap64 z := by
  unfold wrap64; rw [BitVec.ofInt_toInt]

/-- `wrap64` fixes anything read out of a 64-bit machine word — the
Sim-side workhorse (machine values are `BitVec 64`, read as `toInt`). -/
theorem wrap64_toInt (v : BitVec 64) : wrap64 v.toInt = v.toInt := by
  unfold wrap64; rw [BitVec.ofInt_toInt]

/-- Pushing a wrapped integer back into the machine representation is
invisible — the other Sim-side workhorse. -/
theorem ofInt_wrap64 (z : Int) : BitVec.ofInt 64 (wrap64 z) = BitVec.ofInt 64 z :=
  BitVec.ofInt_toInt

/-- **The M4 pilot's overflow gap, closed.** The pilot found `EvalE.neg`
with unbounded `Int` unsatisfiable against the machine at `n = -2^63`
(`neg a1,a1` wraps: `-INT64_MIN = INT64_MIN`; see `experiments/pctrace.md`
and `memory/m4-recursive-cases.md`). With wrapping this is exactly what the
rule now derives. -/
theorem wrap64_neg_min : wrap64 (-(-2^63 : Int)) = -2^63 := by decide

/-- libgcc's soft-division overflow case falls out of `wrap64` around the
true (toward-zero) quotient: `INT64_MIN / -1` wraps to `INT64_MIN`. -/
theorem wrap64_tdiv_min : wrap64 ((-2^63 : Int).tdiv (-1)) = -2^63 := by decide

/-- …and the corresponding remainder is `0`. -/
theorem wrap64_tmod_min : wrap64 ((-2^63 : Int).tmod (-1)) = 0 := by decide

/-- Semantics of the arithmetic/comparison operators (`eval_binary`).
`none` means runtime error. Division truncates toward zero like C
(`Int.tdiv`/`Int.tmod`), and every arithmetic result wraps at 64 bits
(`wrap64`), exactly as the compiled `long long` arithmetic does. -/
def binOpSem (s : Store) : BinOp → Value → Value → Option Value
  | .add, l, r =>
    match l, r with
    | .str _, _ | _, .str _ => some (.str (l.display s ++ r.display s))
    | .int a, .int b => some (.int (wrap64 (a + b)))
    | _, _ => none
  | .sub, .int a, .int b => some (.int (wrap64 (a - b)))
  | .mul, .int a, .int b => some (.int (wrap64 (a * b)))
  | .div, .int a, .int b => if b == 0 then none else some (.int (wrap64 (a.tdiv b)))
  | .mod, .int a, .int b => if b == 0 then none else some (.int (wrap64 (a.tmod b)))
  | .eq, l, r => some (.bool (l.equal r))
  | .ne, l, r => some (.bool (!(l.equal r)))
  | .lt, .str a, .str b => some (.bool (a < b))
  | .le, .str a, .str b => some (.bool (a < b || a == b))
  | .gt, .str a, .str b => some (.bool (b < a))
  | .ge, .str a, .str b => some (.bool (b < a || a == b))
  | .lt, .int a, .int b => some (.bool (a < b))
  | .le, .int a, .int b => some (.bool (a ≤ b))
  | .gt, .int a, .int b => some (.bool (a > b))
  | .ge, .int a, .int b => some (.bool (a ≥ b))
  | _, _, _ => none

/-- The maximum number of active nested closure calls (`MAX_CALL_DEPTH` in
`c/src/interp.c`). A closure call at active depth `d` succeeds only when
`d < maxCallDepth` (mirroring `if (++call_depth > MAX_CALL_DEPTH) error`),
and runs its body at depth `d + 1`. -/
def maxCallDepth : Nat := 1000

mutual

/-- Big-step evaluation of expressions: `EvalE st d env e st' v` means that in
state `st`, at call depth `d`, with current scope `env`, expression `e`
evaluates to `v`, producing state `st'` (`eval_expr`). The depth `d` is
carried unchanged through every rule; only `Call.closure` consults and
increments it. -/
inductive EvalE : St → Nat → Addr → Expr → St → Value → Prop where
  | int (st : St) (d : Nat) (env : Addr) (n : Int) :
    EvalE st d env (.int n) st (.int n)
  | str (st : St) (d : Nat) (env : Addr) (s : String) :
    EvalE st d env (.str s) st (.str s)
  | bool (st : St) (d : Nat) (env : Addr) (b : Bool) :
    EvalE st d env (.bool b) st (.bool b)
  | null (st : St) (d : Nat) (env : Addr) :
    EvalE st d env .null st .null
  | var (st : St) (d : Nat) (env : Addr) (x : String) (v : Value) :
    st.store.get? env x = some v →
    EvalE st d env (.var x) st v
  | assign (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St)
      (v : Value) (store'' : Store) :
    EvalE st d env e st' v →
    st'.store.set? env x v = some store'' →
    EvalE st d env (.assign x e) ⟨store'', st'.out⟩ v
  | binary (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : St) (lv rv v : Value) :
    EvalE st d env l st' lv →
    EvalE st' d env r st'' rv →
    binOpSem st''.store op lv rv = some v →
    EvalE st d env (.binary op l r) st'' v
  | orTrue (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) :
    EvalE st d env l st' lv → lv.truthy = true →
    EvalE st d env (.logical .or l r) st' (.bool true)
  | orFalse (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St)
      (lv rv : Value) :
    EvalE st d env l st' lv → lv.truthy = false →
    EvalE st' d env r st'' rv →
    EvalE st d env (.logical .or l r) st'' (.bool rv.truthy)
  | andFalse (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) :
    EvalE st d env l st' lv → lv.truthy = false →
    EvalE st d env (.logical .and l r) st' (.bool false)
  | andTrue (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St)
      (lv rv : Value) :
    EvalE st d env l st' lv → lv.truthy = true →
    EvalE st' d env r st'' rv →
    EvalE st d env (.logical .and l r) st'' (.bool rv.truthy)
  | neg (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (n : Int) :
    EvalE st d env e st' (.int n) →
    EvalE st d env (.unary .neg e) st' (.int (wrap64 (-n)))
  | not (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) :
    EvalE st d env e st' v →
    EvalE st d env (.unary .not e) st' (.bool (!v.truthy))
  | call (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' st''' : St) (fv : Value) (vs : List Value) (v : Value) :
    EvalE st d env f st' fv →
    EvalArgs st' d env args st'' vs →
    Call st'' d fv vs st''' v →
    EvalE st d env (.call f args) st''' v
  | fn (st : St) (d : Nat) (env : Addr) (name : Option String)
      (params : List String) (body : List Stmt) (store' : Store) (a : Addr) :
    st.store.allocClosure ⟨env, name, params, body⟩ = (store', a) →
    EvalE st d env (.fn name params body) ⟨store', st.out⟩ (.closure a)

/-- Left-to-right evaluation of argument lists. -/
inductive EvalArgs : St → Nat → Addr → List Expr → St → List Value → Prop where
  | nil (st : St) (d : Nat) (env : Addr) : EvalArgs st d env [] st []
  | cons (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' st'' : St) (v : Value) (vs : List Value) :
    EvalE st d env e st' v →
    EvalArgs st' d env es st'' vs →
    EvalArgs st d env (e :: es) st'' (v :: vs)

/-- Calling a value (`call_value`). Closures run their body in a fresh frame
whose parent is the closure's captured environment; a body finishing
normally returns `null`, `return v` returns `v` (`brk`/`cont` escaping is a
runtime error, hence underivable). The active call depth `d` is the number of
enclosing closure calls: a closure call succeeds only when `d < maxCallDepth`
(mirroring `if (++call_depth > MAX_CALL_DEPTH) error`), and runs its body at
`d + 1`. The natives carry `d` but neither guard nor increment it. -/
inductive Call : St → Nat → Value → List Value → St → Value → Prop where
  | closure (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : St) (status : Status)
      (v : Value) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st.out⟩ (d + 1) frame cd.body st' status →
    (status = .normal ∧ v = .null ∨ status = .ret v) →
    Call st d (.closure a) vs st' v
  | print (st : St) (d : Nat) (vs : List Value) :
    Call st d (.native .print) vs
      ⟨st.store, st.out ++ printArgs st.store vs⟩ .null
  | println (st : St) (d : Nat) (vs : List Value) :
    Call st d (.native .println) vs
      ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null
  | assertOk (st : St) (d : Nat) (vs : List Value) (v m : Value) :
    (vs = [v] ∨ vs = [v, m]) →
    v.truthy = true →
    Call st d (.native .assert) vs st .null

/-- Big-step execution of a statement (`exec_stmt`). -/
inductive ExecS : St → Nat → Addr → Stmt → St → Status → Prop where
  | expr (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) :
    EvalE st d env e st' v →
    ExecS st d env (.expr e) st' .normal
  | varInit (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St)
      (v : Value) :
    EvalE st d env e st' v →
    ExecS st d env (.varDecl x (some e))
      ⟨st'.store.define env x v, st'.out⟩ .normal
  | varNull (st : St) (d : Nat) (env : Addr) (x : String) :
    ExecS st d env (.varDecl x none)
      ⟨st.store.define env x .null, st.out⟩ .normal
  | block (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr) (st' : St) (status : Status) :
    st.store.allocFrame (some env) = (store', inner) →
    ExecSeq ⟨store', st.out⟩ d inner ss st' status →
    ExecS st d env (.block ss) st' status
  | ifTrue (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) (st' st'' : St) (v : Value) (status : Status) :
    EvalE st d env c st' v → v.truthy = true →
    ExecS st' d env t st'' status →
    ExecS st d env (.ifStmt c t e) st'' status
  | ifFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
      (st' st'' : St) (v : Value) (status : Status) :
    EvalE st d env c st' v → v.truthy = false →
    ExecS st' d env e st'' status →
    ExecS st d env (.ifStmt c t (some e)) st'' status
  | ifNone (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : St)
      (v : Value) :
    EvalE st d env c st' v → v.truthy = false →
    ExecS st d env (.ifStmt c t none) st' .normal
  | whileFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = false →
    ExecS st d env (.whileStmt c b) st' .normal
  | whileBreak (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = true →
    ExecS st' d env b st'' .brk →
    ExecS st d env (.whileStmt c b) st'' .normal
  | whileRet (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v rv : Value) :
    EvalE st d env c st' v → v.truthy = true →
    ExecS st' d env b st'' (.ret rv) →
    ExecS st d env (.whileStmt c b) st'' (.ret rv)
  | whileLoop (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' st''' : St) (v : Value) (status status' : Status) :
    EvalE st d env c st' v → v.truthy = true →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    ExecS st'' d env (.whileStmt c b) st''' status' →
    ExecS st d env (.whileStmt c b) st''' status'
  | forStart (st : St) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' st'' : St) (status : Status) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecInit ⟨store', st.out⟩ d outer init st' →
    ForLoop st' d outer cnd step b st'' status →
    ExecS st d env (.forStmt init cnd step b) st'' status
  | ret (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) :
    EvalE st d env e st' v →
    ExecS st d env (.ret (some e)) st' (.ret v)
  | retNull (st : St) (d : Nat) (env : Addr) :
    ExecS st d env (.ret none) st (.ret .null)
  | brk (st : St) (d : Nat) (env : Addr) : ExecS st d env .brk st .brk
  | cont (st : St) (d : Nat) (env : Addr) : ExecS st d env .cont st .cont

/-- The optional `for` initializer, run in the loop's outer frame. -/
inductive ExecInit : St → Nat → Addr → Option Stmt → St → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ExecInit st d env none st
  | some (st : St) (d : Nat) (env : Addr) (s : Stmt) (st' : St) :
    ExecS st d env s st' .normal →
    ExecInit st d env (some s) st'

/-- The `for` loop proper (cond → body → step → repeat). A missing
condition is truthy. -/
inductive ForLoop : St → Nat → Addr → Option Expr → Option Expr → Stmt → St →
    Status → Prop where
  | condFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr)
      (b : Stmt) (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = false →
    ForLoop st d env (some c) step b st' .normal
  | bodyBreak (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' : St) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' .brk →
    ForLoop st d env cnd step b st'' .normal
  | bodyRet (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' : St) (rv : Value) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' (.ret rv) →
    ForLoop st d env cnd step b st'' (.ret rv)
  | loop (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : St)
      (status status' : Status) :
    ForCond st d env cnd st' →
    ExecS st' d env b st'' status →
    (status = .normal ∨ status = .cont) →
    ExecStep st'' d env step st''' →
    ForLoop st''' d env cnd step b st'''' status' →
    ForLoop st d env cnd step b st'''' status'

/-- A `for` condition that passed (or was absent). -/
inductive ForCond : St → Nat → Addr → Option Expr → St → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ForCond st d env none st
  | some (st : St) (d : Nat) (env : Addr) (c : Expr) (st' : St) (v : Value) :
    EvalE st d env c st' v → v.truthy = true →
    ForCond st d env (some c) st'

/-- The optional `for` step expression. -/
inductive ExecStep : St → Nat → Addr → Option Expr → St → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ExecStep st d env none st
  | some (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value) :
    EvalE st d env e st' v →
    ExecStep st d env (some e) st'

/-- Statement sequences: stop at the first non-`normal` status. -/
inductive ExecSeq : St → Nat → Addr → List Stmt → St → Status → Prop where
  | nil (st : St) (d : Nat) (env : Addr) : ExecSeq st d env [] st .normal
  | consNormal (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' st'' : St) (status : Status) :
    ExecS st d env s st' .normal →
    ExecSeq st' d env ss st'' status →
    ExecSeq st d env (s :: ss) st'' status
  | consAbrupt (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : St) (status : Status) :
    ExecS st d env s st' status →
    status ≠ .normal →
    ExecSeq st d env (s :: ss) st' status

end

/-- The initial state: one global frame with the three natives bound
(`interp_init`). The globals frame has address 0. -/
def initSt : St :=
  { store :=
      { frames := #[⟨none, [("print", .native .print), ("println", .native .println),
          ("assert", .native .assert)]⟩]
        closures := #[] }
    out := "" }

/-- **The specification.** `BigStep p out` holds iff the WHILE program `p`
runs to completion in the global scope (as `interp_run` does in script mode)
printing exactly `out`. -/
def BigStep (p : Program) (out : String) : Prop :=
  ∃ st', ExecSeq initSt 0 0 p st' .normal ∧ st'.out = out

end Vsa.While
