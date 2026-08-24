import Vsa.While.Semantics

/-!
# Allocation-cost companion relations for the WHILE semantics

This file is a **conservative extension** of `Vsa/While/Semantics.lean`:
nothing in that file is changed or re-stated in a way that could weaken it.
We add, for each of the nine big-step relations, a *cost companion* relation
that carries one extra `Nat` output — an upper bound on the number of bytes
the C evaluator (`c/src/interp.c`, `env.c`, `value.c`) requests from `malloc`
while producing the very same derivation. The companions mirror the semantics
constructor-for-constructor; each constructor's cost is *its own* allocation
bytes plus the sum of its sub-derivations' costs.

The point is to demonstrate that the big-step semantics is rich enough to
*bound a program's machine-allocation budget ahead of time* from its
derivation. This budget feeds the M4/M6 arena-budget hypothesis
(`Vsa/Alloc.lean`'s `MallocContract`, whose `maxReq`/arena bounds it is meant
to discharge): if `BigStepBudget p out n` holds then `n` bytes of arena
suffice.

## Cost unit and the alignment convention

The unit is **bytes requested per `malloc` call**, and *every* per-`malloc`
charge is rounded up to a multiple of 16 (`roundUp16`). The allocator
(`MallocContract`) hands back 16-aligned blocks, so an aligned allocator
consumes at least the requested size rounded to its granule; charging the
rounded size here makes the cost an *over*-approximation of what any
16-granule allocator actually consumes for the same request sequence. (Both
`envBytes = 32` and `closureBytes = 16` are already multiples of 16, so the
rounding is the identity there; it only bites on the variable-length string
and array charges.) The consumer therefore need not re-round.

## C allocation sites mirrored (runtime only — lexer/parser out of scope)

| site | C location | bytes requested |
|------|------------|-----------------|
| new frame (`env_new`) | `env.c:12-20`, called `interp.c:194,287,309` | `sizeof(Env) = 32` |
| closure (`EX_FN`) | `interp.c:258-266` | `sizeof(Closure) = 16` |
| binding name copy | `env.c:35` (`xmalloc(strlen(name)+1)`) | `len(name)+1` |
| binding array growth | `env.c:29-33` (realloc names+vals at `count==cap`) | `32 * newcap` (`8*cap` names + `24*cap` vals) |
| string concat result | `interp.c:118` | `la+lb+1` |
| `stringify` operand | `interp.c:84-106` | `len(displayed)+1` |

The growth policy (`env.c:29-33`): a frame starts `cap = 0`; on the define
that would overflow, `cap := cap ? 2*cap : 8`, giving the cap sequence
`8, 16, 32, 64, …`. The realloc requests `8*cap` (names, `char*`) + `24*cap`
(vals, `Value`) = `32*cap` bytes; the *old* arrays are leaked (no `free`),
so the cumulative array cost of a frame that reaches `k` bindings is the sum
of `32*cap` over every cap it ever grew to (`arrayCost` below).

## Spec-invisible / data-dependent allocations — findings

* **String literals (`EX_STR`, `interp.c:214`)**: `value_str(e->as.str_val)`
  takes ownership of the *parser-owned* AST string; there is **no runtime
  `malloc`**. Correctly charged 0.
* **`stringify` of an already-`VAL_STR` operand** still `malloc`s a copy
  (`interp.c:85-89`); charged.
* Every runtime allocation whose size the C computes is a function of
  spec-visible data (the value being stringified via `Value.display`, the
  binding name, the frame's current binding count). **No spec-invisible
  allocation cost was found**: the cost model is exact-up-to-alignment, not a
  blind over-approximation.
* The globals frame and its three native bindings are built by `interp_init`
  *before* `interp_run`; they are the pre-built `initSt` store, not produced
  by any `allocFrame`/`define` in a derivation. Their bytes are the "initial
  store contribution" of the store bound below, kept separate from the
  derivation cost `n`.
-/

namespace Vsa.While

/-! ## Cost-model constants and closed-form charges -/

/-- Round a byte request up to the allocator's 16-byte granule. -/
def roundUp16 (n : Nat) : Nat := (n + 15) / 16 * 16

/-- `sizeof(Env)` (`env.c` `env_new`): one frame allocation. -/
def envBytes : Nat := 32

/-- `sizeof(Closure)` (`interp.c` `EX_FN`): one closure allocation. -/
def closureBytes : Nat := 16

/-- Bytes for the name copy of a fresh binding (`env.c:35`,
`xmalloc(strlen(name)+1)`), rounded to the granule. -/
def nameCopyCost (x : String) : Nat := roundUp16 (x.length + 1)

/-- The array-realloc charge for growing a frame to capacity `cap`
(`env.c:31-32`): `8*cap` (names) + `24*cap` (vals), rounded. -/
def arrayReallocCost (cap : Nat) : Nat := roundUp16 (32 * cap)

/-- Cumulative names+vals array bytes for a frame that reaches `k` bindings.
The frame grows through caps `8, 16, 32, …`; each growth to cap `c` leaks the
old arrays and requests `32*c` bytes. `arrayCost k` sums those requests over
exactly the caps a `k`-binding frame passes through.

Implemented by fuel recursion over the cap it is currently at: starting from
`cap = 0`, as long as the target `k` exceeds the current `cap` we pay for the
next cap (`8` if `cap = 0`, else `2*cap`) and recurse. Fuel `k` always
suffices since each step at least reaches the next power-of-two multiple. -/
def arrayCostAux : (fuel cap k : Nat) → Nat
  | 0, _, _ => 0
  | fuel + 1, cap, k =>
    if k ≤ cap then 0
    else
      let cap' := if cap = 0 then 8 else 2 * cap
      arrayReallocCost cap' + arrayCostAux fuel cap' k

/-- Cumulative array-allocation bytes for a frame reaching `k` bindings. -/
def arrayCost (k : Nat) : Nat := arrayCostAux k 0 k

/-- Marginal binding cost of `define`-ing `x` in frame `a` of `store`
(`env_define`, `env.c:22-40`): if `x` is already bound the C returns early
with no allocation (`0`); otherwise it copies the name, and — when the
current binding count sits on a cap boundary — reallocs the arrays. The
current count is read from the (spec-visible) frame; a missing frame yields
`0` (the corresponding semantics rule cannot fire anyway). -/
def defineCost (store : Store) (a : Addr) (x : String) : Nat :=
  match store.frames[a]? with
  | none => 0
  | some f =>
    if f.vars.any (·.1 == x) then 0
    else
      let c := f.vars.length
      let growth :=
        -- realloc iff count == cap, i.e. c ∈ {0, 8, 16, 32, …}
        if c = 0 then arrayReallocCost 8
        else if arrayCostAux (c + 1) 0 (c + 1) ≠ arrayCostAux c 0 c then
          -- reached a new cap: charge the difference (the new realloc)
          arrayCostAux (c + 1) 0 (c + 1) - arrayCostAux c 0 c
        else 0
      nameCopyCost x + growth

/-- Bytes `stringify` requests for value `v` (`interp.c:84-106`): a copy of
its displayed form (`Value.display`), rounded. Covers both the `VAL_STR`
branch (copy the string) and the formatted branch. -/
def stringifyCost (store : Store) (v : Value) : Nat :=
  roundUp16 ((v.display store).length + 1)

/-- Bytes a string `+` requests (`interp.c:117-123`): `stringify` of each
operand plus the concatenation buffer (`la+lb+1`). -/
def concatCost (store : Store) (lv rv : Value) : Nat :=
  stringifyCost store lv + stringifyCost store rv +
    roundUp16 ((lv.display store).length + (rv.display store).length + 1)

/-- Allocation charge of a single `binOpSem` evaluation on `interp.c`'s
`eval_binary`: only string `+` allocates; every other operator is arithmetic
or boolean and requests nothing. Mirrors `binOpSem`'s `add` string case. -/
def binOpCost (store : Store) (op : BinOp) (lv rv : Value) : Nat :=
  match op, lv, rv with
  | .add, .str _, _ => concatCost store lv rv
  | .add, _, .str _ => concatCost store lv rv
  | _, _, _ => 0

/-- The cumulative parameter-binding cost of a closure call: fold `defineCost`
across the `params.zip vs` list exactly as `Call.closure` folds `define`,
threading the growing store so each `defineCost` sees the frame count the C
would. -/
def bindParamsCost : Store → Addr → List (String × Value) → Nat
  | _, _, [] => 0
  | store, frame, (x, v) :: rest =>
    defineCost store frame x + bindParamsCost (store.define frame x v) frame rest

/-! ## The companion cost relations

Mirrors the nine mutual relations of `Semantics.lean` one-to-one. Each
carries a trailing `Nat` cost; premises reuse the *same* semantic sub-costs,
and the head cost is the site charge plus the sub-costs. Binder style follows
the semantics exactly (explicit constructor arguments). -/

mutual

/-- Cost companion of `EvalE`. -/
inductive EvalECost : St → Nat → Addr → Expr → St → Value → Nat → Prop where
  | int (st : St) (d : Nat) (env : Addr) (n : Int) :
    EvalECost st d env (.int n) st (.int n) 0
  | str (st : St) (d : Nat) (env : Addr) (s : String) :
    EvalECost st d env (.str s) st (.str s) 0
  | bool (st : St) (d : Nat) (env : Addr) (b : Bool) :
    EvalECost st d env (.bool b) st (.bool b) 0
  | null (st : St) (d : Nat) (env : Addr) :
    EvalECost st d env .null st .null 0
  | var (st : St) (d : Nat) (env : Addr) (x : String) (v : Value) :
    st.store.get? env x = some v →
    EvalECost st d env (.var x) st v 0
  | assign (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St)
      (v : Value) (store'' : Store) (n : Nat) :
    EvalECost st d env e st' v n →
    st'.store.set? env x v = some store'' →
    EvalECost st d env (.assign x e) ⟨store'', st'.out⟩ v n
  | binary (st : St) (d : Nat) (env : Addr) (op : BinOp) (l r : Expr)
      (st' st'' : St) (lv rv v : Value) (nl nr : Nat) :
    EvalECost st d env l st' lv nl →
    EvalECost st' d env r st'' rv nr →
    binOpSem st''.store op lv rv = some v →
    EvalECost st d env (.binary op l r) st'' v (nl + nr + binOpCost st''.store op lv rv)
  | orTrue (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) (n : Nat) :
    EvalECost st d env l st' lv n → lv.truthy = true →
    EvalECost st d env (.logical .or l r) st' (.bool true) n
  | orFalse (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St)
      (lv rv : Value) (nl nr : Nat) :
    EvalECost st d env l st' lv nl → lv.truthy = false →
    EvalECost st' d env r st'' rv nr →
    EvalECost st d env (.logical .or l r) st'' (.bool rv.truthy) (nl + nr)
  | andFalse (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' : St)
      (lv : Value) (n : Nat) :
    EvalECost st d env l st' lv n → lv.truthy = false →
    EvalECost st d env (.logical .and l r) st' (.bool false) n
  | andTrue (st : St) (d : Nat) (env : Addr) (l r : Expr) (st' st'' : St)
      (lv rv : Value) (nl nr : Nat) :
    EvalECost st d env l st' lv nl → lv.truthy = true →
    EvalECost st' d env r st'' rv nr →
    EvalECost st d env (.logical .and l r) st'' (.bool rv.truthy) (nl + nr)
  | neg (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (n : Int)
      (m : Nat) :
    EvalECost st d env e st' (.int n) m →
    EvalECost st d env (.unary .neg e) st' (.int (-n)) m
  | not (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value)
      (m : Nat) :
    EvalECost st d env e st' v m →
    EvalECost st d env (.unary .not e) st' (.bool (!v.truthy)) m
  | call (st : St) (d : Nat) (env : Addr) (f : Expr) (args : List Expr)
      (st' st'' st''' : St) (fv : Value) (vs : List Value) (v : Value)
      (nf na nc : Nat) :
    EvalECost st d env f st' fv nf →
    EvalArgsCost st' d env args st'' vs na →
    CallCost st'' d fv vs st''' v nc →
    EvalECost st d env (.call f args) st''' v (nf + na + nc)
  | fn (st : St) (d : Nat) (env : Addr) (name : Option String)
      (params : List String) (body : List Stmt) (store' : Store) (a : Addr) :
    st.store.allocClosure ⟨env, name, params, body⟩ = (store', a) →
    EvalECost st d env (.fn name params body) ⟨store', st.out⟩ (.closure a) closureBytes

/-- Cost companion of `EvalArgs`. -/
inductive EvalArgsCost : St → Nat → Addr → List Expr → St → List Value → Nat → Prop where
  | nil (st : St) (d : Nat) (env : Addr) : EvalArgsCost st d env [] st [] 0
  | cons (st : St) (d : Nat) (env : Addr) (e : Expr) (es : List Expr)
      (st' st'' : St) (v : Value) (vs : List Value) (ne nes : Nat) :
    EvalECost st d env e st' v ne →
    EvalArgsCost st' d env es st'' vs nes →
    EvalArgsCost st d env (e :: es) st'' (v :: vs) (ne + nes)

/-- Cost companion of `Call`. The closure case charges one `env_new` (the
fresh call frame, `interp.c:194`) plus the per-parameter binding costs plus
the body cost. Natives allocate nothing. -/
inductive CallCost : St → Nat → Value → List Value → St → Value → Nat → Prop where
  | closure (st : St) (d : Nat) (a : Addr) (cd : ClosureData) (vs : List Value)
      (store' : Store) (frame : Addr) (st' : St) (status : Status)
      (v : Value) (nb : Nat) :
    st.store.closures[a]? = some cd →
    vs.length = cd.params.length →
    d < maxCallDepth →
    st.store.allocFrame (some cd.env) = (store', frame) →
    ExecSeqCost ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st.out⟩ (d + 1) frame cd.body st' status nb →
    (status = .normal ∧ v = .null ∨ status = .ret v) →
    CallCost st d (.closure a) vs st' v
      (envBytes + bindParamsCost store' frame (cd.params.zip vs) + nb)
  | print (st : St) (d : Nat) (vs : List Value) :
    CallCost st d (.native .print) vs
      ⟨st.store, st.out ++ printArgs st.store vs⟩ .null 0
  | println (st : St) (d : Nat) (vs : List Value) :
    CallCost st d (.native .println) vs
      ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null 0
  | assertOk (st : St) (d : Nat) (vs : List Value) (v m : Value) :
    (vs = [v] ∨ vs = [v, m]) →
    v.truthy = true →
    CallCost st d (.native .assert) vs st .null 0

/-- Cost companion of `ExecS`. -/
inductive ExecSCost : St → Nat → Addr → Stmt → St → Status → Nat → Prop where
  | expr (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value)
      (n : Nat) :
    EvalECost st d env e st' v n →
    ExecSCost st d env (.expr e) st' .normal n
  | varInit (st : St) (d : Nat) (env : Addr) (x : String) (e : Expr) (st' : St)
      (v : Value) (n : Nat) :
    EvalECost st d env e st' v n →
    ExecSCost st d env (.varDecl x (some e))
      ⟨st'.store.define env x v, st'.out⟩ .normal (n + defineCost st'.store env x)
  | varNull (st : St) (d : Nat) (env : Addr) (x : String) :
    ExecSCost st d env (.varDecl x none)
      ⟨st.store.define env x .null, st.out⟩ .normal (defineCost st.store env x)
  | block (st : St) (d : Nat) (env : Addr) (ss : List Stmt) (store' : Store)
      (inner : Addr) (st' : St) (status : Status) (n : Nat) :
    st.store.allocFrame (some env) = (store', inner) →
    ExecSeqCost ⟨store', st.out⟩ d inner ss st' status n →
    ExecSCost st d env (.block ss) st' status (envBytes + n)
  | ifTrue (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt)
      (e : Option Stmt) (st' st'' : St) (v : Value) (status : Status)
      (nc nt : Nat) :
    EvalECost st d env c st' v nc → v.truthy = true →
    ExecSCost st' d env t st'' status nt →
    ExecSCost st d env (.ifStmt c t e) st'' status (nc + nt)
  | ifFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (t e : Stmt)
      (st' st'' : St) (v : Value) (status : Status) (nc ne : Nat) :
    EvalECost st d env c st' v nc → v.truthy = false →
    ExecSCost st' d env e st'' status ne →
    ExecSCost st d env (.ifStmt c t (some e)) st'' status (nc + ne)
  | ifNone (st : St) (d : Nat) (env : Addr) (c : Expr) (t : Stmt) (st' : St)
      (v : Value) (nc : Nat) :
    EvalECost st d env c st' v nc → v.truthy = false →
    ExecSCost st d env (.ifStmt c t none) st' .normal nc
  | whileFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' : St) (v : Value) (nc : Nat) :
    EvalECost st d env c st' v nc → v.truthy = false →
    ExecSCost st d env (.whileStmt c b) st' .normal nc
  | whileBreak (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v : Value) (nc nb : Nat) :
    EvalECost st d env c st' v nc → v.truthy = true →
    ExecSCost st' d env b st'' .brk nb →
    ExecSCost st d env (.whileStmt c b) st'' .normal (nc + nb)
  | whileRet (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' : St) (v rv : Value) (nc nb : Nat) :
    EvalECost st d env c st' v nc → v.truthy = true →
    ExecSCost st' d env b st'' (.ret rv) nb →
    ExecSCost st d env (.whileStmt c b) st'' (.ret rv) (nc + nb)
  | whileLoop (st : St) (d : Nat) (env : Addr) (c : Expr) (b : Stmt)
      (st' st'' st''' : St) (v : Value) (status status' : Status)
      (nc nb nr : Nat) :
    EvalECost st d env c st' v nc → v.truthy = true →
    ExecSCost st' d env b st'' status nb →
    (status = .normal ∨ status = .cont) →
    ExecSCost st'' d env (.whileStmt c b) st''' status' nr →
    ExecSCost st d env (.whileStmt c b) st''' status' (nc + nb + nr)
  | forStart (st : St) (d : Nat) (env : Addr) (init : Option Stmt)
      (cnd : Option Expr) (step : Option Expr) (b : Stmt) (store' : Store)
      (outer : Addr) (st' st'' : St) (status : Status) (ni nl : Nat) :
    st.store.allocFrame (some env) = (store', outer) →
    ExecInitCost ⟨store', st.out⟩ d outer init st' ni →
    ForLoopCost st' d outer cnd step b st'' status nl →
    ExecSCost st d env (.forStmt init cnd step b) st'' status (envBytes + ni + nl)
  | ret (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value)
      (n : Nat) :
    EvalECost st d env e st' v n →
    ExecSCost st d env (.ret (some e)) st' (.ret v) n
  | retNull (st : St) (d : Nat) (env : Addr) :
    ExecSCost st d env (.ret none) st (.ret .null) 0
  | brk (st : St) (d : Nat) (env : Addr) : ExecSCost st d env .brk st .brk 0
  | cont (st : St) (d : Nat) (env : Addr) : ExecSCost st d env .cont st .cont 0

/-- Cost companion of `ExecInit`. -/
inductive ExecInitCost : St → Nat → Addr → Option Stmt → St → Nat → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ExecInitCost st d env none st 0
  | some (st : St) (d : Nat) (env : Addr) (s : Stmt) (st' : St) (n : Nat) :
    ExecSCost st d env s st' .normal n →
    ExecInitCost st d env (some s) st' n

/-- Cost companion of `ForLoop`. -/
inductive ForLoopCost : St → Nat → Addr → Option Expr → Option Expr → Stmt → St →
    Status → Nat → Prop where
  | condFalse (st : St) (d : Nat) (env : Addr) (c : Expr) (step : Option Expr)
      (b : Stmt) (st' : St) (v : Value) (nc : Nat) :
    EvalECost st d env c st' v nc → v.truthy = false →
    ForLoopCost st d env (some c) step b st' .normal nc
  | bodyBreak (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' : St) (nc nb : Nat) :
    ForCondCost st d env cnd st' nc →
    ExecSCost st' d env b st'' .brk nb →
    ForLoopCost st d env cnd step b st'' .normal (nc + nb)
  | bodyRet (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' : St) (rv : Value) (nc nb : Nat) :
    ForCondCost st d env cnd st' nc →
    ExecSCost st' d env b st'' (.ret rv) nb →
    ForLoopCost st d env cnd step b st'' (.ret rv) (nc + nb)
  | loop (st : St) (d : Nat) (env : Addr) (cnd : Option Expr)
      (step : Option Expr) (b : Stmt) (st' st'' st''' st'''' : St)
      (status status' : Status) (nc nb ns nr : Nat) :
    ForCondCost st d env cnd st' nc →
    ExecSCost st' d env b st'' status nb →
    (status = .normal ∨ status = .cont) →
    ExecStepCost st'' d env step st''' ns →
    ForLoopCost st''' d env cnd step b st'''' status' nr →
    ForLoopCost st d env cnd step b st'''' status' (nc + nb + ns + nr)

/-- Cost companion of `ForCond`. -/
inductive ForCondCost : St → Nat → Addr → Option Expr → St → Nat → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ForCondCost st d env none st 0
  | some (st : St) (d : Nat) (env : Addr) (c : Expr) (st' : St) (v : Value)
      (nc : Nat) :
    EvalECost st d env c st' v nc → v.truthy = true →
    ForCondCost st d env (some c) st' nc

/-- Cost companion of `ExecStep`. -/
inductive ExecStepCost : St → Nat → Addr → Option Expr → St → Nat → Prop where
  | none (st : St) (d : Nat) (env : Addr) : ExecStepCost st d env none st 0
  | some (st : St) (d : Nat) (env : Addr) (e : Expr) (st' : St) (v : Value)
      (n : Nat) :
    EvalECost st d env e st' v n →
    ExecStepCost st d env (some e) st' n

/-- Cost companion of `ExecSeq`. -/
inductive ExecSeqCost : St → Nat → Addr → List Stmt → St → Status → Nat → Prop where
  | nil (st : St) (d : Nat) (env : Addr) : ExecSeqCost st d env [] st .normal 0
  | consNormal (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' st'' : St) (status : Status) (n1 n2 : Nat) :
    ExecSCost st d env s st' .normal n1 →
    ExecSeqCost st' d env ss st'' status n2 →
    ExecSeqCost st d env (s :: ss) st'' status (n1 + n2)
  | consAbrupt (st : St) (d : Nat) (env : Addr) (s : Stmt) (ss : List Stmt)
      (st' : St) (status : Status) (n : Nat) :
    ExecSCost st d env s st' status n →
    status ≠ .normal →
    ExecSeqCost st d env (s :: ss) st' status n

end

/-! ## Existence of a cost derivation

Every semantic derivation has a cost companion. Because the nine relations are
mutually recursive, existence is proved for all of them simultaneously by the
auto-generated mutual induction principle (`EvalE.rec`), with the motive for
each relation being "there exists a cost". Each case picks the matching cost
constructor and feeds it the sub-witnesses; the numeric output is whatever the
constructor computes. -/

/-- The nine existence motives, packaged so all recursor calls share them. -/
private def M1 st d a e st' v (_ : EvalE st d a e st' v) : Prop :=
  ∃ n, EvalECost st d a e st' v n
private def M2 st d a es st' vs (_ : EvalArgs st d a es st' vs) : Prop :=
  ∃ n, EvalArgsCost st d a es st' vs n
private def M3 st d fv vs st' v (_ : Call st d fv vs st' v) : Prop :=
  ∃ n, CallCost st d fv vs st' v n
private def M4 st d a s st' status (_ : ExecS st d a s st' status) : Prop :=
  ∃ n, ExecSCost st d a s st' status n
private def M5 st d a init st' (_ : ExecInit st d a init st') : Prop :=
  ∃ n, ExecInitCost st d a init st' n
private def M6 st d a cnd step b st' status (_ : ForLoop st d a cnd step b st' status) : Prop :=
  ∃ n, ForLoopCost st d a cnd step b st' status n
private def M7 st d a cnd st' (_ : ForCond st d a cnd st') : Prop :=
  ∃ n, ForCondCost st d a cnd st' n
private def M8 st d a step st' (_ : ExecStep st d a step st') : Prop :=
  ∃ n, ExecStepCost st d a step st' n
private def M9 st d a ss st' status (_ : ExecSeq st d a ss st' status) : Prop :=
  ∃ n, ExecSeqCost st d a ss st' status n

/-- The 50 minor premises of the mutual recursor, as standalone lemmas so the
nine relation-existence projections below can each feed them to the recursor
without duplicating proofs. The final `(_ : Rel.ctor …)` slot of each motive is
proof-irrelevant, so the loose derivation term there is defeq to the exact one
the recursor supplies. Each is proved in tactic mode with explicitly named
`intro`s (matching the stated binders) so the proofs do not depend on fragile
positional-underscore counts. -/
private theorem c_int : ∀ st d env n, M1 st d env (.int n) st (.int n) (.int ..)
    := by
  intro _ _ _ _
  exact ⟨_, .int ..⟩
private theorem c_str : ∀ st d env s, M1 st d env (.str s) st (.str s) (.str ..)
    := by
  intro _ _ _ _
  exact ⟨_, .str ..⟩
private theorem c_bool : ∀ st d env b, M1 st d env (.bool b) st (.bool b) (.bool ..)
    := by
  intro _ _ _ _
  exact ⟨_, .bool ..⟩
private theorem c_null : ∀ st d env, M1 st d env .null st .null (.null ..)
    := by
  intro _ _ _
  exact ⟨_, .null ..⟩
private theorem c_var : ∀ st d env x v (hv : st.store.get? env x = some v),
    M1 st d env (.var x) st v (.var st d env x v hv)
    := by
  intro st d env x v hv
  exact ⟨_, .var _ _ _ _ _ hv⟩
private theorem c_assign : ∀ st d env x e st' v store''
    (he : EvalE st d env e st' v) (hs : st'.store.set? env x v = some store''),
    M1 st d env e st' v he →
    M1 st d env (.assign x e) ⟨store'', st'.out⟩ v (.assign st d env x e st' v store'' he hs)
    := by
  intro st d env x e st' v store'' he hs ih
  obtain ⟨n, hn⟩ := ih
  exact ⟨n, .assign _ _ _ _ _ _ _ _ _ hn hs⟩
private theorem c_bin : ∀ st d env op l r st' st'' lv rv v
    (hl : EvalE st d env l st' lv) (hr : EvalE st' d env r st'' rv)
    (hop : binOpSem st''.store op lv rv = some v),
    M1 st d env l st' lv hl → M1 st' d env r st'' rv hr →
    M1 st d env (.binary op l r) st'' v (.binary st d env op l r st' st'' lv rv v hl hr hop)
    := by
  intro st d env op l r st' st'' lv rv v hl hr hop ihl ihr
  obtain ⟨_, hnl⟩ := ihl
  obtain ⟨_, hnr⟩ := ihr
  exact ⟨_, .binary _ _ _ _ _ _ _ _ _ _ _ _ _ hnl hnr hop⟩
private theorem c_ort : ∀ st d env l r st' lv
    (hl : EvalE st d env l st' lv) (ht : lv.truthy = true),
    M1 st d env l st' lv hl →
    M1 st d env (.logical .or l r) st' (.bool true) (.orTrue st d env l r st' lv hl ht)
    := by
  intro st d env l r st' lv hl ht ih
  obtain ⟨n, hn⟩ := ih
  exact ⟨n, .orTrue _ _ _ _ _ _ _ _ hn ht⟩
private theorem c_orf : ∀ st d env l r st' st'' lv rv
    (hl : EvalE st d env l st' lv) (hf : lv.truthy = false) (hr : EvalE st' d env r st'' rv),
    M1 st d env l st' lv hl → M1 st' d env r st'' rv hr →
    M1 st d env (.logical .or l r) st'' (.bool rv.truthy) (.orFalse st d env l r st' st'' lv rv hl hf hr)
    := by
  intro st d env l r st' st'' lv rv hl hf hr ihl ihr
  obtain ⟨_, hnl⟩ := ihl
  obtain ⟨_, hnr⟩ := ihr
  exact ⟨_, .orFalse _ _ _ _ _ _ _ _ _ _ _ hnl hf hnr⟩
private theorem c_anf : ∀ st d env l r st' lv
    (hl : EvalE st d env l st' lv) (hf : lv.truthy = false),
    M1 st d env l st' lv hl →
    M1 st d env (.logical .and l r) st' (.bool false) (.andFalse st d env l r st' lv hl hf)
    := by
  intro st d env l r st' lv hl hf ih
  obtain ⟨n, hn⟩ := ih
  exact ⟨n, .andFalse _ _ _ _ _ _ _ _ hn hf⟩
private theorem c_ant : ∀ st d env l r st' st'' lv rv
    (hl : EvalE st d env l st' lv) (ht : lv.truthy = true) (hr : EvalE st' d env r st'' rv),
    M1 st d env l st' lv hl → M1 st' d env r st'' rv hr →
    M1 st d env (.logical .and l r) st'' (.bool rv.truthy) (.andTrue st d env l r st' st'' lv rv hl ht hr)
    := by
  intro st d env l r st' st'' lv rv hl ht hr ihl ihr
  obtain ⟨_, hnl⟩ := ihl
  obtain ⟨_, hnr⟩ := ihr
  exact ⟨_, .andTrue _ _ _ _ _ _ _ _ _ _ _ hnl ht hnr⟩
private theorem c_neg : ∀ st d env e st' n (he : EvalE st d env e st' (.int n)),
    M1 st d env e st' (.int n) he →
    M1 st d env (.unary .neg e) st' (.int (-n)) (.neg st d env e st' n he)
    := by
  intro st d env e st' n he ih
  obtain ⟨m, hm⟩ := ih
  exact ⟨m, .neg _ _ _ _ _ _ _ hm⟩
private theorem c_not : ∀ st d env e st' v (he : EvalE st d env e st' v),
    M1 st d env e st' v he →
    M1 st d env (.unary .not e) st' (.bool (!v.truthy)) (.not st d env e st' v he)
    := by
  intro st d env e st' v he ih
  obtain ⟨m, hm⟩ := ih
  exact ⟨m, .not _ _ _ _ _ _ _ hm⟩
private theorem c_call : ∀ st d env f args st' st'' st''' fv vs v
    (hf : EvalE st d env f st' fv) (ha : EvalArgs st' d env args st'' vs)
    (hc : Call st'' d fv vs st''' v),
    M1 st d env f st' fv hf → M2 st' d env args st'' vs ha → M3 st'' d fv vs st''' v hc →
    M1 st d env (.call f args) st''' v (.call st d env f args st' st'' st''' fv vs v hf ha hc)
    := by
  intro st d env f args st' st'' st''' fv vs v hf ha hc ihf iha ihc
  obtain ⟨_, hnf⟩ := ihf
  obtain ⟨_, hna⟩ := iha
  obtain ⟨_, hnc⟩ := ihc
  exact ⟨_, .call _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnf hna hnc⟩
private theorem c_fn : ∀ st d env name params body store' a
    (hc : st.store.allocClosure ⟨env, name, params, body⟩ = (store', a)),
    M1 st d env (.fn name params body) ⟨store', st.out⟩ (.closure a) (.fn st d env name params body store' a hc)
    := by
  intro st d env name params body store' a hc
  exact ⟨_, .fn _ _ _ _ _ _ _ _ hc⟩
private theorem c_anil : ∀ st d env, M2 st d env [] st [] (.nil ..)
    := by
  intro _ _ _
  exact ⟨_, .nil ..⟩
private theorem c_acons : ∀ st d env e es st' st'' v vs
    (he : EvalE st d env e st' v) (hes : EvalArgs st' d env es st'' vs),
    M1 st d env e st' v he → M2 st' d env es st'' vs hes →
    M2 st d env (e :: es) st'' (v :: vs) (.cons st d env e es st' st'' v vs he hes)
    := by
  intro st d env e es st' st'' v vs he hes ihe ihes
  obtain ⟨_, hne⟩ := ihe
  obtain ⟨_, hnes⟩ := ihes
  exact ⟨_, .cons _ _ _ _ _ _ _ _ _ _ _ hne hnes⟩
private theorem c_clo : ∀ st d a cd vs store' frame st' status v
    (hc : st.store.closures[a]? = some cd) (hlen : vs.length = cd.params.length)
    (hd : d < maxCallDepth) (hf : st.store.allocFrame (some cd.env) = (store', frame))
    (hst : ExecSeq ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
      (d + 1) frame cd.body st' status)
    (hstat : status = .normal ∧ v = .null ∨ status = .ret v),
    M9 ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st.out⟩
      (d + 1) frame cd.body st' status hst →
    M3 st d (.closure a) vs st' v (.closure st d a cd vs store' frame st' status v hc hlen hd hf hst hstat)
    := by
  intro st d a cd vs store' frame st' status v hc hlen hd hf hst hstat ihb
  obtain ⟨_, hnb⟩ := ihb
  exact ⟨_, .closure _ _ _ _ _ _ _ _ _ _ _ hc hlen hd hf hnb hstat⟩
private theorem c_pr : ∀ st d vs,
    M3 st d (.native .print) vs ⟨st.store, st.out ++ printArgs st.store vs⟩ .null (.print ..)
    := by
  intro _ _ _
  exact ⟨_, .print ..⟩
private theorem c_prl : ∀ st d vs,
    M3 st d (.native .println) vs ⟨st.store, st.out ++ printArgs st.store vs ++ "\n"⟩ .null (.println ..)
    := by
  intro _ _ _
  exact ⟨_, .println ..⟩
private theorem c_as : ∀ st d vs v m (hvs : vs = [v] ∨ vs = [v, m]) (ht : v.truthy = true),
    M3 st d (.native .assert) vs st .null (.assertOk st d vs v m hvs ht)
    := by
  intro st d vs v m hvs ht
  exact ⟨_, .assertOk _ _ _ _ _ hvs ht⟩
private theorem c_sexpr : ∀ st d env e st' v (he : EvalE st d env e st' v),
    M1 st d env e st' v he → M4 st d env (.expr e) st' .normal (.expr st d env e st' v he)
    := by
  intro st d env e st' v he ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .expr _ _ _ _ _ _ _ hn⟩
private theorem c_svi : ∀ st d env x e st' v (he : EvalE st d env e st' v),
    M1 st d env e st' v he →
    M4 st d env (.varDecl x (some e)) ⟨st'.store.define env x v, st'.out⟩ .normal
      (.varInit st d env x e st' v he)
    := by
  intro st d env x e st' v he ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .varInit _ _ _ _ _ _ _ _ hn⟩
private theorem c_svn : ∀ st d env x,
    M4 st d env (.varDecl x none) ⟨st.store.define env x .null, st.out⟩ .normal (.varNull ..)
    := by
  intro _ _ _ _
  exact ⟨_, .varNull ..⟩
private theorem c_sblk : ∀ st d env ss store' inner st' status
    (hf : st.store.allocFrame (some env) = (store', inner))
    (hseq : ExecSeq ⟨store', st.out⟩ d inner ss st' status),
    M9 ⟨store', st.out⟩ d inner ss st' status hseq →
    M4 st d env (.block ss) st' status (.block st d env ss store' inner st' status hf hseq)
    := by
  intro st d env ss store' inner st' status hf hseq ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .block _ _ _ _ _ _ _ _ _ hf hn⟩
private theorem c_sift : ∀ st d env c t e st' st'' v status
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hs : ExecS st' d env t st'' status),
    M1 st d env c st' v hc → M4 st' d env t st'' status hs →
    M4 st d env (.ifStmt c t e) st'' status (.ifTrue st d env c t e st' st'' v status hc ht hs)
    := by
  intro st d env c t e st' st'' v status hc ht hs ihc iht
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnt⟩ := iht
  exact ⟨_, .ifTrue _ _ _ _ _ _ _ _ _ _ _ _ hnc ht hnt⟩
private theorem c_siff : ∀ st d env c t e st' st'' v status
    (hc : EvalE st d env c st' v) (hf : v.truthy = false) (hs : ExecS st' d env e st'' status),
    M1 st d env c st' v hc → M4 st' d env e st'' status hs →
    M4 st d env (.ifStmt c t (some e)) st'' status (.ifFalse st d env c t e st' st'' v status hc hf hs)
    := by
  intro st d env c t e st' st'' v status hc hf hs ihc ihe
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hne⟩ := ihe
  exact ⟨_, .ifFalse _ _ _ _ _ _ _ _ _ _ _ _ hnc hf hne⟩
private theorem c_sifn : ∀ st d env c t st' v
    (hc : EvalE st d env c st' v) (hf : v.truthy = false),
    M1 st d env c st' v hc →
    M4 st d env (.ifStmt c t none) st' .normal (.ifNone st d env c t st' v hc hf)
    := by
  intro st d env c t st' v hc hf ihc
  obtain ⟨_, hnc⟩ := ihc
  exact ⟨_, .ifNone _ _ _ _ _ _ _ _ hnc hf⟩
private theorem c_swf : ∀ st d env c b st' v
    (hc : EvalE st d env c st' v) (hf : v.truthy = false),
    M1 st d env c st' v hc →
    M4 st d env (.whileStmt c b) st' .normal (.whileFalse st d env c b st' v hc hf)
    := by
  intro st d env c b st' v hc hf ihc
  obtain ⟨_, hnc⟩ := ihc
  exact ⟨_, .whileFalse _ _ _ _ _ _ _ _ hnc hf⟩
private theorem c_swb : ∀ st d env c b st' st'' v
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hb : ExecS st' d env b st'' .brk),
    M1 st d env c st' v hc → M4 st' d env b st'' .brk hb →
    M4 st d env (.whileStmt c b) st'' .normal (.whileBreak st d env c b st' st'' v hc ht hb)
    := by
  intro st d env c b st' st'' v hc ht hb ihc ihb
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  exact ⟨_, .whileBreak _ _ _ _ _ _ _ _ _ _ hnc ht hnb⟩
private theorem c_swr : ∀ st d env c b st' st'' v rv
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hb : ExecS st' d env b st'' (.ret rv)),
    M1 st d env c st' v hc → M4 st' d env b st'' (.ret rv) hb →
    M4 st d env (.whileStmt c b) st'' (.ret rv) (.whileRet st d env c b st' st'' v rv hc ht hb)
    := by
  intro st d env c b st' st'' v rv hc ht hb ihc ihb
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  exact ⟨_, .whileRet _ _ _ _ _ _ _ _ _ _ _ hnc ht hnb⟩
private theorem c_swl : ∀ st d env c b st' st'' st''' v status status'
    (hc : EvalE st d env c st' v) (ht : v.truthy = true) (hb : ExecS st' d env b st'' status)
    (hstat : status = .normal ∨ status = .cont)
    (hr : ExecS st'' d env (.whileStmt c b) st''' status'),
    M1 st d env c st' v hc → M4 st' d env b st'' status hb →
    M4 st'' d env (.whileStmt c b) st''' status' hr →
    M4 st d env (.whileStmt c b) st''' status'
      (.whileLoop st d env c b st' st'' st''' v status status' hc ht hb hstat hr)
    := by
  intro st d env c b st' st'' st''' v status status' hc ht hb hstat hr ihc ihb ihr
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  obtain ⟨_, hnr⟩ := ihr
  exact ⟨_, .whileLoop _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnc ht hnb hstat hnr⟩
private theorem c_sfor : ∀ st d env init cnd step b store' outer st' st'' status
    (hf : st.store.allocFrame (some env) = (store', outer))
    (hi : ExecInit ⟨store', st.out⟩ d outer init st')
    (hl : ForLoop st' d outer cnd step b st'' status),
    M5 ⟨store', st.out⟩ d outer init st' hi → M6 st' d outer cnd step b st'' status hl →
    M4 st d env (.forStmt init cnd step b) st'' status
      (.forStart st d env init cnd step b store' outer st' st'' status hf hi hl)
    := by
  intro st d env init cnd step b store' outer st' st'' status hf hi hl ihi ihl
  obtain ⟨_, hni⟩ := ihi
  obtain ⟨_, hnl⟩ := ihl
  exact ⟨_, .forStart _ _ _ _ _ _ _ _ _ _ _ _ _ _ hf hni hnl⟩
private theorem c_sret : ∀ st d env e st' v (he : EvalE st d env e st' v),
    M1 st d env e st' v he → M4 st d env (.ret (some e)) st' (.ret v) (.ret st d env e st' v he)
    := by
  intro st d env e st' v he ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .ret _ _ _ _ _ _ _ hn⟩
private theorem c_srn : ∀ st d env, M4 st d env (.ret none) st (.ret .null) (.retNull ..)
    := by
  intro _ _ _
  exact ⟨_, .retNull ..⟩
private theorem c_sbrk : ∀ st d env, M4 st d env .brk st .brk (.brk ..)
    := by
  intro _ _ _
  exact ⟨_, .brk ..⟩
private theorem c_scont : ∀ st d env, M4 st d env .cont st .cont (.cont ..)
    := by
  intro _ _ _
  exact ⟨_, .cont ..⟩
private theorem c_inone : ∀ st d env, M5 st d env none st (.none ..)
    := by
  intro _ _ _
  exact ⟨_, .none ..⟩
private theorem c_isome : ∀ st d env s st' (hs : ExecS st d env s st' .normal),
    M4 st d env s st' .normal hs → M5 st d env (some s) st' (.some st d env s st' hs)
    := by
  intro st d env s st' hs ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .some _ _ _ _ _ _ hn⟩
private theorem c_lcf : ∀ st d env c step b st' v
    (hc : EvalE st d env c st' v) (hf : v.truthy = false),
    M1 st d env c st' v hc →
    M6 st d env (some c) step b st' .normal (.condFalse st d env c step b st' v hc hf)
    := by
  intro st d env c step b st' v hc hf ihc
  obtain ⟨_, hnc⟩ := ihc
  exact ⟨_, .condFalse _ _ _ _ _ _ _ _ _ hnc hf⟩
private theorem c_lbb : ∀ st d env cnd step b st' st''
    (hcond : ForCond st d env cnd st') (hb : ExecS st' d env b st'' .brk),
    M7 st d env cnd st' hcond → M4 st' d env b st'' .brk hb →
    M6 st d env cnd step b st'' .normal (.bodyBreak st d env cnd step b st' st'' hcond hb)
    := by
  intro st d env cnd step b st' st'' hcond hb ihc ihb
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  exact ⟨_, .bodyBreak _ _ _ _ _ _ _ _ _ _ hnc hnb⟩
private theorem c_lbr : ∀ st d env cnd step b st' st'' rv
    (hcond : ForCond st d env cnd st') (hb : ExecS st' d env b st'' (.ret rv)),
    M7 st d env cnd st' hcond → M4 st' d env b st'' (.ret rv) hb →
    M6 st d env cnd step b st'' (.ret rv) (.bodyRet st d env cnd step b st' st'' rv hcond hb)
    := by
  intro st d env cnd step b st' st'' rv hcond hb ihc ihb
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  exact ⟨_, .bodyRet _ _ _ _ _ _ _ _ _ _ _ hnc hnb⟩
private theorem c_lloop : ∀ st d env cnd step b st' st'' st''' st'''' status status'
    (hcond : ForCond st d env cnd st') (hb : ExecS st' d env b st'' status)
    (hstat : status = .normal ∨ status = .cont) (hs : ExecStep st'' d env step st''')
    (hr : ForLoop st''' d env cnd step b st'''' status'),
    M7 st d env cnd st' hcond → M4 st' d env b st'' status hb →
    M8 st'' d env step st''' hs → M6 st''' d env cnd step b st'''' status' hr →
    M6 st d env cnd step b st'''' status'
      (.loop st d env cnd step b st' st'' st''' st'''' status status' hcond hb hstat hs hr)
    := by
  intro st d env cnd step b st' st'' st''' st'''' status status' hcond hb hstat hs hr ihc ihb ihs ihr
  obtain ⟨_, hnc⟩ := ihc
  obtain ⟨_, hnb⟩ := ihb
  obtain ⟨_, hns⟩ := ihs
  obtain ⟨_, hnr⟩ := ihr
  exact ⟨_, .loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hnc hnb hstat hns hnr⟩
private theorem c_cnone : ∀ st d env, M7 st d env none st (.none ..)
    := by
  intro _ _ _
  exact ⟨_, .none ..⟩
private theorem c_csome : ∀ st d env c st' v
    (hc : EvalE st d env c st' v) (ht : v.truthy = true),
    M1 st d env c st' v hc → M7 st d env (some c) st' (.some st d env c st' v hc ht)
    := by
  intro st d env c st' v hc ht ihc
  obtain ⟨_, hnc⟩ := ihc
  exact ⟨_, .some _ _ _ _ _ _ _ hnc ht⟩
private theorem c_stnone : ∀ st d env, M8 st d env none st (.none ..)
    := by
  intro _ _ _
  exact ⟨_, .none ..⟩
private theorem c_stsome : ∀ st d env e st' v (he : EvalE st d env e st' v),
    M1 st d env e st' v he → M8 st d env (some e) st' (.some st d env e st' v he)
    := by
  intro st d env e st' v he ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .some _ _ _ _ _ _ _ hn⟩
private theorem c_qnil : ∀ st d env, M9 st d env [] st .normal (.nil ..)
    := by
  intro _ _ _
  exact ⟨_, .nil ..⟩
private theorem c_qcn : ∀ st d env s ss st' st'' status
    (hs : ExecS st d env s st' .normal) (hss : ExecSeq st' d env ss st'' status),
    M4 st d env s st' .normal hs → M9 st' d env ss st'' status hss →
    M9 st d env (s :: ss) st'' status (.consNormal st d env s ss st' st'' status hs hss)
    := by
  intro st d env s ss st' st'' status hs hss ihs ihss
  obtain ⟨_, hn1⟩ := ihs
  obtain ⟨_, hn2⟩ := ihss
  exact ⟨_, .consNormal _ _ _ _ _ _ _ _ _ _ hn1 hn2⟩
private theorem c_qca : ∀ st d env s ss st' status
    (hs : ExecS st d env s st' status) (hne : status ≠ .normal),
    M4 st d env s st' status hs →
    M9 st d env (s :: ss) st' status (.consAbrupt st d env s ss st' status hs hne)
    := by
  intro st d env s ss st' status hs hne ih
  obtain ⟨_, hn⟩ := ih
  exact ⟨_, .consAbrupt _ _ _ _ _ _ _ _ hn hne⟩

/-- Existence of a cost derivation, established for all nine relations at once
by the mutual recursor with the existence motives `M1..M9` and the 50 shared
minor-premise lemmas above. -/
theorem cost_exists_mutual :
    (∀ {st d a e st' v}, EvalE st d a e st' v → ∃ n, EvalECost st d a e st' v n) ∧
    (∀ {st d a es st' vs}, EvalArgs st d a es st' vs → ∃ n, EvalArgsCost st d a es st' vs n) ∧
    (∀ {st d fv vs st' v}, Call st d fv vs st' v → ∃ n, CallCost st d fv vs st' v n) ∧
    (∀ {st d a s st' status}, ExecS st d a s st' status → ∃ n, ExecSCost st d a s st' status n) ∧
    (∀ {st d a init st'}, ExecInit st d a init st' → ∃ n, ExecInitCost st d a init st' n) ∧
    (∀ {st d a cnd step b st' status}, ForLoop st d a cnd step b st' status →
      ∃ n, ForLoopCost st d a cnd step b st' status n) ∧
    (∀ {st d a cnd st'}, ForCond st d a cnd st' → ∃ n, ForCondCost st d a cnd st' n) ∧
    (∀ {st d a step st'}, ExecStep st d a step st' → ∃ n, ExecStepCost st d a step st' n) ∧
    (∀ {st d a ss st' status}, ExecSeq st d a ss st' status →
      ∃ n, ExecSeqCost st d a ss st' status n) :=
  ⟨@fun st d a e st' v h => EvalE.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a es st' vs h => EvalArgs.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d fv vs st' v h => Call.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a s st' status h => ExecS.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a init st' h => ExecInit.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a cnd step b st' status h => ForLoop.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a cnd st' h => ForCond.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a step st' h => ExecStep.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h,
   @fun st d a ss st' status h => ExecSeq.rec (motive_1 := M1) (motive_2 := M2) (motive_3 := M3) (motive_4 := M4) (motive_5 := M5) (motive_6 := M6) (motive_7 := M7) (motive_8 := M8) (motive_9 := M9) c_int c_str c_bool c_null c_var c_assign c_bin c_ort c_orf c_anf c_ant c_neg c_not c_call c_fn c_anil c_acons c_clo c_pr c_prl c_as c_sexpr c_svi c_svn c_sblk c_sift c_siff c_sifn c_swf c_swb c_swr c_swl c_sfor c_sret c_srn c_sbrk c_scont c_inone c_isome c_lcf c_lbb c_lbr c_lloop c_cnone c_csome c_stnone c_stsome c_qnil c_qcn c_qca h⟩

/-- Existence of a cost derivation for expression evaluation. -/
theorem evalE_cost_exists {st d a e st' v} :
    EvalE st d a e st' v → ∃ n, EvalECost st d a e st' v n :=
  cost_exists_mutual.1

/-- Existence of a cost derivation for statement sequences — the relation
`BigStep` is built from. -/
theorem execSeq_cost_exists {st d a ss st' status} :
    ExecSeq st d a ss st' status → ∃ n, ExecSeqCost st d a ss st' status n :=
  cost_exists_mutual.2.2.2.2.2.2.2.2

/-! ## The store-derived cheap bound

The `Store` is append-only (`allocFrame`/`allocClosure` push, `define` only
rewrites `vars`), so frame and closure counts never shrink. The following are
the pure-store facts that underlie deliverable 4; the derivation-level
monotonicity (`execSeq_store_mono` below) then shows the final store's object
counts dominate the initial store's — so the machine frame/closure allocation
footprint is bounded by the final state alone (append-onlyness), without
re-examining the derivation. -/

/-- `allocFrame` grows the frame count by one and leaves closures alone. -/
theorem allocFrame_size (s : Store) (p : Option Addr) :
    (s.allocFrame p).1.frames.size = s.frames.size + 1 ∧
    (s.allocFrame p).1.closures.size = s.closures.size := by
  simp [Store.allocFrame]

/-- `allocClosure` grows the closure count by one and leaves frames alone. -/
theorem allocClosure_size (s : Store) (c : ClosureData) :
    (s.allocClosure c).1.closures.size = s.closures.size + 1 ∧
    (s.allocClosure c).1.frames.size = s.frames.size := by
  simp [Store.allocClosure]

/-- `define` never changes either object count (it only rewrites `vars`). -/
theorem define_size (s : Store) (a : Addr) (x : String) (v : Value) :
    (s.define a x v).frames.size = s.frames.size ∧
    (s.define a x v).closures.size = s.closures.size := by
  simp [Store.define]

/-- Folding `define` over a binding list preserves both object counts — the
shape the closure-call frame-init uses. -/
theorem foldDefine_size (l : List (String × Value)) (frame : Addr) (s : Store) :
    (l.foldl (fun s (x, v) => s.define frame x v) s).frames.size = s.frames.size ∧
    (l.foldl (fun s (x, v) => s.define frame x v) s).closures.size = s.closures.size := by
  induction l generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons p rest ih =>
    obtain ⟨x, v⟩ := p
    simp only [List.foldl_cons]
    obtain ⟨hf, hc⟩ := ih (s.define frame x v)
    exact ⟨by rw [hf]; exact (define_size s frame x v).1,
           by rw [hc]; exact (define_size s frame x v).2⟩

/-- Store-count ordering: `a`'s frame and closure counts are both ≤ `b`'s. This
is the append-only invariant, packaged for transitive chaining across a
derivation. -/
def StoreLe (a b : Store) : Prop :=
  a.frames.size ≤ b.frames.size ∧ a.closures.size ≤ b.closures.size

theorem StoreLe.refl (a : Store) : StoreLe a a := ⟨Nat.le_refl _, Nat.le_refl _⟩
theorem StoreLe.trans {a b c : Store} : StoreLe a b → StoreLe b c → StoreLe a c :=
  fun h1 h2 => ⟨Nat.le_trans h1.1 h2.1, Nat.le_trans h1.2 h2.2⟩
theorem StoreLe.allocFrame {s s' : Store} {p a} (h : s.allocFrame p = (s', a)) :
    StoreLe s s' := by
  have : s' = (s.allocFrame p).1 := by rw [h]
  refine this ▸ ⟨?_, ?_⟩ <;> simp [Store.allocFrame]
theorem StoreLe.allocClosure {s s' : Store} {c a} (h : s.allocClosure c = (s', a)) :
    StoreLe s s' := by
  have : s' = (s.allocClosure c).1 := by rw [h]
  refine this ▸ ⟨?_, ?_⟩ <;> simp [Store.allocClosure]
theorem StoreLe.define (s : Store) (a : Addr) (x : String) (v : Value) :
    StoreLe s (s.define a x v) := by refine ⟨?_, ?_⟩ <;> simp [Store.define]
theorem StoreLe.foldDefine (l : List (String × Value)) (frame : Addr) (s : Store) :
    StoreLe s (l.foldl (fun s (x, v) => s.define frame x v) s) := by
  induction l generalizing s with
  | nil => exact .refl _
  | cons p rest ih =>
    obtain ⟨x, v⟩ := p; simp only [List.foldl_cons]
    exact .trans (.define s frame x v) (ih _)

/-- Composite step: an `allocFrame` followed by (the store having reached) `t`.
Stated with the *continuation* `StoreLe (fold …) t` as an explicit premise so
`solve_by_elim` can apply it in one shot, driven by the sub-derivation
witness rather than guessing the fold. Covers `Call.closure`'s store chain. -/
theorem StoreLe.afFoldThen {s s' t : Store} {p a} (frame : Addr)
    (l : List (String × Value))
    (h : s.allocFrame p = (s', a))
    (ht : StoreLe (l.foldl (fun s (x, v) => s.define frame x v) s') t) :
    StoreLe s t :=
  .trans (.allocFrame h) (.trans (.foldDefine l frame s') ht)

/-- Composite step: an `allocFrame` followed by a continuation `StoreLe s' t`,
in one application (for `ExecS.block`/`ExecS.forStart`-style chains). -/
theorem StoreLe.afThen {s s' t : Store} {p a} (h : s.allocFrame p = (s', a))
    (ht : StoreLe s' t) : StoreLe s t :=
  .trans (.allocFrame h) ht

/-- Four-fold transitivity in one application, so `solve_by_elim` can compose
the longest pure-`StoreLe` chain — `ForLoop.loop`/`ForLoop.bodyBreak`'s
cond → body → step → recurse — without a deep transitivity search. -/
theorem StoreLe.trans4 {a b c e f : Store} :
    StoreLe a b → StoreLe b c → StoreLe c e → StoreLe e f → StoreLe a f :=
  fun h1 h2 h3 h4 => .trans h1 (.trans h2 (.trans h3 h4))

/-- `Store.set` (chain-walking assignment) never changes either object count —
it only rewrites one `vars` slot in place. -/
theorem set_preserves_size : ∀ g (s : Store) a x v s', s.set g a x v = some s' →
    s'.frames.size = s.frames.size ∧ s'.closures.size = s.closures.size := by
  intro g; induction g with
  | zero => intro s a x v s' h; exact absurd h (by simp [Store.set])
  | succ g ih =>
    intro s a x v s' h; unfold Store.set at h
    cases hfa : s.frames[a]? with
    | none => rw [hfa] at h; exact absurd h (by simp)
    | some f =>
      rw [hfa] at h; simp only [bind, Option.bind] at h
      by_cases hany : f.vars.any (·.1 == x)
      · rw [if_pos hany] at h; injection h with h; subst h
        exact ⟨Array.size_modify .., rfl⟩
      · rw [if_neg hany] at h
        cases hp : f.parent with
        | none => rw [hp] at h; exact absurd h (by simp)
        | some p =>
          rw [hp] at h; change s.set g p x v = some s' at h; exact ih s p x v s' h

theorem StoreLe.set {s s' : Store} {a x v} (h : s.set? a x v = some s') :
    StoreLe s s' := by
  obtain ⟨hf, hc⟩ := set_preserves_size _ s a x v s' h
  exact ⟨Nat.le_of_eq hf.symm, Nat.le_of_eq hc.symm⟩


set_option maxHeartbeats 8000000 in
/-- **Append-only monotonicity of the store along a derivation.** Executing a
statement sequence never shrinks the frame or closure count: the final store's
object counts dominate the initial store's. Proved by the mutual recursor with
`StoreLe`-between-input-and-output motives for all nine relations; each minor
premise chains the sub-derivations' `StoreLe` witnesses through the
constructor's `allocFrame`/`allocClosure`/`define`/`set` step, composed by
`solve_by_elim` (which accepts only fully-elaborated proofs, so no store
metavariable can leak). Consequence: `st'.store.frames.size`/`closures.size` —
hence the machine frame/closure allocation footprint the M4/M6 arena must
cover — are bounded by the *final* store alone, without re-examining the
derivation. -/
theorem execSeq_store_mono {st d a ss st' status}
    (h : ExecSeq st d a ss st' status) : StoreLe st.store st'.store := by
  refine ExecSeq.rec
    (motive_1 := fun st _ _ _ st' _ _ => StoreLe st.store st'.store)
    (motive_2 := fun st _ _ _ st' _ _ => StoreLe st.store st'.store)
    (motive_3 := fun st _ _ _ st' _ _ => StoreLe st.store st'.store)
    (motive_4 := fun st _ _ _ st' _ _ => StoreLe st.store st'.store)
    (motive_5 := fun st _ _ _ st' _ => StoreLe st.store st'.store)
    (motive_6 := fun st _ _ _ _ _ st' _ _ => StoreLe st.store st'.store)
    (motive_7 := fun st _ _ _ st' _ => StoreLe st.store st'.store)
    (motive_8 := fun st _ _ _ st' _ => StoreLe st.store st'.store)
    (motive_9 := fun st _ _ _ st' _ _ => StoreLe st.store st'.store)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  all_goals intros
  -- Each case's goal is one `StoreLe A B` where `B` is `A` after a bounded
  -- chain of allocation/define/set operations. `solve_by_elim` composes it
  -- from the pure-store lemmas — including the `afThen`/`afFoldThen` composites
  -- that fold the `Call.closure` and block/`for` allocation-then-continuation
  -- chains into a single application driven by the sub-derivation witness — and
  -- the in-context IHs. It only returns fully-elaborated proofs, so no `Store`
  -- metavariable is ever left dangling.
  all_goals
    solve_by_elim
      [StoreLe.refl, StoreLe.trans, StoreLe.trans4, StoreLe.allocFrame,
       StoreLe.allocClosure, StoreLe.define, StoreLe.foldDefine, StoreLe.set,
       StoreLe.afThen, StoreLe.afFoldThen]

/-- Specialised to a whole-program run from `initSt`: the final store retains
its one pre-built global frame (`initSt.store.frames.size = 1`). The
arena-budget argument reads the final object counts off `st'.store` knowing
they only grew from this baseline. -/
theorem bigStep_store_mono {st' : St} {p : Program}
    (h : ExecSeq initSt 0 0 p st' .normal) :
    1 ≤ st'.store.frames.size :=
  (execSeq_store_mono h).1

/-! ## The top-level budget package (deliverable 5)

`BigStepBudget p out n` says: the program `p` has a big-step derivation
printing exactly `out` whose **allocation cost is at most `n` bytes**. It is
the `BigStep` specification refined with a machine-allocation budget, and is
exactly the hypothesis the M4/M6 arena-budget argument consumes (with
`initSt`'s pre-built globals frame — 32 bytes plus its three native-name
copies — accounted as the fixed initial store contribution, separate from
`n`). -/
def BigStepBudget (p : Program) (out : String) (n : Nat) : Prop :=
  ∃ st' m, ExecSeqCost initSt 0 0 p st' .normal m ∧ st'.out = out ∧ m ≤ n

/-- Every `BigStep` derivation comes with a finite allocation budget: run the
existence lemma on the `ExecSeq` witness and take `n` to be its exact cost. -/
theorem bigStep_budget_exists {p : Program} {out : String} :
    BigStep p out → ∃ n, BigStepBudget p out n := by
  rintro ⟨st', hseq, hout⟩
  obtain ⟨m, hm⟩ := execSeq_cost_exists hseq
  exact ⟨m, st', m, hm, hout, Nat.le_refl m⟩

end Vsa.While
