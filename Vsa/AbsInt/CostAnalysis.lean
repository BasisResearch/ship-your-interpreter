import Vsa.AbsInt.Interp
import Vsa.AbsInt.Domains.ToItv
import Vsa.AbsInt.Domains.Offset
import Vsa.While.Cost

/-!
# Static bounds on allocation cost

`ccost`/`scost` compute an upper bound (`CB`, `none` = unbounded) on the
allocation cost the cost relations of `Vsa/While/Cost.lean` assign to any
run from a state in `γ(σ)`. They follow `aeval`/`aexec` and read the
abstract states and values those compute:

* a frame allocation costs `envBytes`, a closure `closureBytes`;
* a definition costs its name copy plus array growth, bounded by the number
  of names the abstract scope may bind (`defineBound`);
* string concatenation is unbounded unless both operands are integers;
* calls into closures are unbounded; natives cost nothing.

A loop's unrolled iterations are summed. The remaining iterations are covered
at a post-fixpoint `J`: if one iteration costs nothing, neither do they;
otherwise a condition `x < e` / `x <= e` bounds them when an offset analysis
(`A × OffV`, `Vsa/AbsInt/Domains/Offset.lean`) shows every iteration
increases `x`, giving `(H - L) · c + c` for an iteration cost `c`, `x ≥ L`
and `e ≤ H` at `J`.
-/

namespace Vsa.AbsInt

open Vsa.While AbsOps AbsDom

/-- A cost bound; `none` is unbounded. -/
abbrev CB := Option Nat

def cadd : CB → CB → CB
  | some a, some b => some (a + b)
  | _, _ => none

def cmax : CB → CB → CB
  | some a, some b => some (max a b)
  | _, _ => none

/-- `n` is within the bound. -/
def CLe (n : Nat) : CB → Prop
  | none => True
  | some m => n ≤ m

/-- The array-growth charge of `env_define` at binding count `c`. -/
def growthOf (c : Nat) : Nat :=
  if c = 0 then arrayReallocCost 8
  else if arrayCostAux (c + 1) 0 (c + 1) ≠ arrayCostAux c 0 c then
    arrayCostAux (c + 1) 0 (c + 1) - arrayCostAux c 0 c
  else 0

/-- The largest growth charge at a count up to `k`. -/
def growthMax (k : Nat) : Nat := (List.range (k + 1)).foldl (fun m c => max m (growthOf c)) 0

section Ops

variable {A : Type} [AbsOps A] [ToItv A]

/-- Bound on `defineCost` in the innermost frame. -/
def defineBound (σ : AState A) (x : String) : CB :=
  match σ with
  | .bot => some 0
  | .top => none
  | .sc [] => none
  | .sc (S :: _) =>
    match S.get x with
    | some ⟨_, true⟩ => some 0
    | _ => some (nameCopyCost x + growthMax (dedup (keys S)).length)

/-- The value is certainly not a string. -/
def noStr (a : A) : Bool :=
  match ToItv.toItv a with
  | .top => false
  | _ => true

/-- Bound on `binOpCost`. -/
def binCost (op : BinOp) (a b : A) : CB :=
  match op with
  | .add => if noStr a && noStr b then some 0 else none
  | _ => some 0

/-- Bound on the cost of calling a value of `a`. -/
def callCost (a : A) : CB :=
  match asNative a with
  | some _ => some 0
  | none => none

mutual

/-- Cost bound of an expression. -/
def ccost (σ : AState A) (e : Expr) : CB :=
  if σ.isBot then some 0 else
  match e with
  | .int _ | .str _ | .bool _ | .null | .var _ => some 0
  | .assign _ e => ccost σ e
  | .binary op l r =>
    cadd (cadd (ccost σ l) (ccost (aeval σ l).st r))
      (binCost op (aeval σ l).val (aeval (aeval σ l).st r).val)
  | .logical .or l r => cadd (ccost σ l) (ccost (branch false l (aeval σ l)) r)
  | .logical .and l r => cadd (ccost σ l) (ccost (branch true l (aeval σ l)) r)
  | .unary _ e => ccost σ e
  | .call f args =>
    cadd (cadd (ccost σ f) (cargs (aeval σ f).st args)) (callCost (aeval σ f).val)
  | .fn _ _ _ => some closureBytes

/-- Cost bound of an argument list. -/
def cargs (σ : AState A) : List Expr → CB
  | [] => some 0
  | e :: es => cadd (ccost σ e) (cargs (aeval σ e).st es)

end

/-- Cost bound of an optional expression. -/
def optCost (e : Option Expr) (I : AState A) : CB :=
  match e with
  | none => some 0
  | some e => ccost I e

/-! ## Loop iteration bounds -/

/-- Lift a state to the offset domain with no offset information. -/
def liftScope (S : Scope A) : Scope (A × OffV) :=
  S.map fun (x, b) => (x, ⟨(b.val, (ToItv.toItv b.val, none)), b.must⟩)

/-- Lift a state, pinning `x` at offset `0` from its current value. -/
def liftAt (J : AState A) (x : String) : AState (A × OffV) :=
  let J' : AState (A × OffV) := match J with
    | .bot => .bot
    | .top => .top
    | .sc l => .sc (l.map liftScope)
  J'.strengthen x ((J.lookup x).1, (ToItv.toItv (J.lookup x).1, some 0))

/-- The condition `x < e` / `x <= e` of a counted loop: the counter, the
bound on `e`, and `1` for `<=` (`0` for `<`). -/
def counted (c : Expr) : Option (String × Expr × Nat) :=
  match c with
  | .binary .lt (.var x) e => some (x, e, 0)
  | .binary .le (.var x) e => some (x, e, 1)
  | _ => none

/-- Upper bound of `e` at `J`. -/
def hiOf (J : AState A) (e : Expr) : Option Int :=
  match pureVal J e with
  | some a =>
    match ToItv.toItv a with
    | .range _ (some h) => some h
    | _ => none
  | none => none

/-- Lower bound of `x` at `J`. -/
def loOf (J : AState A) (x : String) : Option Int :=
  match ToItv.toItv (J.lookup x).1 with
  | .range (some l) _ => some l
  | _ => none

/-- The offset of `x` in a lifted state. -/
def offOf (σ : AState (A × OffV)) (x : String) : Option Int := (σ.lookup x).1.2.2

/-- Bound on the number of body entries from head states in `J`, given the
successor-state function of the lifted iteration. -/
def iterBound (next : AState (A × OffV) → AState (A × OffV)) (c : Expr)
    (J : AState A) : Option Nat :=
  match counted c with
  | some (x, e, k) =>
    match loOf J x, hiOf J e, offOf (next (liftAt J x)) x with
    | some l, some h, some o => if 1 ≤ o then some (h + k - l).toNat else none
    | _, _, _ => none
  | none => none

/-- Cost of all iterations from a post-fixpoint `J` with iteration cost `c`. -/
def rankCost (c : CB) (bound : Option Nat) : CB :=
  match c with
  | some 0 => some 0
  | some c => match bound with
    | some k => some (k * c + c)
    | none => none
  | none => none

/-- Cost of a loop: `k` unrolled iterations, then the post-fixpoint. -/
def loopCost (cfg : Cfg) (F : AState A → LStep A) (itc : AState A → CB)
    (rank : AState A → CB) : Nat → AState A → CB
  | 0, I => rank (postFix (fun J => (F J).next) cfg.widenFuel cfg.narrowFuel I)
  | k + 1, I =>
    if (F I).next.isBot then itc I
    else if (F I).next.le I then rank I
    else cadd (itc I) (loopCost cfg F itc rank k (F I).next)

end Ops

variable {A : Type} [AbsOps A] [ToItv A]

mutual

/-- Cost bound of a statement. -/
def scost (cfg : Cfg) (σ : AState A) (s : Stmt) : CB :=
  if σ.isBot then some 0 else
  match s with
  | .expr e => ccost σ e
  | .varDecl x (some e) => cadd (ccost σ e) (defineBound (aeval σ e).st x)
  | .varDecl x none => defineBound σ x
  | .block ss => cadd (some envBytes) (seqcost cfg σ.push ss)
  | .ifStmt c t e =>
    cadd (ccost σ c)
      (cmax (scost cfg (branch true c (aeval σ c)) t)
        (scostOpt cfg (branch false c (aeval σ c)) e))
  | .whileStmt c b =>
    loopCost cfg (whileF cfg c b)
      (fun I => cadd (ccost I c) (scost cfg (branch true c (aeval I c)) b))
      (fun J => rankCost (cadd (ccost J c) (scost cfg (branch true c (aeval J c)) b))
        (iterBound (fun I => (whileF cfg c b I).next) c J))
      cfg.unroll σ
  | .forStmt init cnd step b =>
    cadd (cadd (some envBytes) (scostOpt cfg σ.push init))
      (loopCost cfg (forF cfg cnd step b)
        (fun I => forItCost cfg cnd step b I)
        (fun J => rankCost (forItCost cfg cnd step b J)
          (match cnd with
            | some c => iterBound (fun I => (forF cfg cnd step b I).next) c J
            | none => none))
        cfg.unroll (aexecOpt cfg σ.push init).any)
  | .ret (some e) => ccost σ e
  | .ret none | .brk | .cont => some 0

/-- Cost bound of an optional statement. -/
def scostOpt (cfg : Cfg) (σ : AState A) : Option Stmt → CB
  | none => some 0
  | some s => scost cfg σ s

/-- Cost bound of one `for` iteration: condition, body, step. -/
def forItCost (cfg : Cfg) (cnd step : Option Expr) (b : Stmt) (I : AState A) : CB :=
  cadd (cadd (optCost cnd I)
      (scost cfg (match cnd with
        | none => I
        | some c => branch true c (optEval cnd I)) b))
    (optCost step
      ((aexec cfg (match cnd with
        | none => I
        | some c => branch true c (optEval cnd I)) b).norm.join
       (aexec cfg (match cnd with
        | none => I
        | some c => branch true c (optEval cnd I)) b).cont))

/-- Cost bound of a statement sequence. -/
def seqcost (cfg : Cfg) (σ : AState A) : List Stmt → CB
  | [] => some 0
  | s :: ss => cadd (scost cfg σ s) (seqcost cfg (aexec cfg σ s).norm ss)

end

/-- Bound on the allocation cost of any normal run of a program. -/
def progCost (cfg : Cfg) (p : Program) : CB := seqcost (A := A) cfg initState p

end Vsa.AbsInt
