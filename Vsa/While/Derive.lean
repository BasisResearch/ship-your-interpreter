import Lean
import Vsa.While.Semantics

/-!
# Syntax-directed derivation construction for the big-step semantics

`bigstep_derive` proves goals of the form `BigStep p out` for closed
programs `p` by *constructing the derivation tree directly*: a meta-level
recursion over the program syntax that, at each node, computes the relevant
side conditions by reduction (`whnf`), picks the unique applicable rule, and
emits the constructor application. There is no proof search and no
backtracking — the relation is deterministic, so the derivation is uniquely
determined by the program.

Nothing here evaluates WHILE inside the theory: this is untrusted tactic
code emitting a certificate; the kernel independently checks the resulting
derivation of the (purely inductive) big-step relation, re-reducing every
side condition itself. The only executable semantics in the development
remains the ELF binary under the RISC-V model.
-/

open Lean Meta Elab Tactic

namespace Vsa.While.DeriveTac

private def stTy : Lean.Expr := mkConst ``Vsa.While.St
private def valueTy : Lean.Expr := mkConst ``Vsa.While.Value
private def statusTy : Lean.Expr := mkConst ``Vsa.While.Status
private def storeTy : Lean.Expr := mkConst ``Vsa.While.Store
private def normalE : Lean.Expr := mkConst ``Vsa.While.Status.normal
private def nullE : Lean.Expr := mkConst ``Vsa.While.Value.null
private def trueE : Lean.Expr := mkConst ``Bool.true
private def falseE : Lean.Expr := mkConst ``Bool.false

private def stMk (store out : Lean.Expr) : Lean.Expr :=
  mkApp2 (mkConst ``Vsa.While.St.mk) store out

private def mkSome (ty v : Lean.Expr) : Lean.Expr :=
  mkApp2 (mkConst ``Option.some [levelZero]) ty v

/-- Split a (whnf'd) state into store and output components. -/
private def stParts (st : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  match (← whnf st).getAppFnArgs with
  | (``Vsa.While.St.mk, #[s, o]) => pure (s, o)
  | _ => throwError "state not in constructor form: {st}"

/-- Full normalization (states are kept normalized at every node so that
side-condition reductions stay cheap and terms stay compact). -/
private def norm (e : Lean.Expr) : MetaM Lean.Expr := Meta.reduce e

/-- Compute a value's truthiness by reduction. -/
private def truthy (v : Lean.Expr) : MetaM Bool := do
  let t ← whnf (mkApp (mkConst ``Vsa.While.Value.truthy) v)
  match t.getAppFnArgs with
  | (``Bool.true, _) => pure true
  | (``Bool.false, _) => pure false
  | _ => throwError "truthiness did not reduce: {t}"

/-- Walk an object-level `List` literal into meta-level elements. -/
private partial def listElems (l : Lean.Expr) : MetaM (List Lean.Expr) := do
  match (← whnf l).getAppFnArgs with
  | (``List.nil, _) => pure []
  | (``List.cons, #[_, hd, tl]) => return hd :: (← listElems tl)
  | _ => throwError "not a list literal: {l}"

/-- Build an object-level `List Value` from meta-level elements. -/
private def mkValueList (vs : List Lean.Expr) : Lean.Expr :=
  vs.foldr (fun v acc => mkApp3 (mkConst ``List.cons [levelZero]) valueTy v acc)
    (mkApp (mkConst ``List.nil [levelZero]) valueTy)

/-- Extract a concrete `Nat` from a reduced expression (literal or
`Nat.zero`/`Nat.succ` constructor form). -/
private partial def asNat (e : Lean.Expr) : MetaM Nat := do
  let e ← whnf e
  if let some n := e.rawNatLit? then return n
  match e.getAppFnArgs with
  | (``Nat.zero, _) => pure 0
  | (``Nat.succ, #[m]) => return (← asNat m) + 1
  | (``OfNat.ofNat, #[_, n, _]) => asNat n
  | _ => throwError "not a Nat literal: {e.dbgToString}"

/-- `some x` / `none` scrutinizer. -/
private def asOption (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let e' ← whnf e
  match e'.getAppFnArgs with
  | (``Option.none, _) => pure none
  | (``Option.some, #[_, v]) => pure (some v)
  | _ => throwError "not an option literal: {e'}"

/-- Scrutinize a status expression. -/
private inductive StatusV where
  | normal | brk | cont | ret (v : Lean.Expr)

private def asStatus (s : Lean.Expr) : MetaM StatusV := do
  match (← whnf s).getAppFnArgs with
  | (``Vsa.While.Status.normal, _) => pure .normal
  | (``Vsa.While.Status.brk, _) => pure .brk
  | (``Vsa.While.Status.cont, _) => pure .cont
  | (``Vsa.While.Status.ret, #[v]) => pure (.ret v)
  | _ => throwError "status did not reduce: {s}"

private def statusExpr : StatusV → Lean.Expr
  | .normal => normalE
  | .brk => mkConst ``Vsa.While.Status.brk
  | .cont => mkConst ``Vsa.While.Status.cont
  | .ret v => mkApp (mkConst ``Vsa.While.Status.ret) v

/-- Proof of `d < maxCallDepth` for a concrete depth literal `d`. The
proposition `d < maxCallDepth` is `Decidable`, so `of_decide_eq_true` applied
to `Eq.refl true` closes it — the kernel reduces `decide (d < 1000)` to `true`
for literal `d`, and `Eq.refl true : decide (d < 1000) = true` type-checks. -/
private def mkDepthProof (d : Lean.Expr) : MetaM Lean.Expr := do
  let propTy ← mkAppM ``LT.lt #[d, mkConst ``Vsa.While.maxCallDepth]
  let decInst ← synthInstance (← mkAppM ``Decidable #[propTy])
  let eqTrue ← mkEqRefl (mkConst ``Bool.true)
  -- `of_decide_eq_true : decide p = true → p`; the kernel reduces
  -- `decide (d < 1000)` to `true` for literal `d`, so `Eq.refl true` fits.
  mkAppOptM ``of_decide_eq_true #[propTy, decInst, eqTrue]

/-- Proof of `status = .normal ∨ status = .cont` for a concrete status. -/
private def normalOrContPrf (s : StatusV) : MetaM Lean.Expr := do
  let sE := statusExpr s
  let a ← mkEq sE normalE
  let b ← mkEq sE (mkConst ``Vsa.While.Status.cont)
  match s with
  | .normal => return mkApp3 (mkConst ``Or.inl) a b (← mkEqRefl normalE)
  | .cont =>
    let contPrf ← mkEqRefl (mkConst ``Vsa.While.Status.cont)
    return mkApp3 (mkConst ``Or.inr) a b contPrf
  | _ => throwError "status is neither normal nor cont"

mutual

/-- Derive `EvalE st d env e ? ?`; returns (proof, state', value). -/
private partial def dEvalE (st d env e : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``Vsa.While.Expr.int, #[n]) =>
    return (mkApp4 (mkConst ``Vsa.While.EvalE.int) st d env n, st,
      mkApp (mkConst ``Vsa.While.Value.int) n)
  | (``Vsa.While.Expr.str, #[s]) =>
    return (mkApp4 (mkConst ``Vsa.While.EvalE.str) st d env s, st,
      mkApp (mkConst ``Vsa.While.Value.str) s)
  | (``Vsa.While.Expr.bool, #[b]) =>
    return (mkApp4 (mkConst ``Vsa.While.EvalE.bool) st d env b, st,
      mkApp (mkConst ``Vsa.While.Value.bool) b)
  | (``Vsa.While.Expr.null, _) =>
    return (mkApp3 (mkConst ``Vsa.While.EvalE.null) st d env, st, nullE)
  | (``Vsa.While.Expr.var, #[x]) =>
    let (store, _) ← stParts st
    let r ← whnf (mkApp3 (mkConst ``Vsa.While.Store.get?) store env x)
    let some v ← asOption r
      | throwError "undefined variable {x}"
    let prf := mkAppN (mkConst ``Vsa.While.EvalE.var)
      #[st, d, env, x, v, ← mkEqRefl (mkSome valueTy v)]
    return (prf, st, v)
  | (``Vsa.While.Expr.assign, #[x, rhs]) =>
    let (p1, st1, v) ← dEvalE st d env rhs
    let (store1, out1) ← stParts st1
    let r ← whnf (mkApp4 (mkConst ``Vsa.While.Store.set?) store1 env x v)
    let some store2 ← asOption r
      | throwError "assignment to undefined variable {x}"
    let store2 ← norm store2
    let prf := mkAppN (mkConst ``Vsa.While.EvalE.assign)
      #[st, d, env, x, rhs, st1, v, store2, p1,
        ← mkEqRefl (mkSome storeTy store2)]
    return (prf, stMk store2 out1, v)
  | (``Vsa.While.Expr.binary, #[op, l, r]) =>
    let (p1, st1, lv) ← dEvalE st d env l
    let (p2, st2, rv) ← dEvalE st1 d env r
    let (store2, _) ← stParts st2
    let w ← whnf (mkAppN (mkConst ``Vsa.While.binOpSem) #[store2, op, lv, rv])
    let some v ← asOption w
      | throwError "binary operator error (type/div-by-zero) on {op}"
    let v ← norm v
    let prf := mkAppN (mkConst ``Vsa.While.EvalE.binary)
      #[st, d, env, op, l, r, st1, st2, lv, rv, v, p1, p2,
        ← mkEqRefl (mkSome valueTy v)]
    return (prf, st2, v)
  | (``Vsa.While.Expr.logical, #[op, l, r]) =>
    let (p1, st1, lv) ← dEvalE st d env l
    let lt ← truthy lv
    match (← whnf op).getAppFnArgs, lt with
    | (``Vsa.While.LogOp.or, _), true =>
      let prf := mkAppN (mkConst ``Vsa.While.EvalE.orTrue)
        #[st, d, env, l, r, st1, lv, p1, ← mkEqRefl trueE]
      return (prf, st1, mkApp (mkConst ``Vsa.While.Value.bool) trueE)
    | (``Vsa.While.LogOp.or, _), false =>
      let (p2, st2, rv) ← dEvalE st1 d env r
      let rt := if (← truthy rv) then trueE else falseE
      let prf := mkAppN (mkConst ``Vsa.While.EvalE.orFalse)
        #[st, d, env, l, r, st1, st2, lv, rv, p1, ← mkEqRefl falseE, p2]
      return (prf, st2, mkApp (mkConst ``Vsa.While.Value.bool) rt)
    | (``Vsa.While.LogOp.and, _), false =>
      let prf := mkAppN (mkConst ``Vsa.While.EvalE.andFalse)
        #[st, d, env, l, r, st1, lv, p1, ← mkEqRefl falseE]
      return (prf, st1, mkApp (mkConst ``Vsa.While.Value.bool) falseE)
    | (``Vsa.While.LogOp.and, _), true =>
      let (p2, st2, rv) ← dEvalE st1 d env r
      let rt := if (← truthy rv) then trueE else falseE
      let prf := mkAppN (mkConst ``Vsa.While.EvalE.andTrue)
        #[st, d, env, l, r, st1, st2, lv, rv, p1, ← mkEqRefl trueE, p2]
      return (prf, st2, mkApp (mkConst ``Vsa.While.Value.bool) rt)
    | _, _ => throwError "bad logical operator"
  | (``Vsa.While.Expr.unary, #[op, e1]) =>
    match (← whnf op).getAppFnArgs with
    | (``Vsa.While.UnOp.neg, _) =>
      let (p1, st1, v) ← dEvalE st d env e1
      match (← whnf v).getAppFnArgs with
      | (``Vsa.While.Value.int, #[n]) =>
        let nn ← norm (mkApp (mkConst ``Int.neg) n)
        let prf := mkAppN (mkConst ``Vsa.While.EvalE.neg)
          #[st, d, env, e1, st1, n, p1]
        return (prf, st1, mkApp (mkConst ``Vsa.While.Value.int) nn)
      | _ => throwError "unary minus on non-int"
    | (``Vsa.While.UnOp.not, _) =>
      let (p1, st1, v) ← dEvalE st d env e1
      let rt := if (← truthy v) then falseE else trueE
      let prf := mkAppN (mkConst ``Vsa.While.EvalE.not)
        #[st, d, env, e1, st1, v, p1]
      return (prf, st1, mkApp (mkConst ``Vsa.While.Value.bool) rt)
    | _ => throwError "bad unary operator"
  | (``Vsa.While.Expr.call, #[f, args]) =>
    let (pf, st1, fv) ← dEvalE st d env f
    let (pa, st2, vsE, _) ← dEvalArgs st1 d env args
    let (pc, st3, v) ← dCall st2 d fv vsE
    let prf := mkAppN (mkConst ``Vsa.While.EvalE.call)
      #[st, d, env, f, args, st1, st2, st3, fv, vsE, v, pf, pa, pc]
    return (prf, st3, v)
  | (``Vsa.While.Expr.fn, #[name, params, body]) =>
    let (store, out) ← stParts st
    let cd := mkApp4 (mkConst ``Vsa.While.ClosureData.mk) env name params body
    let w ← whnf (mkApp2 (mkConst ``Vsa.While.Store.allocClosure) store cd)
    match w.getAppFnArgs with
    | (``Prod.mk, #[_, _, store', a]) =>
      let store' ← norm store'
      let a ← norm a
      let pairE := mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) storeTy
        (mkConst ``Nat) store' a
      let prf := mkAppN (mkConst ``Vsa.While.EvalE.fn)
        #[st, d, env, name, params, body, store', a, ← mkEqRefl pairE]
      return (prf, stMk store' out, mkApp (mkConst ``Vsa.While.Value.closure) a)
    | _ => throwError "allocClosure did not reduce to a pair"
  | _ => throwError "unknown expression head: {e}"

/-- Derive `EvalArgs st d env es ? ?`; returns
(proof, state', object list of values, meta list of values). -/
private partial def dEvalArgs (st d env es : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × Lean.Expr × List Lean.Expr) := do
  match (← whnf es).getAppFnArgs with
  | (``List.nil, _) =>
    return (mkApp3 (mkConst ``Vsa.While.EvalArgs.nil) st d env, st,
      mkValueList [], [])
  | (``List.cons, #[_, e, es']) =>
    let (p1, st1, v) ← dEvalE st d env e
    let (p2, st2, vsE, vs) ← dEvalArgs st1 d env es'
    let vsE' := mkApp3 (mkConst ``List.cons [levelZero]) valueTy v vsE
    let prf := mkAppN (mkConst ``Vsa.While.EvalArgs.cons)
      #[st, d, env, e, es', st1, st2, v, vsE, p1, p2]
    return (prf, st2, vsE', v :: vs)
  | _ => throwError "argument list is not a literal"

/-- Derive `Call st d fv vs ? ?`; returns (proof, state', result value). -/
private partial def dCall (st d fv vsE : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let fv ← whnf fv
  match fv.getAppFnArgs with
  | (``Vsa.While.Value.closure, #[a]) =>
    let (store, out) ← stParts st
    -- look up the closure by walking the (literal) closure array
    let closures ← match (← whnf store).getAppFnArgs with
      | (``Vsa.While.Store.mk, #[_, cs]) => pure cs
      | _ => throwError "store not in constructor form"
    let csList ← match (← whnf closures).getAppFnArgs with
      | (``Array.mk, #[_, l]) => listElems l
      | _ => throwError "closure array not a literal"
    let aN ← asNat a
    let some cd := csList[aN]?
      | throwError "dangling closure address {aN}"
    let (cdEnv, params) ← match (← whnf cd).getAppFnArgs with
      | (``Vsa.While.ClosureData.mk, #[env', _, ps, _]) =>
        pure (env', ← listElems ps)
      | _ => throwError "closure data not in constructor form"
    let body ← match (← whnf cd).getAppFnArgs with
      | (``Vsa.While.ClosureData.mk, #[_, _, _, b]) => pure b
      | _ => unreachable!
    let vs ← listElems vsE
    unless vs.length == params.length do
      throwError "arity mismatch: {vs.length} args for {params.length} params"
    -- the call-depth guard: this closure call needs `d < maxCallDepth`, and
    -- its body runs one level deeper.
    let dN ← asNat d
    unless dN < 1000 do
      throwError "call depth {dN} reached the cap (maxCallDepth = 1000)"
    let depthPrf ← mkDepthProof d
    let dSucc := mkRawNatLit (dN + 1)
    -- allocate the frame
    let w ← whnf (mkApp2 (mkConst ``Vsa.While.Store.allocFrame) store
      (mkSome (mkConst ``Nat) cdEnv))
    let (store1, frame) ← match w.getAppFnArgs with
      | (``Prod.mk, #[_, _, s, f]) => pure (← norm s, ← norm f)
      | _ => throwError "allocFrame did not reduce"
    -- bind the parameters
    let mut storeB := store1
    for (x, v) in params.zip vs do
      storeB ← norm (mkAppN (mkConst ``Vsa.While.Store.define)
        #[storeB, frame, x, v])
    -- run the body at depth `d + 1`
    let (pseq, st', sv) ← dExecSeq (stMk storeB out) dSucc frame body
    let statusE := statusExpr sv
    -- the status disjunction and result value
    let (v, orPrf) ← match sv with
      | .normal =>
        let aTy ← mkAppM ``And #[← mkEq statusE normalE, ← mkEq nullE nullE]
        let bTy ← mkEq statusE (mkApp (mkConst ``Vsa.While.Status.ret) nullE)
        let andPrf := mkApp4 (mkConst ``And.intro) (← mkEq statusE normalE)
          (← mkEq nullE nullE) (← mkEqRefl normalE) (← mkEqRefl nullE)
        pure (nullE, mkApp3 (mkConst ``Or.inl) aTy bTy andPrf)
      | .ret rv =>
        let aTy ← mkAppM ``And #[← mkEq statusE normalE, ← mkEq rv nullE]
        let bTy ← mkEq statusE (mkApp (mkConst ``Vsa.While.Status.ret) rv)
        pure (rv, mkApp3 (mkConst ``Or.inr) aTy bTy (← mkEqRefl statusE))
      | _ => throwError "break/continue escaped a function body"
    let prf := mkAppN (mkConst ``Vsa.While.Call.closure)
      #[st, d, a, cd, vsE, store1, frame, st', statusE, v,
        ← mkEqRefl (mkSome (mkConst ``Vsa.While.ClosureData) cd),
        ← mkEqRefl (mkNatLit params.length),
        depthPrf,
        ← mkEqRefl (mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) storeTy
          (mkConst ``Nat) store1 frame),
        pseq, orPrf]
    return (prf, st', v)
  | (``Vsa.While.Value.native, #[nf]) =>
    let (store, out) ← stParts st
    match (← whnf nf).getAppFnArgs with
    | (``Vsa.While.NativeFn.print, _) =>
      let printed ← norm (mkApp2 (mkConst ``Vsa.While.printArgs) store vsE)
      let out' ← norm (mkApp2 (mkConst ``String.append) out printed)
      let prf := mkApp3 (mkConst ``Vsa.While.Call.print) st d vsE
      return (prf, stMk store out', nullE)
    | (``Vsa.While.NativeFn.println, _) =>
      let printed ← norm (mkApp2 (mkConst ``Vsa.While.printArgs) store vsE)
      let out' ← norm (mkApp2 (mkConst ``String.append)
        (mkApp2 (mkConst ``String.append) out printed) (mkStrLit "\n"))
      let prf := mkApp3 (mkConst ``Vsa.While.Call.println) st d vsE
      return (prf, stMk store out', nullE)
    | (``Vsa.While.NativeFn.assert, _) =>
      let vs ← listElems vsE
      let (v, m) ← match vs with
        | [v] => pure (v, nullE)
        | [v, m] => pure (v, m)
        | _ => throwError "assert takes 1 or 2 arguments"
      unless (← truthy v) do throwError "assertion failed"
      let aTy ← mkEq vsE (mkValueList [v])
      let bTy ← mkEq vsE (mkValueList [v, m])
      let orPrf ← match vs with
        | [_] => pure (mkApp3 (mkConst ``Or.inl) aTy bTy (← mkEqRefl vsE))
        | _ => pure (mkApp3 (mkConst ``Or.inr) aTy bTy (← mkEqRefl vsE))
      let prf := mkAppN (mkConst ``Vsa.While.Call.assertOk)
        #[st, d, vsE, v, m, orPrf, ← mkEqRefl trueE]
      return (prf, st, nullE)
    | _ => throwError "unknown native"
  | _ => throwError "call of a non-function value"

/-- Derive `ExecS st d env s ? ?`; returns (proof, state', status). -/
private partial def dExecS (st d env s : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × StatusV) := do
  let s ← whnf s
  match s.getAppFnArgs with
  | (``Vsa.While.Stmt.expr, #[e]) =>
    let (p1, st1, v) ← dEvalE st d env e
    let prf := mkAppN (mkConst ``Vsa.While.ExecS.expr)
      #[st, d, env, e, st1, v, p1]
    return (prf, st1, .normal)
  | (``Vsa.While.Stmt.varDecl, #[x, oe]) =>
    match ← asOption oe with
    | some e =>
      let (p1, st1, v) ← dEvalE st d env e
      let (store1, out1) ← stParts st1
      let store' ← norm (mkAppN (mkConst ``Vsa.While.Store.define)
        #[store1, env, x, v])
      let prf := mkAppN (mkConst ``Vsa.While.ExecS.varInit)
        #[st, d, env, x, e, st1, v, p1]
      return (prf, stMk store' out1, .normal)
    | none =>
      let (store, out) ← stParts st
      let store' ← norm (mkAppN (mkConst ``Vsa.While.Store.define)
        #[store, env, x, nullE])
      let prf := mkApp4 (mkConst ``Vsa.While.ExecS.varNull) st d env x
      return (prf, stMk store' out, .normal)
  | (``Vsa.While.Stmt.block, #[ss]) =>
    let (store, out) ← stParts st
    let w ← whnf (mkApp2 (mkConst ``Vsa.While.Store.allocFrame) store
      (mkSome (mkConst ``Nat) env))
    let (store', inner) ← match w.getAppFnArgs with
      | (``Prod.mk, #[_, _, s', f]) => pure (← norm s', ← norm f)
      | _ => throwError "allocFrame did not reduce"
    let (pseq, st', sv) ← dExecSeq (stMk store' out) d inner ss
    let prf := mkAppN (mkConst ``Vsa.While.ExecS.block)
      #[st, d, env, ss, store', inner, st', statusExpr sv,
        ← mkEqRefl (mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) storeTy
          (mkConst ``Nat) store' inner),
        pseq]
    return (prf, st', sv)
  | (``Vsa.While.Stmt.ifStmt, #[c, t, oe]) =>
    let (pc, st1, v) ← dEvalE st d env c
    if ← truthy v then
      let (pt, st2, sv) ← dExecS st1 d env t
      let prf := mkAppN (mkConst ``Vsa.While.ExecS.ifTrue)
        #[st, d, env, c, t, oe, st1, st2, v, statusExpr sv, pc,
          ← mkEqRefl trueE, pt]
      return (prf, st2, sv)
    else
      match ← asOption oe with
      | some e =>
        let (pe, st2, sv) ← dExecS st1 d env e
        let prf := mkAppN (mkConst ``Vsa.While.ExecS.ifFalse)
          #[st, d, env, c, t, e, st1, st2, v, statusExpr sv, pc,
            ← mkEqRefl falseE, pe]
        return (prf, st2, sv)
      | none =>
        let prf := mkAppN (mkConst ``Vsa.While.ExecS.ifNone)
          #[st, d, env, c, t, st1, v, pc, ← mkEqRefl falseE]
        return (prf, st1, .normal)
  | (``Vsa.While.Stmt.whileStmt, #[c, b]) =>
    dWhile st d env c b
  | (``Vsa.While.Stmt.forStmt, #[init, cnd, step, b]) =>
    let (store, out) ← stParts st
    let w ← whnf (mkApp2 (mkConst ``Vsa.While.Store.allocFrame) store
      (mkSome (mkConst ``Nat) env))
    let (store', outer) ← match w.getAppFnArgs with
      | (``Prod.mk, #[_, _, s', f]) => pure (← norm s', ← norm f)
      | _ => throwError "allocFrame did not reduce"
    let st0 := stMk store' out
    let (pinit, st1) ← match ← asOption init with
      | none =>
        pure (mkApp3 (mkConst ``Vsa.While.ExecInit.none) st0 d outer, st0)
      | some is =>
        let (ps, st1, sv) ← dExecS st0 d outer is
        match sv with
        | .normal =>
          pure (mkAppN (mkConst ``Vsa.While.ExecInit.some)
            #[st0, d, outer, is, st1, ps], st1)
        | _ => throwError "for-initializer did not finish normally"
    let (ploop, st2, sv) ← dForLoop st1 d outer cnd step b
    let prf := mkAppN (mkConst ``Vsa.While.ExecS.forStart)
      #[st, d, env, init, cnd, step, b, store', outer, st1, st2, statusExpr sv,
        ← mkEqRefl (mkApp4 (mkConst ``Prod.mk [levelZero, levelZero]) storeTy
          (mkConst ``Nat) store' outer),
        pinit, ploop]
    return (prf, st2, sv)
  | (``Vsa.While.Stmt.ret, #[oe]) =>
    match ← asOption oe with
    | some e =>
      let (p1, st1, v) ← dEvalE st d env e
      let prf := mkAppN (mkConst ``Vsa.While.ExecS.ret)
        #[st, d, env, e, st1, v, p1]
      return (prf, st1, .ret v)
    | none =>
      let prf := mkApp3 (mkConst ``Vsa.While.ExecS.retNull) st d env
      return (prf, st, .ret nullE)
  | (``Vsa.While.Stmt.brk, _) =>
    return (mkApp3 (mkConst ``Vsa.While.ExecS.brk) st d env, st, .brk)
  | (``Vsa.While.Stmt.cont, _) =>
    return (mkApp3 (mkConst ``Vsa.While.ExecS.cont) st d env, st, .cont)
  | _ => throwError "unknown statement head: {s}"

/-- Derive a `while` statement (iterating meta-side). -/
private partial def dWhile (st d env c b : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × StatusV) := do
  let (pc, st1, v) ← dEvalE st d env c
  if !(← truthy v) then
    let prf := mkAppN (mkConst ``Vsa.While.ExecS.whileFalse)
      #[st, d, env, c, b, st1, v, pc, ← mkEqRefl falseE]
    return (prf, st1, .normal)
  else
    let (pb, st2, bsv) ← dExecS st1 d env b
    match bsv with
    | .brk =>
      let prf := mkAppN (mkConst ``Vsa.While.ExecS.whileBreak)
        #[st, d, env, c, b, st1, st2, v, pc, ← mkEqRefl trueE, pb]
      return (prf, st2, .normal)
    | .ret rv =>
      let prf := mkAppN (mkConst ``Vsa.While.ExecS.whileRet)
        #[st, d, env, c, b, st1, st2, v, rv, pc, ← mkEqRefl trueE, pb]
      return (prf, st2, .ret rv)
    | _ =>
      let (pnext, st3, sv') ← dWhile st2 d env c b
      let prf := mkAppN (mkConst ``Vsa.While.ExecS.whileLoop)
        #[st, d, env, c, b, st1, st2, st3, v, statusExpr bsv, statusExpr sv',
          pc, ← mkEqRefl trueE, pb, ← normalOrContPrf bsv, pnext]
      return (prf, st3, sv')

/-- Derive a `for` loop (iterating meta-side). -/
private partial def dForLoop (st d env cnd step b : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × StatusV) := do
  -- condition
  let condRes ← match ← asOption cnd with
    | none =>
      pure (Sum.inl (mkApp3 (mkConst ``Vsa.While.ForCond.none) st d env, st))
    | some c =>
      let (pc, st1, v) ← dEvalE st d env c
      if ← truthy v then
        pure (Sum.inl (mkAppN (mkConst ``Vsa.While.ForCond.some)
          #[st, d, env, c, st1, v, pc, ← mkEqRefl trueE], st1))
      else
        -- condition failed: ForLoop.condFalse
        let prf := mkAppN (mkConst ``Vsa.While.ForLoop.condFalse)
          #[st, d, env, c, step, b, st1, v, pc, ← mkEqRefl falseE]
        pure (Sum.inr (prf, st1))
  match condRes with
  | .inr (prf, st1) => return (prf, st1, .normal)
  | .inl (pcond, st1) =>
    let (pb, st2, bsv) ← dExecS st1 d env b
    match bsv with
    | .brk =>
      let prf := mkAppN (mkConst ``Vsa.While.ForLoop.bodyBreak)
        #[st, d, env, cnd, step, b, st1, st2, pcond, pb]
      return (prf, st2, .normal)
    | .ret rv =>
      let prf := mkAppN (mkConst ``Vsa.While.ForLoop.bodyRet)
        #[st, d, env, cnd, step, b, st1, st2, rv, pcond, pb]
      return (prf, st2, .ret rv)
    | _ =>
      let (pstep, st3) ← match ← asOption step with
        | none =>
          pure (mkApp3 (mkConst ``Vsa.While.ExecStep.none) st2 d env, st2)
        | some e =>
          let (pe, st3, v) ← dEvalE st2 d env e
          pure (mkAppN (mkConst ``Vsa.While.ExecStep.some)
            #[st2, d, env, e, st3, v, pe], st3)
      let (pnext, st4, sv') ← dForLoop st3 d env cnd step b
      let prf := mkAppN (mkConst ``Vsa.While.ForLoop.loop)
        #[st, d, env, cnd, step, b, st1, st2, st3, st4, statusExpr bsv,
          statusExpr sv', pcond, pb, ← normalOrContPrf bsv, pstep, pnext]
      return (prf, st4, sv')

/-- Derive `ExecSeq st d env ss ? ?`; returns (proof, state', status). -/
private partial def dExecSeq (st d env ss : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr × StatusV) := do
  match (← whnf ss).getAppFnArgs with
  | (``List.nil, _) =>
    return (mkApp3 (mkConst ``Vsa.While.ExecSeq.nil) st d env, st, .normal)
  | (``List.cons, #[_, s, ss']) =>
    let (p1, st1, sv) ← dExecS st d env s
    match sv with
    | .normal =>
      let (p2, st2, sv') ← dExecSeq st1 d env ss'
      let prf := mkAppN (mkConst ``Vsa.While.ExecSeq.consNormal)
        #[st, d, env, s, ss', st1, st2, statusExpr sv', p1, p2]
      return (prf, st2, sv')
    | _ =>
      let statusE := statusExpr sv
      let neTy := mkApp3 (mkConst ``Ne [levelOne]) statusTy statusE normalE
      let nePrf ← mkDecideProof neTy
      let prf := mkAppN (mkConst ``Vsa.While.ExecSeq.consAbrupt)
        #[st, d, env, s, ss', st1, statusE, p1, nePrf]
      return (prf, st1, sv)
  | _ => throwError "statement list is not a literal"

end

/-- Prove `BigStep p out` by direct syntax-directed derivation construction. -/
elab "bigstep_derive" : tactic => do
  let g ← getMainGoal
  g.withContext do
    let goalTy ← g.getType
    let (p, out) ← match (← whnfR goalTy).getAppFnArgs with
      | (``Vsa.While.BigStep, #[p, out]) => pure (p, out)
      | _ => throwError "goal is not of the form BigStep p out"
    let st0 ← norm (mkConst ``Vsa.While.initSt)
    -- top-level statements run at call depth 0 in the global frame (address 0)
    let (prf, st', sv) ← dExecSeq st0 (mkRawNatLit 0) (mkRawNatLit 0) p
    unless (match sv with | .normal => true | _ => false) do
      throwError "program did not finish normally"
    -- ⟨st', derivation, output check⟩
    let aTy := mkAppN (mkConst ``Vsa.While.ExecSeq)
      #[mkConst ``Vsa.While.initSt, mkRawNatLit 0, mkRawNatLit 0, p, st', normalE]
    let bTy ← mkEq (mkApp (mkConst ``Vsa.While.St.out) st') out
    -- the claimed output must actually reduce to the target string
    let outActual ← norm (mkApp (mkConst ``Vsa.While.St.out) st')
    let outTarget ← norm out
    unless (← isDefEq outActual outTarget) do
      throwError "program output does not match the claimed string\n
        claimed: {outTarget}\nactual: {outActual}"
    let andPrf := mkApp4 (mkConst ``And.intro) aTy bTy prf (← mkEqRefl out)
    let some (_, pred) := (← whnf goalTy).app2? ``Exists
      | throwError "BigStep did not unfold to an existential"
    let exPrf := mkApp4 (mkConst ``Exists.intro [levelOne]) stTy pred st' andPrf
    g.assign exPrf

end Vsa.While.DeriveTac
