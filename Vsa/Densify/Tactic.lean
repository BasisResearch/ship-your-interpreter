import Vsa.Densify.Resp

/-!
# The `resp_auto` tactic

Discharges `Resp (f args)` / `RespE (f args)` for a model function whose body
has been unfolded. `resp_step` looks at the head symbol of the computation and
applies the one matching rule: bind, pure, lift, throw, early-return blocks,
fuel and `for` loops, `if` (syntactically, keeping the condition as a
hypothesis), `match` (reduced on a constructor, `split` otherwise), `do` join
points (`have jp := fun r => k r; body`: `k` is proved ONCE and the body gets
the hypothesis `∀ r, Resp (jp r)`, never inlined: inlining is exponential in
the nesting depth), pure `have`/`let`s (inlined), the literal-pattern casts,
compiled case splits, and calls to already-proved functions (their lemmas
resolved by name: `Gen`, `RecMutual`, `RecPt`, `PS`, or the explicit list;
induction hypotheses by `assumption`/`apply`). `resp_auto` is a flat,
bounded loop of `resp_step` over every open goal, setting a goal aside after
its first failure.

Nothing here traverses a term: the 330-alternative CSR tables (and every
literal-pattern matcher) are unfolded head-only (`delta?` + beta) and their
`dite` chains split by a syntactic step that builds the proof term directly,
so no elaboration limit is raised.
-/

namespace Vsa.Densify

open Lean Meta Elab Tactic

/-- The computation under `Resp`/`RespE` in the goal, with the goal's head and
arguments (the computation is the last argument). -/
def respGoal (goal : MVarId) : MetaM (Expr × Array Expr × Expr) := do
  let t ← goal.getType
  let t ← if t.hasMVar then instantiateMVars t else pure t
  let fn := t.getAppFn
  let args := t.getAppArgs
  unless (fn.isConstOf ``Vsa.Densify.Resp && args.size == 2) ||
      (fn.isConstOf ``Vsa.Densify.RespE && args.size == 3) do
    throwError "not a Resp/RespE goal"
  return (fn, args, args.back!)

/-- A matcher whose alternatives are selected by decidable equality only (string,
bit-vector or numeral literals): its expansion is a `dite` chain with no
`casesOn`/`rec`. -/
def isLiteralMatcher (env : Environment) (c : Name) : Bool :=
  let isCases (n : Name) : Bool :=
    match n with
    | .str _ s => s == "rec" || s == "casesOn" || s.startsWith "_sparseCasesOn" || s.startsWith "rec_"
    | _ => false
  match env.find? c with
  | some ci => !(((ci.value?.map (·.getUsedConstants)).getD #[]).any isCases)
  | none => false

/-- Delta-reduce the head of the computation when it is a matcher on string or
bit-vector literals (the CSR name and number tables, hundreds of alternatives):
`split` and `dsimp` overflow on them, and so does any traversal of the
expanded `dite` chain, so only the head is unfolded (`delta?`) and beta-reduced. -/
def deltaHeadMatcher (goal : MVarId) : MetaM MVarId := goal.withContext do
  let (fn, args, x) ← respGoal goal
  let env ← getEnv
  let some c := x.getAppFn.constName? | throwError "delta_head_matcher: no head constant"
  let some mi := Match.Extension.getMatcherInfo? env c
    | throwError "delta_head_matcher: not a matcher"
  unless mi.numAlts ≥ 4 do throwError "delta_head_matcher: small matcher"
  unless isLiteralMatcher env c do throwError "delta_head_matcher: constructor patterns"
  let some x' ← delta? x (fun n => n == c) | throwError "delta_head_matcher: delta failed"
  goal.replaceTargetDefEq (mkAppN fn (args.set! (args.size - 1) x'.headBeta))

/-- `Resp (dite c t e)` / `Resp (ite c t e)` (and `RespE`) by `Resp.dite` /
`Resp.ite_h`, building the proof term and the two goals syntactically (bound
variable, no abstraction, no `simp`): nothing traverses the `else` chain. -/
def respDiteHead (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  let (fn, args, x) ← respGoal goal
  let isD := x.isAppOfArity ``dite 5
  unless isD || x.isAppOfArity ``ite 5 do throwError "resp_dite_head: not an if"
  let xargs := x.getAppArgs
  let c := xargs[1]!; let inst := xargs[2]!; let tt := xargs[3]!; let ee := xargs[4]!
  let isR := fn.isConstOf ``Vsa.Densify.Resp
  let mkGoal (dom : Expr) (f : Expr) : Expr :=
    let body := if isD then mkApp f (.bvar 0) else f
    mkForall `h .default dom (mkAppN fn (args.set! (args.size - 1) body))
  let g1 ← mkFreshExprMVar (mkGoal c tt)
  let g2 ← mkFreshExprMVar (mkGoal (mkNot c) ee)
  let lem := if isD then (if isR then ``Vsa.Densify.Resp.dite else ``Vsa.Densify.RespE.dite)
    else (if isR then ``Vsa.Densify.Resp.ite_h else ``Vsa.Densify.RespE.ite_h)
  goal.assign (mkAppN (mkConst lem) (args.pop ++ #[c, inst, tt, ee, g1, g2]))
  return [g1.mvarId!, g2.mvarId!]

/-- One shallow reduction at the head of the computation: a `have`/`let` join
point is inlined, a beta-redex is reduced. Never traverses the term. -/
def headZeta (goal : MVarId) : MetaM MVarId := goal.withContext do
  let (fn, args, x) ← respGoal goal
  let x' ← (do
    if x.isLet then return x.letBody!.instantiate1 x.letValue!
    if x.isAppOfArity ``letFun 4 then
      let a := x.getAppArgs
      return a[3]!.beta #[a[2]!]
    if x.isHeadBetaTarget then return x.headBeta
    throwError "head_zeta: nothing to reduce")
  goal.replaceTargetDefEq (mkAppN fn (args.set! (args.size - 1) x'))

elab "delta_head_matcher" : tactic => do
  let g ← deltaHeadMatcher (← getMainGoal); replaceMainGoal [g]
elab "resp_dite_head" : tactic => do
  let gs ← respDiteHead (← getMainGoal); replaceMainGoal gs
elab "head_zeta" : tactic => do
  let g ← headZeta (← getMainGoal); replaceMainGoal [g]

/-- The lemma proving `Resp (f …)` for a model or lean-sail function, by the
generator's naming convention (`scripts/gen_resp.py`). -/
def lemmaFor (env : Environment) (c : Name) : Option Name :=
  let s := c.toString
  let strip (pre : String) (s : String) : String := if s.startsWith pre then (s.drop pre.length).toString else s
  let base := (strip "Functions." (strip "LeanRV64DExecutable." (strip "Sail.ConcurrencyInterfaceV1.PreSail." s)))
  let base := (base.replace "." "_") ++ "_resp"
  let cands := [`Vsa.Densify.Gen ++ base.toName, `Vsa.Densify.RecMutual ++ base.toName,
    `Vsa.Densify.RecPt ++ base.toName, `Vsa.Densify.PS ++ base.toName]
  cands.find? env.contains

/-- Rules keyed by the head constant of the computation. -/
def headRules : List (Name × Name × Name) :=   -- head, lemma for Resp, lemma for RespE
  [(``Bind.bind, ``Resp.bind, ``RespE.bind),
   (``Pure.pure, ``Resp.pure, ``RespE.pure),
   (``Eq.ndrec_symm, ``Resp.ndrec_symm, ``RespE.ndrec_symm),
   (``liftM, ``RespE.lift, ``RespE.lift),
   (``LeanRV64DExecutable.SailME.run, ``Resp.runME, ``Resp.runME),
   (``LeanRV64DExecutable.SailME.throw, ``RespE.throw, ``RespE.throw),
   (``MonadExcept.throw, ``Resp.throw, ``RespE.throwL),
   (``untilFuelM, ``Resp.untilFuelM, ``RespE.untilFuelM),
   (``forIn, ``Resp.forIn_range, ``RespE.forIn_range),
   (``Functor.map, ``Resp.map, ``Resp.map),
   (``SeqRight.seqRight, ``Resp.seqRight, ``Resp.seqRight),
   (``Sail.ConcurrencyInterfaceV1.PreSail.sailTryCatch, ``PS.sailTryCatch_resp, ``PS.sailTryCatch_resp)]

/-- `with_reducible apply n`, without going through syntax. -/
def applyLemma (n : Name) : TacticM Unit := do
  let goal ← getMainGoal
  let gs ← withReducible (goal.apply (← mkConstWithFreshMVarLevels n))
  replaceMainGoal gs

/-- Is `x` a `let`-bound monadic function of at most two arguments (a `do`
join point)? Its arity, if so. -/
def joinPointArity (x : Expr) : MetaM (Option Nat) := do
  unless x.isLet do return none
  let (n, mon) ← forallTelescope (← inferType x.letValue!) fun xs b => do
    let h := b.getAppFn.constName?.getD .anonymous
    pure (xs.size, h == ``LeanRV64DExecutable.SailM || h == ``LeanRV64DExecutable.SailME ||
      h == ``Sail.ConcurrencyInterfaceV1.PreSailM || h == ``Sail.ConcurrencyInterfaceV1.PreSailME ||
      h == ``EStateM || h == ``ExceptT)
  return if mon && n ≤ 2 then some n else none

/-- One step of `resp_auto` on the main goal. -/
def respStep (extra : Array Name) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let t ← goal.getType
  let t ← if t.hasMVar then instantiateMVars t else pure t
  if t.isForall then
    let (_, g) ← goal.intro1P
    replaceMainGoal [g]; return
  unless t.getAppFn.isConstOf ``Vsa.Densify.Resp || t.getAppFn.isConstOf ``Vsa.Densify.RespE do
    -- a side goal of a cast rule (`a = "misa"`): it is a hypothesis
    evalTactic (← `(tactic| with_reducible assumption)); return
  let (fn, _, x) ← respGoal goal
  let isE := fn.isConstOf ``Vsa.Densify.RespE
  -- a monadic join point (`have jp := fun r => k r; body`, a non-dependent `let`):
  -- restate it as `letFun` and prove it once
  if let some n ← joinPointArity x then
    let v := x.letValue!
    let vty ← inferType v
    let (fn, args, _) ← respGoal goal
    let xty ← inferType x
    let x' := mkApp4 (mkConst ``letFun [levelOne, levelOne]) vty (mkLambda `_ .default vty xty) v
      (mkLambda x.letName! .default x.letType! x.letBody!)
    let goal' ← goal.replaceTargetDefEq (mkAppN fn (args.set! (args.size - 1) x'))
    replaceMainGoal [goal']
    let lem := match n, isE with
      | 0, false => ``Resp.letFun0 | 1, false => ``Resp.letFun1 | _, false => ``Resp.letFun2
      | 0, true => ``RespE.letFun0 | 1, true => ``RespE.letFun1 | _, true => ``RespE.letFun2
    applyLemma lem; return
  -- pure join points, values, beta-redexes (all the consecutive ones at once, stopping
  -- at a monadic join point)
  if x.isLet || x.isAppOfArity ``letFun 4 || x.isHeadBetaTarget then
    let mut g ← headZeta goal
    for _ in [0:64] do
      let (_, _, y) ← respGoal g
      if (← joinPointArity y).isSome then break
      match ← (try some <$> headZeta g catch _ => pure none) with
      | some g' => g := g'
      | none => break
    replaceMainGoal [g]; return
  let env ← getEnv
  match x.getAppFn.constName? with
  | some c =>
    if c == ``dite || c == ``ite then replaceMainGoal (← respDiteHead goal); return
    if c == ``panic then
      try applyLemma ``Resp.panic; return catch _ => pure ()
      applyLemma ``Resp.panic_fun; return
    if let some (_, lr, le) := headRules.find? (·.1 == c) then
      applyLemma (if isE then le else lr); return
    if let some mi := Match.Extension.getMatcherInfo? env c then
      if mi.numAlts ≥ 4 && isLiteralMatcher env c then
        replaceMainGoal [← deltaHeadMatcher goal]; return
      -- constructor discriminants reduce (no `whnf` on symbolic ones); otherwise split
      let xargs := x.getAppArgs
      let discrs := (List.range mi.numDiscrs).map fun i => xargs[mi.numParams + 1 + i]!
      if ← discrs.allM (fun d => (Meta.isConstructorApp d : MetaM Bool)) then
        if let .reduced x' ← reduceMatcher? x then
          let (fn, args, _) ← respGoal goal
          replaceMainGoal [← goal.replaceTargetDefEq (mkAppN fn (args.set! (args.size - 1) x'))]
          return
      evalTactic (← `(tactic| split)); return
    -- a compiled case split (`casesOn`, `_sparseCasesOn_n`): on a constructor, unfold and
    -- iota-reduce; on a variable, case on it
    if (match c with | .str _ s => s == "casesOn" || s.startsWith "_sparseCasesOn" | _ => false) then
      let (fn, args, _) ← respGoal goal
      if let some x' ← delta? x (fun n => n == c) then
        let x'' ← whnfCore x'
        if x'' != x' then
          replaceMainGoal [← goal.replaceTargetDefEq (mkAppN fn (args.set! (args.size - 1) x''))]
          return
      if let some d := x.getAppArgs.find? (·.isFVar) then
        let subgoals ← goal.cases d.fvarId!
        replaceMainGoal (subgoals.map (·.mvarId)).toList
        return
    if let some l := lemmaFor env c then
      try applyLemma l; return catch _ => pure ()
  | none => pure ()
  for l in extra do
    try evalTactic (← `(tactic| with_reducible apply $(mkIdent l))); return catch _ => pure ()
  -- an excluded constructor of a case split (`h : C = C → False`)
  try evalTactic (← `(tactic| exact absurd rfl ‹_›)); return catch _ => pure ()
  -- an impossible arm of a split (`heq : C₁ = C₂`, distinct constructors)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if let some (_, a, b) := d.type.eq? then
      if let some ca ← (Meta.isConstructorApp? a : MetaM _) then
        if let some cb ← (Meta.isConstructorApp? b : MetaM _) then
          if ca.name != cb.name then
            evalTactic (← `(tactic| contradiction)); return
  -- an induction hypothesis, possibly universally quantified
  if ← withReducible goal.assumptionCore then replaceMainGoal []; return
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ok ← forallTelescope d.type fun _ b =>
      pure (b.getAppFn.isConstOf ``Vsa.Densify.Resp || b.getAppFn.isConstOf ``Vsa.Densify.RespE)
    if ok then
      try
        let gs ← withReducible (goal.apply (mkFVar d.fvarId))
        replaceMainGoal gs; return
      catch _ => pure ()
  try evalTactic (← `(tactic| split)); return catch _ => pure ()
  try evalTactic (← `(tactic| dsimp only)); return catch _ => pure ()
  if isE then evalTactic (← `(tactic| apply RespE.of_resp)); return
  throwError "resp_step: no rule for {x.getAppFn}"

syntax "resp_step" (" [" ident,* "]")? : tactic
syntax "resp_auto" (" [" ident,* "]")? : tactic

elab_rules : tactic
  | `(tactic| resp_step) => respStep #[]
  | `(tactic| resp_step [$ls,*]) => respStep (ls.getElems.map (·.getId.eraseMacroScopes))

/-- A flat, bounded loop: every round applies one `resp_step` to every open
goal. A goal on which the step fails is set aside (a step is a function of the
goal, so retrying cannot help); it is reported at the end. -/
elab_rules : tactic
  | `(tactic| resp_auto) => do evalTactic (← `(tactic| resp_auto []))
  | `(tactic| resp_auto [$ls,*]) => do
    let extra := ls.getElems.map (·.getId.eraseMacroScopes)
    let mut stuck : Array MVarId := #[]
    for _ in [0:4000] do
      let gs ← getGoals
      if gs.isEmpty then break
      let mut newGoals : Array MVarId := #[]
      for g in gs do
        setGoals [g]
        let saved ← saveState
        try
          respStep extra
          newGoals := newGoals ++ (← getGoals).toArray
        catch _ =>
          saved.restore
          stuck := stuck.push g
      setGoals newGoals.toList
    setGoals ((← getGoals) ++ stuck.toList)

end Vsa.Densify
