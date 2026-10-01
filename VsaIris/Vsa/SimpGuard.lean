import VsaIris.Vsa.SimpSets

namespace VsaIris.SimpGuard

open Lean Meta Elab Tactic

register_option simp_set.check : Bool :=
  { defValue := false, descr := "run a skipped `simp_set` anyway and warn if it made progress" }

structure GInfo where
  heads : NameSet := {}
  unfold : NameSet := {}
  always : Bool := false
  thms : SimpTheorems := {}
  procs : Simprocs := {}
  cond : NameSet := {}

def rootHeads {α} (acc : NameSet × Bool) (d : DiscrTree α) : NameSet × Bool :=
  d.root.foldl (init := acc) fun (s, a) k _ => match k with
    | .const n _ => (s.insert n, a)
    | _ => (s, true)

def lhsHead? (thm : SimpTheorem) : MetaM (Option Name) := do
  let ty ← inferType (← thm.getValue)
  forallTelescope ty fun _ b => do
    let b := b.consumeMData
    let l := if let some (_, l, _) := b.eq? then l
      else if let some (l, _) := b.iff? then l
      else if let some p := b.not? then p
      else b
    return l.getAppFn.constName?

/-- Whether the theorem has a hypothesis that a discharger must prove. -/
def conditional (thm : SimpTheorem) : MetaM Bool := do
  forallTelescopeReducing (← inferType (← thm.getValue)) fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isInstImplicit then continue
      if ← isProp d.type then return true
    return false

initialize gCache : IO.Ref (Std.HashMap Name (Nat × GInfo)) ← IO.mkRef {}

def gInfoCore (thms : SimpTheorems) (procs : Simprocs) : MetaM GInfo := do
  let acc := rootHeads ({}, false) thms.pre
  let acc := rootHeads acc thms.post
  let acc := rootHeads acc procs.pre
  let (heads, always) := rootHeads acc procs.post
  let some (heads, cond) ← withoutModifyingState do
      let mut heads := heads
      let mut cond : NameSet := {}
      for t in thms.pre.values ++ thms.post.values do
        match ← observing? (lhsHead? t) with
        | some (some n) => heads := heads.insert n
        | _ => return none
        match ← observing? (conditional t) with
        | some false => pure ()
        | _ => cond := cond.insert t.origin.key
      return some (heads, cond)
    | return { always := true }
  let unfold := thms.toUnfold.fold (init := ({} : NameSet)) fun s n => s.insert n
  let unfold := thms.toUnfoldThms.foldl (init := unfold) fun s n _ => s.insert n
  return { heads, unfold, always, thms, procs, cond }

def gInfo (set : Name) : MetaM GInfo := do
  let some ext ← getSimpExtension? set | throwError "simp_set: unknown simp set {set}"
  let thms ← ext.getTheorems
  let procs ← match ← Simp.getSimprocExtension? set with
    | some e => e.getSimprocs
    | none => pure {}
  let cnt {α} [BEq α] [Hashable α] (h : PersistentHashSet α) : Nat := h.fold (init := 0) fun n _ => n + 1
  let stamp := cnt thms.lemmaNames + cnt thms.toUnfold + cnt procs.simprocNames
  if let some (st, g) := (← gCache.get)[set]? then
    if st == stamp then return { g with thms, procs }
  let g ← gInfoCore thms procs
  gCache.modify (·.insert set (stamp, g))
  return g

def GInfo.hitHead (g : GInfo) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => g.heads.contains n || g.unfold.contains n
  | _ => false

/-- A subterm on which `simp`'s own reduction steps (beta, zeta, projections, matchers and
recursors, folding a raw literal) may act. -/
def reducible? (env : Environment) (e : Expr) : Bool :=
  match e with
  | .letE .. | .proj .. | .lit (.natVal _) => true
  | .app .. =>
    let f := e.getAppFn
    f.isHeadBetaTargetFn false || match f with
      | .const n _ => env.isProjectionFn n || isMatcherCore env n || isAuxRecursor env n ||
          isNoConfusion env n || match env.find? n with
            | some (.recInfo _) | some (.quotInfo _) => true
            | _ => false
      | _ => false
  | _ => false

def GInfo.hit (g : GInfo) (env : Environment) (e : Expr) : Bool :=
  g.hitHead e || reducible? env e

def builtinFires (e : Expr) : MetaM Bool := withReducible do
  try
    match e with
    | .letE .. | .lit (.natVal _) => return true
    | .proj .. => return (← reduceProj? e).isSome
    | .app .. =>
      let f := e.getAppFn
      if f.isHeadBetaTargetFn false then return true
      if let .const n _ := f then
        if let some info ← getProjectionFnInfo? n then
          if let some m := e.getAppArgs[info.numParams]? then
            if ← isConstructorApp (← whnfR m) then return true
        if (← reduceRecMatcher? e).isSome then return true
      return false
    | _ => return false
  catch _ => return true

def stepChanges (e : Expr) : Simp.Step → Bool
  | .done r | .visit r | .continue (some r) => r.expr != e
  | .continue none => false

def dstepChanges (e : Expr) : TransformStep → Bool
  | .done e' | .visit e' | .continue (some e') => e' != e
  | .continue none => false

def thmFires (cond : NameSet) (e : Expr) (thm : SimpTheorem) (extra : Nat) : SimpM Bool := do
  if extra != 0 || cond.contains thm.origin.key then return true
  try
    if let some r ← Simp.tryTheorem? e thm then
      return r.expr != e
    return false
  catch _ => return true

def procFires (e : Expr) (p : Simp.SimprocEntry) (extra : Nat) : SimpM Bool := do
  if extra != 0 then return true
  try
    match p.proc with
    | .inl f => return stepChanges e (← f e)
    | .inr f => return dstepChanges e (← f e)
  catch _ => return true

def GInfo.matches (g : GInfo) (e : Expr) : SimpM Bool := do
  if let .const n _ := e.getAppFn then
    if g.unfold.contains n then return true
  if e.hasLooseBVars then return true
  for (t, k) in (← g.thms.post.getMatchWithExtra e) ++ (← g.thms.pre.getMatchWithExtra e) do
    if ← thmFires g.cond e t k then return true
  for (p, k) in (← g.procs.post.getMatchWithExtra e) ++ (← g.procs.pre.getMatchWithExtra e) do
    if ← procFires e p k then return true
  return false

partial def GInfo.visit (g : GInfo) (env : Environment) (e : Expr) :
    StateT (Std.HashSet Expr) SimpM Bool := do
  if (← get).contains e then return false
  modify (·.insert e)
  if reducible? env e then
    if ← builtinFires e then return true
  if g.hitHead e then
    if ← g.matches e then return true
  if e.isAppOf ``OfNat.ofNat || e.isAppOf ``instOfNatNat then return false
  match e with
  | .app f a => if ← g.visit env f then return true else g.visit env a
  | .lam n t b bi | .forallE n t b bi =>
    if ← g.visit env t then return true
    if (b.find? (g.hit env)).isNone then return false
    withLocalDecl n bi t fun x => g.visit env (b.instantiate1 x)
  | .letE n t v b _ =>
    if ← g.visit env t then return true
    if ← g.visit env v then return true
    if (b.find? (g.hit env)).isNone then return false
    withLetDecl n t v fun x => g.visit env (b.instantiate1 x)
  | .mdata _ b | .proj _ _ b => g.visit env b
  | _ => return false

/-- Whether some rule of the set may rewrite somewhere in `es`: a subterm whose head is a head
symbol of the set's rules (or a constant it unfolds), which the set's discrimination trees match
and on which the matched simproc changes the term or the matched theorem rewrites (a theorem
with hypotheses counts as rewriting). -/
def GInfo.mayFire (g : GInfo) (loc : Option Expr × Array Expr) : MetaM Bool := do
  if g.always then return true
  let tgt? ← loc.1.mapM instantiateMVars
  let hyps ← loc.2.mapM instantiateMVars
  if tgt?.any (·.isTrue) || hyps.any (·.isFalse) then return true
  let es := tgt?.toArray ++ hyps
  let env ← getEnv
  unless es.any (fun e => (e.find? (g.hit env)).isSome) do return false
  let ctx ← Simp.mkContext {} #[g.thms] (← getSimpCongrTheorems)
  withoutModifyingState do
    let (r, _) ← Simp.SimpM.run ctx {} {} do
      let mut seen : Std.HashSet Expr := {}
      for e in es do
        if (e.find? (g.hit env)).isNone then continue
        let (r, s) ← (g.visit env e).run seen
        if r then return true
        seen := s
      return false
    return r

def guardExprs (loc : Syntax) : TacticM (Option Expr × Array Expr) := withMainContext do
  let g ← getMainGoal
  let tgt ← g.getType
  if loc.isNone then return (some tgt, #[])
  match expandLocation loc[0] with
  | .wildcard =>
    let mut out := #[]
    for fv in ← g.getNondepPropHyps do
      out := out.push (← fv.getType)
    return (some tgt, out)
  | .targets hyps type =>
    let mut out := #[]
    for h in hyps do
      let fv ← getFVarId h
      out := out.push (← fv.getType)
    return (if type then some tgt else none, out)

def logStat (set : Name) (fire : Bool) (ns : Nat) : IO Unit := do
  let some path ← IO.getEnv "SIMPSET_OUT" | return
  let h ← IO.FS.Handle.mk path .append
  h.putStrLn s!"{set}\t{if fire then 1 else 0}\t{ns.toFloat / 1e6}"

syntax (name := simpSetTac) "simp_set " (Lean.Parser.Tactic.discharger)? ident (Lean.Parser.Tactic.location)? : tactic

@[tactic simpSetTac] def evalSimpSet : Tactic := fun stx => do
  let disch := stx[1]
  let set := stx[2].getId.eraseMacroScopes
  let loc := stx[3]
  let t0 ← IO.monoNanosNow
  let gi ← try gInfo set catch _ => pure { always := true }
  let fire ← withMainContext do
    try gi.mayFire (← guardExprs loc) catch _ => pure true
  let t1 ← IO.monoNanosNow
  logStat set fire (t1 - t0)
  let id := mkIdent set
  let tac ← match disch.isNone, loc.isNone with
    | true, true => `(tactic| simp only [$id:ident])
    | true, false => `(tactic| simp only [$id:ident] $(⟨loc[0]⟩))
    | false, true => `(tactic| simp $(⟨disch[0]⟩):discharger only [$id:ident])
    | false, false => `(tactic| simp $(⟨disch[0]⟩):discharger only [$id:ident] $(⟨loc[0]⟩))
  if fire then
    evalTactic tac
  else if simp_set.check.get (← getOptions) || (← IO.getEnv "SIMPSET_CHECK").isSome then
    let s ← saveState
    try
      evalTactic tac
      let detail ← withoutModifyingState <| s.restore *> withMainContext do
        let ctx ← Simp.mkContext {} #[gi.thms] (← getSimpCongrTheorems)
        let mut out : MessageData := m!""
        let (t?, hs) ← guardExprs loc
        for e in t?.toArray ++ hs do
          let e ← instantiateMVars e
          let (r, st) ← Simp.main e ctx (methods := Simp.mkDefaultMethodsCore #[gi.procs])
          if r.expr != e then
            let used := st.usedTheorems.map.toList.map (·.1.key)
            out := out ++ m!"\n  in: {e}\n  used: {used}"
        return out
      logWarning m!"simp_set: guard skipped {set} but it made progress{detail}"
    catch _ =>
      s.restore
      throwError "simp_set: no rule of {set} applies"
  else
    throwError "simp_set: no rule of {set} applies"

end VsaIris.SimpGuard
