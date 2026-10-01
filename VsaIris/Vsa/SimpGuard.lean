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

def gInfo (set : Name) : MetaM GInfo := do
  let some ext ← getSimpExtension? set | throwError "simp_set: unknown simp set {set}"
  let thms ← ext.getTheorems
  let procs ← match ← Simp.getSimprocExtension? set with
    | some e => e.getSimprocs
    | none => pure {}
  let acc := rootHeads ({}, false) thms.pre
  let acc := rootHeads acc thms.post
  let acc := rootHeads acc procs.pre
  let (heads, always) := rootHeads acc procs.post
  let some heads ← withoutModifyingState do
      let mut heads := heads
      for t in thms.pre.values ++ thms.post.values do
        match ← observing? (lhsHead? t) with
        | some (some n) => heads := heads.insert n
        | _ => return none
      return some heads
    | return { always := true }
  let unfold := thms.toUnfold.fold (init := ({} : NameSet)) fun s n => s.insert n
  let unfold := thms.toUnfoldThms.foldl (init := unfold) fun s n _ => s.insert n
  return { heads, unfold, always, thms, procs }

def GInfo.hit (g : GInfo) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => g.heads.contains n || g.unfold.contains n
  | _ => false

def GInfo.matches (g : GInfo) (e : Expr) : MetaM Bool := do
  if let .const n _ := e.getAppFn then
    if g.unfold.contains n then return true
  if e.hasLooseBVars then return true
  if !(← g.thms.post.getMatchWithExtra e).isEmpty then return true
  if !(← g.thms.pre.getMatchWithExtra e).isEmpty then return true
  if !(← g.procs.post.getMatchWithExtra e).isEmpty then return true
  if !(← g.procs.pre.getMatchWithExtra e).isEmpty then return true
  return false

partial def GInfo.visit (g : GInfo) (e : Expr) : StateT (Std.HashSet Expr) MetaM Bool := do
  if (← get).contains e then return false
  modify (·.insert e)
  if g.hit e then
    if ← g.matches e then return true
  match e with
  | .app f a => if ← g.visit f then return true else g.visit a
  | .lam _ t b _ | .forallE _ t b _ => if ← g.visit t then return true else g.visit b
  | .letE _ t v b _ =>
    if ← g.visit t then return true
    if ← g.visit v then return true
    g.visit b
  | .mdata _ b | .proj _ _ b => g.visit b
  | _ => return false

/-- Whether some rule of the set may rewrite somewhere in `es`: a subterm whose head is a root
symbol of the set's discrimination trees (or a constant it unfolds) and which the trees match. -/
def GInfo.mayFire (g : GInfo) (es : Array Expr) : MetaM Bool := do
  if g.always then return true
  let es ← es.mapM instantiateMVars
  unless es.any (fun e => (e.find? g.hit).isSome) do return false
  let mut seen : Std.HashSet Expr := {}
  for e in es do
    let (r, s) ← (g.visit e).run seen
    if r then return true
    seen := s
  return false

def guardExprs (loc : Syntax) : TacticM (Array Expr) := withMainContext do
  let g ← getMainGoal
  let tgt ← g.getType
  if loc.isNone then return #[tgt]
  match expandLocation loc[0] with
  | .wildcard =>
    let mut out := #[tgt]
    for d in ← getLCtx do
      if !d.isImplementationDetail then out := out.push d.type
    return out
  | .targets hyps type =>
    let mut out := if type then #[tgt] else #[]
    for h in hyps do
      let fv ← getFVarId h
      out := out.push (← fv.getType)
    return out

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
      logWarning m!"simp_set: guard skipped {set} but it made progress"
    catch _ =>
      s.restore
      throwError "simp_set: no rule of {set} applies"
  else
    throwError "simp_set: no rule of {set} applies"

end VsaIris.SimpGuard
