import VsaIris.Vsa.AllocTac
import VsaIris.Vsa.StepTables.Interp0
import VsaIris.Vsa.StepTables.Interp1
import VsaIris.Vsa.StepTables.Interp2

namespace VsaIris.Sym

open Lean Elab Tactic Meta

theorem mem_accAddrs_iff {a w b : Nat} : b ∈ accAddrs a w ↔ a ≤ b ∧ b < a + w :=
  ⟨of_mem_accAddrs, fun ⟨h1, h2⟩ => by
    have e : a + (b - a) = b := by omega
    rw [← e]; exact mem_accAddrs (by omega)⟩

macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; simp only [mem_accAddrs_iff, List.mem_append, VsaIris.InExt] at *; sx_addr))

syntax "ix_mem" : tactic
macro_rules
  | `(tactic| ix_mem) =>
    `(tactic| simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss] at *)

macro_rules
  | `(tactic| sx_side) => `(tactic| decide)

/-- A constant-table access lies in the interpreter's `.rodata` ranges. -/
macro "ix_ro" : tactic => `(tactic| exact interpRO_mem_img (by decide))

macro_rules
  | `(tactic| sx_side) => `(tactic| ix_ro)

private def hex8 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (8 - s.length) (Char.ofNat 48)) ++ s

def ixNormTab (facts : Array Term) (tab : Option (TSyntax `tactic)) : TacticM Syntax := do
  let tab ← match tab with
    | some t => pure t
    | none => `(tactic| ix_tab)
  let tab : TSyntax ``Lean.Parser.Tactic.tacticSeq ← `(Lean.Parser.Tactic.tacticSeq| $tab:tactic)
  if facts.isEmpty then
    `(tactic| ((try sx_norm) <;> (try $tab) <;> (try sx_norm) <;> (try ix_mem)))
  else
    let lems : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
      facts.mapM fun f => `(Lean.Parser.Tactic.simpLemma| $f:term)
    `(tactic| ((try sx_norm) <;> (try simp only [$lems,*]) <;> (try $tab) <;> (try sx_norm) <;> (try ix_mem)))

def ixNorm (facts : Array Term) : TacticM Syntax := ixNormTab facts none

def ixSide (side : Option Syntax) : TacticM Syntax := do
  match side with
  | some t => pure t
  | none => `(tactic| sx_side)

def ixTrySide (norm : Syntax) (g : MVarId) (side : Option Syntax := none) : TacticM Bool := do
  let saved ← saveState
  let sd ← ixSide side
  try
    let gs ← evalTacticAt (← `(tactic| ($(⟨norm⟩) <;> $(⟨sd⟩)))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

def ixTryPrune (norm : Syntax) (g : MVarId) (side : Option Syntax := none)
    (condFacts : Bool := false) : TacticM Bool := do
  let saved ← saveState
  let sd ← ixSide side
  try

    let tac ← if condFacts then
        `(tactic| (intro hc; exfalso; revert hc; (try simp only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false, ne_eq, Decidable.not_not]); ($(⟨norm⟩) <;> $(⟨sd⟩))))
      else `(tactic| (intro hc; exfalso; ($(⟨norm⟩) <;> (revert hc; $(⟨sd⟩)))))
    let gs ← evalTacticAt tac g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

def ixPre : List String := ["it", "itD", "itT", "itH", "itO", "itS", "itDS", "itTS", "itHS", "itOS"]

def ixCandidates (pc : Nat) (pre : List String := ixPre) :
    TacticM (List Name) := do
  let env ← getEnv
  let mk (p : String) := Name.mkStr (Name.mkStr (Name.mkStr .anonymous "VsaIris") "Sym") s!"{p}_{hex8 pc}"
  return (pre.map mk).filter env.contains

def ixApply (norm : Syntax) (h : Syntax) (g : MVarId) (nm : Name) (strict : Bool)
    (side : Option Syntax := none) : TacticM (Option (List MVarId × List MVarId)) := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| apply $(mkIdent nm) $(⟨h⟩))) g
    let mut conts : List MVarId := []
    let mut pending : List MVarId := []
    for g in gs do
      let ty ← g.withContext (do instantiateMVars (← g.getType))
      if ← g.withContext (forallTelescopeReducing ty fun _ b => isSWP b) then
        conts := conts ++ [g]
      else if !(← ixTrySide norm g side) then
        pending := pending ++ [g]
    if strict && !pending.isEmpty then
      saved.restore; return none
    return some (conts, pending)
  catch _ =>
    saved.restore; return none

def ixStep (norm : Syntax) (h : Syntax) (g : MVarId)
    (pre : List String := ixPre) (side : Option Syntax := none) :
    TacticM (Option (List MVarId × List MVarId)) := do
  let some pc ← g.withContext (do swpPC? (← g.getType)) | return none
  let cands ← ixCandidates pc pre
  -- `IX_TRACE=1` lists the step lemmas a build still uses (one `IXPC <name>` line each)
  let used (nm : Name) : TacticM Unit := do
    if (← IO.getEnv "IX_TRACE").isSome then IO.eprintln s!"IXPC {nm}"
  for nm in cands do
    if let some r ← ixApply norm h g nm true side then used nm; return some r
  for nm in cands do
    if let some r ← ixApply norm h g nm false side then used nm; return some r
  return none

syntax "ix_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

syntax "ix_run1 " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

def ixRunCore (explore : Bool) (n : Option (TSyntax `num)) (h : Syntax)
    (fs : Option (Syntax.TSepArray `term ",")) (stops : Option (Array (TSyntax `num)))
    (pre : List String := ixPre)
    (mkNorm : Array Term → TacticM Syntax := ixNorm) (clearPruned : Bool := false)
    (budgetPct : Nat := 0) (condFacts : Bool := false) :
    TacticM Unit := do
    let budget := (n.map (·.getNat)).getD 400
    let stopPCs : List Nat := match stops with
      | some ss => ss.toList.map (·.getNat)
      | none => []
    let facts : Array Term := match fs with
      | some fs => fs.getElems
      | none => #[]
    let norm ← mkNorm facts
    let mut pending : List MVarId := []
    let mut stuck : List MVarId := []
    let first ← getMainGoal

    let first ← do
      let saved ← saveState
      try
        match ← evalTacticAt (← `(tactic| (try simp only [Nat.reduceAdd]))) first with
        | [c'] => pure c'
        | _ => saved.restore; pure first
      catch _ => saved.restore; pure first

    let mut work : List (MVarId × Nat) := [(first, budget)]
    let ctx ← readThe Core.Context
    while !work.isEmpty do
      let (cur, fuel) := work.head!
      work := work.tail!
      if fuel == 0 then stuck := stuck ++ [cur]; continue

      if budgetPct != 0 && ctx.maxHeartbeats != 0 then
        let used := (← IO.getNumHeartbeats) - ctx.initHeartbeats
        if used * 100 > ctx.maxHeartbeats * budgetPct then stuck := stuck ++ [cur]; continue
      if let some pc ← cur.withContext (do swpPC? (← cur.getType)) then
        if stopPCs.contains pc then stuck := stuck ++ [cur]; continue
      let some (conts, pend) ← ixStep norm h cur pre | stuck := stuck ++ [cur]; continue
      pending := pending ++ pend
      match conts with
      | [c] =>

        let c ← do
          let ty ← c.withContext (do whnfR (← instantiateMVars (← c.getType)))
          if ty.isForall then
            match ← evalTacticAt (← `(tactic| intro _)) c with
            | [c'] => pure c'
            | _ => pure c
          else pure c
        let c ← do
          let saved ← saveState
          try
            match ← evalTacticAt norm c with
            | [c'] => pure c'
            | _ => saved.restore; pure c
          catch _ => saved.restore; pure c
        if (← c.withContext (do swpPC? (← c.getType))).isSome then
          work := (c, fuel - 1) :: work
        else
          stuck := stuck ++ [c]
      | [t, f] =>
        let introTac ← if clearPruned then `(tactic| intro _) else `(tactic| intro hc)
        if ← ixTryPrune norm t none condFacts then
          let [f'] ← evalTacticAt introTac f | stuck := stuck ++ [f]; continue
          work := (f', fuel - 1) :: work
        else if ← ixTryPrune norm f none condFacts then
          let [t'] ← evalTacticAt introTac t | stuck := stuck ++ [t]; continue
          work := (t', fuel - 1) :: work
        else if !explore then
          stuck := stuck ++ [t, f]
        else

          let [t'] ← evalTacticAt (← `(tactic| intro hc)) t | stuck := stuck ++ [t, f]; continue
          let [f'] ← evalTacticAt (← `(tactic| intro hc)) f | stuck := stuck ++ [t', f]; continue
          work := (t', fuel - 1) :: (f', fuel - 1) :: work
      | cs => stuck := stuck ++ cs
    setGoals (pending ++ stuck)

elab_rules : tactic
  | `(tactic| ix_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => ixRunCore true n h fs stops
  | `(tactic| ix_run1 $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => ixRunCore false n h fs stops

end VsaIris.Sym

namespace VsaIris.Sym

open Lean Elab Command Term Meta

private def zeroLevels (e : Expr) : Expr :=
  e.replaceLevel fun l =>
    if l.hasMVar then some (l.replace fun | .mvar _ => some levelZero | _ => none) else none

def ixAddPiece (declName : Name) (vars : Array Expr) (goal : Expr) (tac : Syntax)
    (allLocals : Bool) (hidden : Array Expr := #[]) : TermElabM Unit := do
  let g ← mkFreshExprMVar goal

  let g0 ← g.mvarId!.tryClearMany (hidden.map (·.fvarId!))
  let gs ← withDeclName declName <| Tactic.run g0 (Tactic.evalTactic tac)
  let gs ← gs.filterM fun g => return !(← g.isAssigned)
  let finish (hks : Array Expr) : TermElabM Unit := do
    let val := zeroLevels (← instantiateMVars (← mkLambdaFVars (vars ++ hks) (← instantiateMVars g)))
    let ty := zeroLevels (← instantiateMVars (← mkForallFVars (vars ++ hks) goal))
    if ty.hasMVar || val.hasMVar then
      throwError "#ix_piece: the proof left metavariables"
    if ty.hasFVar || val.hasFVar then
      let fs := (collectFVars {} val).fvarIds ++ (collectFVars {} ty).fvarIds
      let ds ← fs.mapM fun f => do
        match (← getLCtx).find? f with
        | some d => return m!"{d.userName} : {d.type}"
        | none => return m!"{mkFVar f} (not in scope)"
      throwError m!"#ix_piece: the proof mentions locals outside its statement:{indentD (MessageData.joinSep ds.toList "\n")}"
    addDecl (.thmDecl { name := declName, levelParams := [], type := ty, value := val })

  let rec abstractAll (i : Nat) (gs : List MVarId) (hks : Array Expr) : TermElabM Unit := do
    match gs with
    | [] => finish hks
    | gf :: rest =>
      let (Tf, extras) ← gf.withContext do
        let Tf ← instantiateMVars (← gf.getType)
        let lctx ← getLCtx

        let fresh := lctx.foldl (init := #[]) fun acc d =>
          if d.isImplementationDetail || d.isLet || vars.contains (mkFVar d.fvarId) ||
              hidden.contains (mkFVar d.fvarId) || hks.contains (mkFVar d.fvarId) then acc
          else acc.push d.fvarId
        let used := collectFVars {} Tf
        let extras := if allLocals then fresh else fresh.filter used.fvarSet.contains
        let ex := extras.map mkFVar
        return (← mkForallFVars ex Tf, ex)
      withLocalDeclD (.mkSimple s!"hk_{i}") Tf fun hk => do
        gf.assign (mkAppN hk extras)
        abstractAll (i + 1) rest (hks.push hk)
  abstractAll 1 gs #[]

def pieceVars (xs : Array Expr) : MetaM Nat := do
  let mut n := xs.size
  while n > 0 do
    let d ← xs[n - 1]!.fvarId!.getDecl
    if d.userName.toString.startsWith "hk_" then n := n - 1 else break
  return n

syntax (name := ixSeg) "#ix_seg " ident bracketedBinder* " : " term " by " tacticSeq : command

@[command_elab ixSeg] def elabIxSeg : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  liftTermElabM do
    Term.elabBinders stx[2].getArgs fun vars => do
      let T ← Term.elabType stx[4]
      Term.synthesizeSyntheticMVarsNoPostponing
      ixAddPiece declName vars (← instantiateMVars T) stx[6] true

syntax (name := ixPiece) "#ix_piece " ident bracketedBinder* " : " term " by " tacticSeq : command
syntax (name := ixPieceFrom) "#ix_piece " ident " from " ident (" at " num)? " by " tacticSeq : command

@[command_elab ixPiece] def elabIxPiece : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  liftTermElabM do
    Term.elabBinders stx[2].getArgs fun vars => do
      let T ← Term.elabType stx[4]
      Term.synthesizeSyntheticMVarsNoPostponing
      ixAddPiece declName vars (← instantiateMVars T) stx[6] true

@[command_elab ixPieceFrom] def elabIxPieceFrom : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  let prev ← liftCoreM <| realizeGlobalConstNoOverload stx[3]

  let k := if stx[4].isNone then 1 else stx[4][1].isNatLit?.getD 1
  liftTermElabM do
    let info ← getConstInfo prev
    forallTelescope info.type fun xs _ => do
      let nv ← pieceVars xs
      let some hk := xs[nv + k - 1]? | throwError "#ix_piece: {prev} has no leftover {k}"

      forallTelescope (← inferType hk) fun ys T => do
        ixAddPiece declName (xs.extract 0 nv ++ ys) T stx[6] true (xs.extract nv xs.size)

syntax (name := ixChain) "#ix_chain " ident " := " "[" ident,+ "]" : command

@[command_elab ixChain] def elabIxChain : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  let names ← stx[4].getSepArgs.mapM fun n => liftCoreM <| realizeGlobalConstNoOverload n
  liftTermElabM do
    let some first := names[0]? | throwError "#ix_chain: no pieces"
    let info0 ← getConstInfo first
    forallTelescope info0.type fun xs0 goal => do
      let nv ← pieceVars xs0
      let vars := xs0.extract 0 nv

      let rec exports (k : Nat) (acc : Array Expr) : MetaM (Array Expr) := do
        let hs ← forallTelescope (← inferType (mkAppN (Lean.mkConst names[k]!) (vars ++ acc)))
          fun hs _ => hs.mapM inferType
        let mut out := #[]
        for h in hs.extract 1 hs.size do
          out := out.push (← mkForallFVars acc h)
        if k + 1 < names.size then
          let some cont := hs[0]? | throwError "#ix_chain: {names[k]!} has no leftover"
          let rest ← forallTelescope cont fun ys _ => exports (k + 1) (acc ++ ys)
          return out ++ rest
        else
          if !hs.isEmpty then throwError "#ix_chain: the last piece {names[k]!} leaves goals"
          return out
      let exTys ← exports 0 #[]
      let exDecls := exTys.mapIdx fun j t => (Name.mkSimple s!"hx_{j + 1}", fun _ => pure t)
      withLocalDeclsD exDecls fun exs => do

        let rec build (k : Nat) (acc : Array Expr) (j : Nat) : MetaM Expr := do
          let c := mkAppN (Lean.mkConst names[k]!) (vars ++ acc)
          let hs ← forallTelescope (← inferType c) fun hs _ => hs.mapM inferType
          let nex := hs.size - (if k + 1 < names.size then 1 else 0)
          let exArgs := (List.range nex).toArray.map fun t => mkAppN exs[j + t]! acc
          if k + 1 < names.size then
            let rest ← forallTelescope hs[0]! fun ys _ => do
              mkLambdaFVars ys (← build (k + 1) (acc ++ ys) (j + nex))
            return mkAppN (mkApp c rest) exArgs
          else
            return mkAppN c exArgs
        let body ← build 0 #[] 0
        let val := zeroLevels (← instantiateMVars (← mkLambdaFVars (vars ++ exs) body))
        let ty := zeroLevels (← instantiateMVars (← mkForallFVars (vars ++ exs) goal))
        addDecl (.thmDecl { name := declName, levelParams := [], type := ty, value := val })

end VsaIris.Sym
