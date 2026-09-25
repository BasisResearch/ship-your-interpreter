import VsaIris.Interp.Steps
import VsaIris.Vsa.AllocTac

/-!
# Driving the interpreter's step table

`ix_run h` runs the interpreter's code symbolically from an `IW … pc R Mt`
goal, the interpreter twin of `sx_run` (`AllocTac.lean`, lane H4). At each PC
literal it tries the step lemmas of that instruction in order — `it_<pc>`
(ALU, store, branch, jump, and a load from OWNED bytes), `itD_<pc>` (a load
from the persistent data view), `itT_<pc>` (a jump-table load), `itO_<pc>` (`snez`/`seqz`) — and keeps the
first whose side conditions `sx_side` closes after `sx_norm`/`sx_mem`. A
branch whose condition `sx_side` refutes is pruned. The run stops at a branch
it cannot decide, at a listed PC (`ix_run h at pc…`: the `jal` of a call), at
a symbolic PC, or after the fuel (default 400 instructions). Undischarged side
conditions and the reached goals are left, side conditions first.

Callers extend `sx_side` with `macro_rules` for the facts of their run (the
values an AST node or a value slot pins).
-/

namespace VsaIris.Sym

open Lean Elab Tactic Meta

theorem mem_accAddrs_iff {a w b : Nat} : b ∈ accAddrs a w ↔ a ≤ b ∧ b < a + w :=
  ⟨of_mem_accAddrs, fun ⟨h1, h2⟩ => by
    have e : a + (b - a) = b := by omega
    rw [← e]; exact mem_accAddrs (by omega)⟩

/-- Byte-set side conditions (`∀ b ∈ accAddrs a w, b ∈ DA` or `S b`), when
the data addresses are a concatenation of `accAddrs` ranges and the owned set
is built from `InExt`: both become interval arithmetic for `omega`. -/
macro_rules
  | `(tactic| sx_side) =>
    `(tactic| (intro b hb; simp only [mem_accAddrs_iff, List.mem_append, VsaIris.InExt] at *; sx_addr))

/-- Store forwarding for `ix_run`: doubleword loads (`Arm.lean` extends it
to word loads). Not `sx_mem`, whose word-load rules (`ldv_lw_miss`) the
allocator's runs need: in an interpreter run a word load off a pointer the
context does not separate from the stack fails its discharge at every step. -/
syntax "ix_mem" : tactic
macro_rules
  | `(tactic| ix_mem) =>
    `(tactic| simp (disch := sx_addr) only [ldv_store_hit, ldv_ld_hit_eq, ldv_ld_miss] at *)

/-- Closed side conditions (a jump-table byte at a literal address is in
`interpRO`). -/
macro_rules
  | `(tactic| sx_side) => `(tactic| decide)

private def hex8 (n : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  String.ofList (List.replicate (8 - s.length) (Char.ofNat 48)) ++ s

/-- The normalizer run after every step and before every side condition:
register lookups, the caller's facts (`using`), store forwarding. -/
def ixNorm (facts : Array Term) (tab : Option (TSyntax `tactic) := none) : TacticM Syntax := do
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

/-- Try `sx_side` (after the normalizers) on a goal; `true` when it closes. -/
def ixTrySide (norm : Syntax) (g : MVarId) : TacticM Bool := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| ($(⟨norm⟩) <;> sx_side))) g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

/-- Close a branch goal `C → IW …` when `sx_side` refutes `C`. -/
def ixTryPrune (norm : Syntax) (g : MVarId) (condFacts : Bool := false) : TacticM Bool := do
  let saved ← saveState
  try
    -- `condFacts`: the caller's facts also rewrite the branch condition itself
    let tac ← if condFacts then
        `(tactic| (intro hc; exfalso; revert hc; (try simp only [VsaIris.Sym.upd_apply, Nat.reduceEqDiff, ite_true, ite_false, ne_eq, Decidable.not_not]); ($(⟨norm⟩) <;> sx_side)))
      else `(tactic| (intro hc; exfalso; ($(⟨norm⟩) <;> (revert hc; sx_side))))
    let gs ← evalTacticAt tac g
    if gs.isEmpty then return true
    saved.restore; return false
  catch _ =>
    saved.restore; return false

/-- The interpreter table's step-lemma prefixes, in the order tried. -/
def ixPrefixes : List String := ["it", "itD", "itT", "itH", "itO"]

/-- The step lemmas of the instruction at `pc`, in the order tried. -/
def ixCandidates (pc : Nat) (pfxs : List String := ixPrefixes) : TacticM (List Name) := do
  let env ← getEnv
  let mk (p : String) := Name.mkStr (Name.mkStr (Name.mkStr .anonymous "VsaIris") "Sym") s!"{p}_{hex8 pc}"
  return (pfxs.map mk).filter env.contains

/-- Apply one candidate: the continuation goals (an `SWP` conclusion) and the
side conditions `sx_side` could not close; `none` when it does not apply. -/
def ixApply (norm : Syntax) (h : Syntax) (g : MVarId) (nm : Name) (strict : Bool) :
    TacticM (Option (List MVarId × List MVarId)) := do
  let saved ← saveState
  try
    let gs ← evalTacticAt (← `(tactic| apply $(mkIdent nm) $(⟨h⟩))) g
    let mut conts : List MVarId := []
    let mut pending : List MVarId := []
    for g in gs do
      let ty ← g.withContext (do instantiateMVars (← g.getType))
      if ← g.withContext (forallTelescopeReducing ty fun _ b => isSWP b) then
        conts := conts ++ [g]
      else if !(← ixTrySide norm g) then
        pending := pending ++ [g]
    if strict && !pending.isEmpty then
      saved.restore; return none
    return some (conts, pending)
  catch _ =>
    saved.restore; return none

/-- One step at a literal PC: the first candidate whose side conditions all
close; failing that, the first candidate that applies, with its side
conditions left pending. -/
def ixStep (norm : Syntax) (h : Syntax) (g : MVarId) (pfxs : List String := ixPrefixes) :
    TacticM (Option (List MVarId × List MVarId)) := do
  let some pc ← g.withContext (do swpPC? (← g.getType)) | return none
  let cands ← ixCandidates pc pfxs
  for nm in cands do
    if let some r ← ixApply norm h g nm true then return some r
  for nm in cands do
    if let some r ← ixApply norm h g nm false then return some r
  return none

/-- `ix_run h`, `ix_run [n] h`, `ix_run h using [e,…]`, `ix_run h at pc…`.
A branch that `sx_side` decides is pruned; an undecided branch is explored on
both sides (each side's goal carries its condition `hc`). -/
syntax "ix_run " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

/-- `ix_run1`: `ix_run` that stops at a branch it cannot decide, leaving both
sides as goals `cond → …` for the script to resolve (H2's proofs). -/
syntax "ix_run1 " ("[" num "] ")? term (" using " "[" term,* "]")? (" at " num+)? : tactic

/-- The driver behind `ix_run` (`explore`) and `ix_run1`. -/
def ixRunCore (explore : Bool) (n : Option (TSyntax `num)) (h : Syntax)
    (fs : Option (Syntax.TSepArray `term ",")) (stops : Option (Array (TSyntax `num)))
    (pfxs : List String := ixPrefixes) (tab : Option (TSyntax `tactic) := none)
    (condFacts : Bool := false) :
    TacticM Unit := do
    let budget := (n.map (·.getNat)).getD 400
    let stopPCs : List Nat := match stops with
      | some ss => ss.toList.map (·.getNat)
      | none => []
    let facts : Array Term := match fs with
      | some fs => fs.getElems
      | none => #[]
    let norm ← ixNorm facts tab
    let mut pending : List MVarId := []
    let mut stuck : List MVarId := []
    let first ← getMainGoal
    -- a start state from a call's return (`BitVec.ofNat 64 (i + 4)`) gets its literal PC
    let first ← do
      let saved ← saveState
      try
        match ← evalTacticAt (← `(tactic| (try simp only [Nat.reduceAdd]))) first with
        | [c'] => pure c'
        | _ => saved.restore; pure first
      catch _ => saved.restore; pure first
    -- a worklist of paths, each with its own step budget
    let mut work : List (MVarId × Nat) := [(first, budget)]
    while !work.isEmpty do
      let (cur, fuel) := work.head!
      work := work.tail!
      if fuel == 0 then stuck := stuck ++ [cur]; continue
      if let some pc ← cur.withContext (do swpPC? (← cur.getType)) then
        if stopPCs.contains pc then stuck := stuck ++ [cur]; continue
      let some (conts, pend) ← ixStep norm h cur pfxs | stuck := stuck ++ [cur]; continue
      pending := pending ++ pend
      match conts with
      | [c] =>
        -- a havoc load's continuation holds for every loaded value
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
        if ← ixTryPrune norm t condFacts then
          let [f'] ← evalTacticAt (← `(tactic| intro hc)) f | stuck := stuck ++ [f]; continue
          work := (f', fuel - 1) :: work
        else if ← ixTryPrune norm f condFacts then
          let [t'] ← evalTacticAt (← `(tactic| intro hc)) t | stuck := stuck ++ [t]; continue
          work := (t', fuel - 1) :: work
        else if !explore then
          stuck := stuck ++ [t, f]
        else
          -- undecided: explore both sides, taken side first
          let [t'] ← evalTacticAt (← `(tactic| intro hc)) t | stuck := stuck ++ [t, f]; continue
          let [f'] ← evalTacticAt (← `(tactic| intro hc)) f | stuck := stuck ++ [t', f]; continue
          work := (t', fuel - 1) :: (f', fuel - 1) :: work
      | cs => stuck := stuck ++ cs
    setGoals (pending ++ stuck)

elab_rules : tactic
  | `(tactic| ix_run $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => ixRunCore true n h fs stops
  | `(tactic| ix_run1 $[[$n]]? $h $[using [$fs,*]]? $[at $stops*]?) => ixRunCore false n h fs stops

end VsaIris.Sym

/-! ## `#ix_seg` / `#ix_piece`: a proof step as its own lemma -/

namespace VsaIris.Sym

open Lean Elab Command Term Meta

/-- Universe metavariables of a proof's library lemmas: any level. -/
private def zeroLevels (e : Expr) : Expr :=
  e.replaceLevel fun l =>
    if l.hasMVar then some (l.replace fun | .mvar _ => some levelZero | _ => none) else none

/-- Run `tac` on `goal` (under the locals `vars`) and add
`declName : ∀ vars, (∀ extras, leftover) → goal`, or `∀ vars, goal` when
nothing is left. `allLocals`: `extras` are every local the script introduced
(a proof piece handing its whole context on); otherwise only those the
leftover mentions (a symbolic run's havoc values). -/
def ixAddPiece (declName : Name) (vars : Array Expr) (goal : Expr) (tac : Syntax)
    (allLocals : Bool) (hidden : Array Expr := #[]) : TermElabM Unit := do
  let g ← mkFreshExprMVar goal
  -- the previous piece's leftovers are not this piece's to use (a `cases` would
  -- otherwise revert them into the proof)
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
  -- each leftover goal becomes a hypothesis `hk_j : ∀ extras, leftover_j`
  let rec abstractAll (i : Nat) (gs : List MVarId) (hks : Array Expr) : TermElabM Unit := do
    match gs with
    | [] => finish hks
    | gf :: rest =>
      let (Tf, extras) ← gf.withContext do
        let Tf ← instantiateMVars (← gf.getType)
        let lctx ← getLCtx
        -- `let` locals (a run's opaque frame) are not handed on
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

/-- The number of a piece's binders before its leftover hypotheses
(`hk_1`, `hk_2`, …). -/
def pieceVars (xs : Array Expr) : MetaM Nat := do
  let mut n := xs.size
  while n > 0 do
    let d ← xs[n - 1]!.fvarId!.getDecl
    if d.userName.toString.startsWith "hk_" then n := n - 1 else break
  return n

/-- `#ix_seg name binders : goal by tac` runs `tac` (an `ix_run`) on `goal`
(an `IW … Q pc R Mt` start state) and defines the theorem
`name : ∀ binders, <end goal> → goal`, whose end goal is the symbolic state
the run reached, quantified over every local the run introduced (havoc-loaded
values, the conditions of the branches it took). A run that stops at a branch
it cannot decide leaves both sides: one hypothesis each. -/
syntax (name := ixSeg) "#ix_seg " ident bracketedBinder* " : " term " by " tacticSeq : command

@[command_elab ixSeg] def elabIxSeg : CommandElab := fun stx => do
  let declName := (← getCurrNamespace) ++ stx[1].getId
  liftTermElabM do
    Term.elabBinders stx[2].getArgs fun vars => do
      let T ← Term.elabType stx[4]
      Term.synthesizeSyntheticMVarsNoPostponing
      ixAddPiece declName vars (← instantiateMVars T) stx[6] true

/-- `#ix_piece name binders : goal by tac` is `#ix_seg` for any proof step:
the leftover goal keeps EVERY local the script introduced.
`#ix_piece name from prev by tac` continues from the (first) leftover of the
piece `prev`: its binders are `prev`'s, its goal `prev`'s leftover;
`from prev at k` continues its `k`-th leftover (a branch `#ix_chain` exports:
another row proves it this way). A long proof is
a chain of pieces (`#ix_chain`), each its own declaration: its own
elaboration budget, and nothing about the intermediate states written by
hand. -/
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
  -- which leftover to continue: the first, or `at k` (an exported branch)
  let k := if stx[4].isNone then 1 else stx[4][1].isNatLit?.getD 1
  liftTermElabM do
    let info ← getConstInfo prev
    forallTelescope info.type fun xs _ => do
      let nv ← pieceVars xs
      let some hk := xs[nv + k - 1]? | throwError "#ix_piece: {prev} has no leftover {k}"
      -- the first leftover's own locals become this piece's binders
      forallTelescope (← inferType hk) fun ys T => do
        ixAddPiece declName (xs.extract 0 nv ++ ys) T stx[6] true (xs.extract nv xs.size)

/-- `#ix_chain name := [p₁, p₂, …]` proves `name` by chaining pieces, each
continuing the previous one's FIRST leftover:
`p₁ xs (fun ys₁ => p₂ xs ys₁ (fun ys₂ => …) e…) e…`. A piece's further
leftovers are exported: they become hypotheses of `name`, each quantified over
the locals the chain introduced before it (another row's proof discharges
them, INTERP_DESIGN.md §6: the branches that leave this row). -/
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
      -- pass 1: the exported leftovers' types, closed over the introduced locals
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
        -- pass 2: the proof
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
