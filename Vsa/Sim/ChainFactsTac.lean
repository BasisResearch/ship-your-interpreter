import Vsa.Sim.DeriveCase
import Vsa.Sim.Code.Eval_expr
import Vsa.Sim.DecodeNF
import Vsa.Sim.TextImage

open Lean Elab Tactic Meta
open LeanRV64DExecutable (Register)

namespace Vsa.Sim

/-- A byte-pin leaf of any body line, from a piece footprint present in memory. -/
theorem bytePinsM_of_text {ps : List TextPiece} {m : Std.ExtHashMap Nat (BitVec 8)}
    (hT : TextIn (piecesText ps) m) {a : MInstr}
    (hb : bytesHasB ps a.pc.toNat [a.b0, a.b1, a.b2, a.b3] = true) : BytePinsM m a :=
  hT.pin4 hb

/-- A byte-pin leaf of any terminator, from a piece footprint present in memory. -/
theorem bytePinsT_of_text {ps : List TextPiece} {m : Std.ExtHashMap Nat (BitVec 8)}
    (hT : TextIn (piecesText ps) m) {t : TInstr}
    (hb : bytesHasB ps t.pc.toNat [t.b0, t.b1, t.b2, t.b3] = true) : BytePinsT m t :=
  hT.pin4 hb

/-- The piece-footprint hypotheses reachable from `h : TextIn T m` by splitting appends and
    unfolding definitions of `T`. -/
partial def cfTextCands (h T : Expr) : MetaM (Array Expr) := do
  let T ← whnfCore (← instantiateMVars T)
  if T.isAppOfArity ``HAppend.hAppend 6 then
    let A := T.getArg! 4
    let B := T.getArg! 5
    let hl ← mkAppOptM ``TextIn.left #[none, A, B, h]
    let hr ← mkAppOptM ``TextIn.right #[none, A, B, h]
    return (← cfTextCands hl A) ++ (← cfTextCands hr B)
  if T.isAppOf ``piecesText then return #[h]
  match ← unfoldDefinition? T with
  | some T' => cfTextCands h T'
  | none => return #[]

/-- Candidates from the hypothesis term: its type is `TextLoaded T m`, `TextIn T m`, or the
    unfolded `∀ p ∈ T, m[p.1]? = some p.2`. -/
def cfHypCands (h : Expr) : MetaM (Array Expr) := do
  let rec go (ty : Expr) (fuel : Nat) : MetaM (Array Expr) := do
    let ty := (← whnfCore (← instantiateMVars ty)).consumeMData
    if ty.getAppNumArgs == 2 then
      if let some c := ty.getAppFn.constName? then
        if c == ``TextIn || c == `VsaIris.Sym.TextLoaded then
          return ← cfTextCands h (ty.getArg! 0)
    match fuel, ← unfoldDefinition? ty with
    | fuel + 1, some ty' => go ty' fuel
    | _, _ => return #[]
  go (← inferType h) 8

private def cfBvLitNat? (e : Expr) : MetaM (Option Nat) := do
  match ← getBitVecValue? e with
  | some ⟨_, v⟩ => return some v.toNat
  | none => return none

private def cfHexName (n : Nat) : String :=
  let s := (Nat.toDigits 16 n).asString
  (String.mk (List.replicate (8 - s.length) '0')) ++ s

private def cfStructField? (a : Expr) (idx : Nat) : Option Expr := a.getAppArgs[idx]?

private def cfLastArg? (ty : Expr) : MetaM (Option Expr) := do
  match ty.getAppArgs.back? with
  | some a => return some (← whnf a)
  | none => return none

/-- Close a byte-pin leaf generically from the piece footprints of `hs`. -/
private def cfClosePinsGeneric (hs : Array Expr) (lem : Name) (g : MVarId) : TacticM Bool := do
  for h in hs do
    let saved ← saveState
    try
      let e ← g.withContext (mkAppM lem #[h])
      let gs ← g.apply e
      let mut ok := true
      for g' in gs do
        let r ← evalTacticAt (← `(tactic| decide)) g'
        unless r.isEmpty do ok := false
      if ok then return true
      saved.restore
    catch _ => saved.restore
  return false

private def cfCloseLeaf (h : Term) (g : MVarId) (ty : Expr) (nm : Nat → String)
    (fieldIdx : Nat) (applyH : Bool) : TacticM Unit := do
  let some a ← cfLastArg? ty | throwError "chain_facts: no instruction literal"
  let some fE := cfStructField? a fieldIdx | throwError "chain_facts: no field {fieldIdx}"
  let some n ← cfBvLitNat? fE | throwError "chain_facts: field not a literal"
  let stx ← if applyH then `($(mkIdent (nm n).toName) $h) else `($(mkIdent (nm n).toName))
  g.assign (← g.withContext (Term.elabTermEnsuringType stx ty))

/-- A decode leaf: `decodeW` computes the instruction of the literal word by `rfl`. -/
private def cfCloseDecode (g : MVarId) (ty : Expr) : TacticM Unit := do
  let stx ← `(fun s h1 h2 h3 => Vsa.Sim.decodeW s h1 h2 h3)
  g.assign (← g.withContext (Term.elabTermEnsuringType stx ty))

private partial def cfSolve (h : Term) (prefixStr : String) (g : MVarId)
    (hs : Array Expr := #[]) : TacticM (List MVarId) := do
  let pinName (pc : Nat) : String := prefixStr ++ cfHexName pc
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  match ty.getAppFn.constName? with
  | some ``And =>
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
      let mut acc : List MVarId := []
      for g' in gs do acc := acc ++ (← cfSolve h prefixStr g' hs)
      return acc
  | some ``BytePinsM =>
      if ← cfClosePinsGeneric hs ``bytePinsM_of_text g then return []
      cfCloseLeaf h g ty pinName 0 true; return []
  | some ``DecodeFactM => cfCloseDecode g ty; return []
  | some ``BytePinsT =>
      if ← cfClosePinsGeneric hs ``bytePinsT_of_text g then return []
      cfCloseLeaf h g ty pinName 0 true; return []
  | some ``DecodeFactT => cfCloseDecode g ty; return []
  | some ``True => g.assign (mkConst ``True.intro); return []
  | some ``ChainFacts | some ``BBlockFacts | some ``ProgFactsM
  | some ``TermPins | some ``TermFactsO =>

      let g' ← g.change (← g.withContext (whnf ty))
      cfSolve h prefixStr g' hs
  | _ =>

      if ← g.withContext (isDefEq ty (mkConst ``True)) then
        g.assign (mkConst ``True.intro); return []
      else
        return [g]

/-- `chain_facts h` closes the code leaves of a `ChainFacts` goal: byte pins from the piece
    footprint of `h` (a `TextLoaded`/`TextIn` hypothesis), decode facts by `decodeW`.
    The optional `with "prefix"` names per-address pin lemmas `prefix<pc>` applied to `h`
    when `h` carries no piece footprint. -/
def chainFactsCore (h : Term) (pstr : String) : TacticM Unit := do
  let g ← getMainGoal
  let hs ← g.withContext do
    try cfHypCands (← Term.elabTerm h none) catch _ => pure #[]
  let leftovers ← cfSolve h pstr g hs
  setGoals leftovers

/-- `chain_facts h` closes the code leaves of a `ChainFacts` goal: byte pins from the piece
    footprint of `h` (a `TextLoaded`/`TextIn` hypothesis), decode facts by `decodeW`.
    With `with "prefix"`, per-address pin lemmas `prefix<pc>` applied to `h` close the byte
    pins that `h` carries no piece footprint for. -/
elab "chain_facts " h:term " with " pfx:str : tactic => chainFactsCore h pfx.getString

@[inherit_doc chainFactsCore]
elab "chain_facts " h:term : tactic => chainFactsCore h ""

end Vsa.Sim
