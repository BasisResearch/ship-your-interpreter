import Vsa.Sim.DeriveCase
import Vsa.Sim.Code.Eval_expr
import Vsa.Sim.DecodeNF

open Lean Elab Tactic Meta
open LeanRV64DExecutable (Register)

namespace Vsa.Sim

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

private partial def cfSolve (h : Term) (prefixStr : String) (g : MVarId) :
    TacticM (List MVarId) := do
  let pinName (pc : Nat) : String := prefixStr ++ cfHexName pc
  let ty := (← instantiateMVars (← g.getType)).consumeMData
  match ty.getAppFn.constName? with
  | some ``And =>
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
      let mut acc : List MVarId := []
      for g' in gs do acc := acc ++ (← cfSolve h prefixStr g')
      return acc
  | some ``BytePinsM => cfCloseLeaf h g ty pinName 0 true; return []
  | some ``DecodeFactM => cfCloseDecode g ty; return []
  | some ``BytePinsT => cfCloseLeaf h g ty pinName 0 true; return []
  | some ``DecodeFactT => cfCloseDecode g ty; return []
  | some ``True => g.assign (mkConst ``True.intro); return []
  | some ``ChainFacts | some ``BBlockFacts | some ``ProgFactsM
  | some ``TermPins | some ``TermFactsO =>

      let g' ← g.change (← g.withContext (whnf ty))
      cfSolve h prefixStr g'
  | _ =>

      if ← g.withContext (isDefEq ty (mkConst ``True)) then
        g.assign (mkConst ``True.intro); return []
      else
        return [g]

elab "chain_facts " h:term " with " pfx:str : tactic => do
  let leftovers ← cfSolve h pfx.getString (← getMainGoal)
  setGoals leftovers

end Vsa.Sim
