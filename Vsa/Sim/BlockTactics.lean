import Vsa.Sim.BlockTerm

/-!
# `block_facts` — auto-discharge the mechanical half of `BBlockFacts`

The `BBlockFacts` bundle a `bblock_sound_bt` application needs is half
mechanical and half data-dependent. The mechanical half is a pure function of
each instruction's `pc`/`word`: the four code-byte pins come from
`Code.<fn>_at_<pc> h`, the decode from `DecodeTable.decode_<word>`.

`block_facts h with "<prefix>"` walks the goal, closes every
`BytePinsM`/`DecodeFactM`/`BytePinsT`/`DecodeFactT`/`True` leaf by generating and
applying those lemmas from the instruction literal, and leaves the
data-dependent leaves (`MemFacts`, terminator guards) as fresh goals in program
order. No search: each closed leaf is one named `exact`.
-/

open Lean Elab Tactic Meta

namespace Vsa.Sim

/-- `Nat` payload of a `BitVec` literal expression, via Lean's own evaluator. -/
private def bvLitNat? (e : Expr) : MetaM (Option Nat) := do
  match ← getBitVecValue? e with
  | some ⟨_, v⟩ => return some v.toNat
  | none => return none

/-- Lowercase hex (no `0x`), zero-padded to 8 digits — the form the generated
`Code.*_at_<pc>` / `DecodeTable.decode_<word>` lemma names use. -/
private def hexName (n : Nat) : String :=
  let s := (Nat.toDigits 16 n).asString
  (String.mk (List.replicate (8 - s.length) '0')) ++ s

/-- Field `idx` (0 = pc, 1 = word) of a reduced `MInstr`/`TInstr` `.mk` literal. -/
private def structField? (a : Expr) (idx : Nat) : Option Expr := a.getAppArgs[idx]?

/-- The instruction literal is the last explicit arg of the leaf predicate. -/
private def lastArg? (ty : Expr) : MetaM (Option Expr) := do
  match ty.getAppArgs.back? with
  | some a => return some (← whnf a)
  | none => return none

/-- Close one `BytePins*`/`DecodeFact*` leaf `g` by generating the lemma name
from the instruction literal's `pc`/`word` field. -/
private def closeLeaf (h : Term) (g : MVarId) (ty : Expr) (nm : Nat → String)
    (fieldIdx : Nat) (applyH : Bool) : TacticM Unit := do
  let some a ← lastArg? ty | throwError "block_facts: no instruction literal"
  let some fE := structField? a fieldIdx | throwError "block_facts: no field {fieldIdx}"
  let some n ← bvLitNat? fE | throwError "block_facts: field not a literal"
  let stx ← if applyH then `($(mkIdent (nm n).toName) $h) else `($(mkIdent (nm n).toName))
  g.assign (← g.withContext (Term.elabTermEnsuringType stx ty))

/-- Walk a `BBlockFacts` goal `g`: reduce container layers
(`BBlockFacts`/`ProgFactsM`/`TermPins`/`TermFactsO`) with `whnf` (which unfolds
the concrete block + the list recursion but stops at the next `And`/leaf head),
close every mechanical `BytePins*`/`DecodeFact*` leaf by generated name, and
return the data-dependent leftovers (`MemFacts`, branch guards) in order. -/
private partial def bfSolve (h : Term) (prefixStr : String) (g : MVarId) :
    TacticM (List MVarId) := do
  let decodeName (w : Nat) : String := "Vsa.Sim.DecodeTable.decode_" ++ hexName w
  let pinName (pc : Nat) : String := prefixStr ++ hexName pc
  let ty ← instantiateMVars (← g.getType)
  match ty.getAppFn.constName? with
  | some ``And =>
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
      let mut acc : List MVarId := []
      for g' in gs do acc := acc ++ (← bfSolve h prefixStr g')
      return acc
  | some ``BytePinsM => closeLeaf h g ty pinName 0 true; return []
  | some ``DecodeFactM => closeLeaf h g ty decodeName 1 false; return []
  | some ``BytePinsT => closeLeaf h g ty pinName 0 true; return []
  | some ``DecodeFactT => closeLeaf h g ty decodeName 1 false; return []
  | some ``True => g.assign (mkConst ``True.intro); return []
  | some ``BBlockFacts | some ``ProgFactsM | some ``TermPins | some ``TermFactsO =>
      -- reduce one container layer, keep walking
      let g' ← g.change (← g.withContext (whnf ty))
      bfSolve h prefixStr g'
  | _ =>
      -- data-dependent leaf (`MemFacts`, branch guard) — leave for the caller
      return [g]

elab "block_facts " h:term " with " pfx:str : tactic => do
  let leftovers ← bfSolve h pfx.getString (← getMainGoal)
  setGoals leftovers

end Vsa.Sim
