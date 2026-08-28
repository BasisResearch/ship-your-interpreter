import Vsa.Sim.DeriveCase
import Vsa.Sim.DecodeTable
import Vsa.Sim.Code.Eval_expr

/-!
# `chain_facts` — auto-discharge the mechanical half of a whole `ChainFacts` bundle

`#derive_case name chain …` emits `theorem name_seg (…) (hfacts : ChainFacts σ.mem
σ.mem L lds name) (hwf : ChainOK …) …`.  The `hfacts` argument is the chained,
memory-threaded analogue of a single block's `BBlockFacts`: it recurses over the
block list, producing `BBlockFacts mc m L lds b ∧ ChainFacts mc … bs` at each
cons and terminating in `True`.

`block_facts` (`BlockTactics.lean`) already auto-closes the *mechanical* leaves
of ONE block (code byte pins + decode facts) from a single loaded-image
hypothesis and a symbol-name prefix.  This file lifts that to the WHOLE
`ChainFacts` bundle so a caller can write

```
chain_facts h with "<prefix>"
```

to CLOSE the `ChainFacts` goal a `name_seg` carries as a hypothesis, instead of
assuming it.  It walks the chain: for each block it closes every
`BytePinsM`/`DecodeFactM`/`BytePinsT`/`DecodeFactT`/`True` leaf by generating and
applying the named `Code.<fn>_at_<pc>` / `DecodeTable.decode_<word>` lemma from
the instruction literal, and leaves the genuinely data-dependent leaves
(load/store `MemFacts` windows + byte pins, branch/jump terminator guards) as
fresh goals in program order — exactly the leftovers `block_facts` leaves,
concatenated block-by-block down the chain.

The whole algorithm is a re-export of `block_facts`'s `bfSolve` walker: that
walker already has a `ChainFacts`/`BBlockFacts` container case (it reduces one
layer with `whnf` and keeps walking), so the same recursion that handles one
block handles the whole chain — the mechanical leaves read only the reduced
`mkLine` instruction literal (its `pc`/`word` fields), never the threaded
`writeLog`/`runGM`/`ldsRunM`/`stepMemM` state, so they close identically at
every depth.  (`bfSolve` is `private` to `BlockTactics.lean`, so the walker is
reproduced here rather than imported.)

No `sorry`/`native_decide`/`bv_decide`/Mathlib.  Verify with
`lake env lean Vsa/Sim/ChainFactsTac.lean`.
-/

open Lean Elab Tactic Meta
open LeanRV64DExecutable (Register)

namespace Vsa.Sim

/-- `Nat` payload of a `BitVec` literal expression, via Lean's own evaluator. -/
private def cfBvLitNat? (e : Expr) : MetaM (Option Nat) := do
  match ← getBitVecValue? e with
  | some ⟨_, v⟩ => return some v.toNat
  | none => return none

/-- Lowercase hex (no `0x`), zero-padded to 8 digits — the form the generated
`Code.*_at_<pc>` / `DecodeTable.decode_<word>` lemma names use. -/
private def cfHexName (n : Nat) : String :=
  let s := (Nat.toDigits 16 n).asString
  (String.mk (List.replicate (8 - s.length) '0')) ++ s

/-- Field `idx` (0 = pc, 1 = word) of a reduced `MInstr`/`TInstr` `.mk` literal. -/
private def cfStructField? (a : Expr) (idx : Nat) : Option Expr := a.getAppArgs[idx]?

/-- The instruction literal is the last explicit arg of the leaf predicate. -/
private def cfLastArg? (ty : Expr) : MetaM (Option Expr) := do
  match ty.getAppArgs.back? with
  | some a => return some (← whnf a)
  | none => return none

/-- Close one `BytePins*`/`DecodeFact*` leaf `g` by generating the lemma name
from the instruction literal's `pc`/`word` field. -/
private def cfCloseLeaf (h : Term) (g : MVarId) (ty : Expr) (nm : Nat → String)
    (fieldIdx : Nat) (applyH : Bool) : TacticM Unit := do
  let some a ← cfLastArg? ty | throwError "chain_facts: no instruction literal"
  let some fE := cfStructField? a fieldIdx | throwError "chain_facts: no field {fieldIdx}"
  let some n ← cfBvLitNat? fE | throwError "chain_facts: field not a literal"
  let stx ← if applyH then `($(mkIdent (nm n).toName) $h) else `($(mkIdent (nm n).toName))
  g.assign (← g.withContext (Term.elabTermEnsuringType stx ty))

/-- Walk a `ChainFacts` (or `BBlockFacts`) goal `g`: reduce container layers
(`ChainFacts`/`BBlockFacts`/`ProgFactsM`/`TermPins`/`TermFactsO`) with `whnf`
(which unfolds the concrete chain/block + the list recursion but stops at the
next `And`/leaf head), close every mechanical `BytePins*`/`DecodeFact*` leaf by
generated name, and return the data-dependent leftovers (`MemFacts`, branch
guards) in program order.  This is `block_facts`'s `bfSolve` walker verbatim; the
`ChainFacts` container case is what makes it traverse a whole chain. -/
private partial def cfSolve (h : Term) (prefixStr : String) (g : MVarId) :
    TacticM (List MVarId) := do
  let decodeName (w : Nat) : String := "Vsa.Sim.DecodeTable.decode_" ++ cfHexName w
  let pinName (pc : Nat) : String := prefixStr ++ cfHexName pc
  let ty ← instantiateMVars (← g.getType)
  match ty.getAppFn.constName? with
  | some ``And =>
      let gs ← g.apply (← mkConstWithFreshMVarLevels ``And.intro)
      let mut acc : List MVarId := []
      for g' in gs do acc := acc ++ (← cfSolve h prefixStr g')
      return acc
  | some ``BytePinsM => cfCloseLeaf h g ty pinName 0 true; return []
  | some ``DecodeFactM => cfCloseLeaf h g ty decodeName 1 false; return []
  | some ``BytePinsT => cfCloseLeaf h g ty pinName 0 true; return []
  | some ``DecodeFactT => cfCloseLeaf h g ty decodeName 1 false; return []
  | some ``True => g.assign (mkConst ``True.intro); return []
  | some ``ChainFacts | some ``BBlockFacts | some ``ProgFactsM
  | some ``TermPins | some ``TermFactsO =>
      -- reduce one container layer, keep walking
      let g' ← g.change (← g.withContext (whnf ty))
      cfSolve h prefixStr g'
  | _ =>
      -- `MemFacts` for an ALU op, and a fall-through terminator's stuck
      -- `match … .term`, are defeq `True`: close them. Genuine data-dependent
      -- leaves (`MemFacts` for a load/store, branch guards) are left in order.
      if ← g.withContext (isDefEq ty (mkConst ``True)) then
        g.assign (mkConst ``True.intro); return []
      else
        return [g]

/-- `chain_facts h with "<prefix>"` closes every mechanical leaf of a
`ChainFacts` (or `BBlockFacts`) goal from the single loaded-image hypothesis `h`
and the `Code.*_at_` symbol prefix, leaving the data-dependent leaves
(load/store windows + pins, terminator guards) as fresh goals in program order. -/
elab "chain_facts " h:term " with " pfx:str : tactic => do
  let leftovers ← cfSolve h pfx.getString (← getMainGoal)
  setGoals leftovers

/-! ## Demo — close a real, whole-chain `ChainFacts` goal end-to-end

`chainFactsDemo` is the pure-ALU segment `0x80003538 … 0x80003548` of `eval_expr`
(`slli/srli/auipc/addi/add`, no terminator): every element's `MemFacts` is `True`
and there are no terminator guards, so `chain_facts` discharges the WHOLE
`ChainFacts` bundle with **zero** leftover goals from one `Eval_exprLoaded`
hypothesis.  This is the whole-chain analogue of a single-block `block_facts`
call, and the exact obligation a `#derive_case … _seg` row would otherwise take
as a hypothesis. -/

#derive_case chainFactsDemo chain
  [(0x80003538#64, 0x02079713#32),   -- slli x14,x15,0x20
   (0x8000353c#64, 0x01e75793#32),   -- srli x15,x14,0x1e
   (0x80003540#64, 0x00017717#32),   -- auipc x14,0x17
   (0x80003544#64, 0xa4470713#32),   -- addi  x14,x14,-1468
   (0x80003548#64, 0x00e787b3#32)]   -- add   x15,x15,x14

/-- The payoff: the whole-chain `ChainFacts` bundle a `#derive_case … _seg` row
would take as a hypothesis, discharged in one `chain_facts` call (zero leftovers)
from a single loaded-image hypothesis. -/
theorem chainFactsDemo_facts (σ : Vsa.Machine.MState)
    (L : GRegs) (lds : List (List (BitVec 8)))
    (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ChainFacts σ.mem σ.mem L lds chainFactsDemo := by
  chain_facts h with "Vsa.Sim.Code.eval_expr_at_"

/-- End-to-end: feed the auto-discharged bundle straight into the row's
`chainFactsDemo_seg` (its `hfacts` hypothesis), closing the `#derive_case`-emitted
run theorem with `chain_facts` in place of the assumed `ChainFacts`. -/
theorem chainFactsDemo_row (σ : Vsa.Machine.MState) (i u : Nat) (vm : BitVec 64)
    (L : GRegs)
    (hG : GoodState σ)
    (hpc : σ.regs.get? Register.PC = some 0x80003538#64)
    (hmi : σ.regs.get? Register.minstret = some vm)
    (hL : GHolds σ L) (hkeys : KeysOK (keysG L))
    (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem)
    (hwf : ChainOK 0x80003538#64 (keysG L) chainFactsDemo)
    (hi : i < 2) :
    let out := evalBlocks chainFactsDemo (SegEvalState.init L [])
    ∃ (σ' : Vsa.Machine.MState) (i' : Nat),
      Vsa.Machine.Steps ⟨σ, i, u⟩ ⟨σ', i', u + evalBlocksFuel chainFactsDemo⟩ ∧
        i' < 2 ∧ GoodState σ' ∧
      σ'.mem = writeLog σ.mem out.log ∧ σ'.sailOutput = σ.sailOutput ∧
      σ'.regs.get? Register.PC
        = some (evalBlocksPC 0x80003538#64 (SegEvalState.init L []) chainFactsDemo) ∧
      (∃ w, σ'.regs.get? Register.minstret = some w) ∧
      GHolds σ' out.regs ∧
      (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
        (∀ n ∈ wrChain chainFactsDemo, (gprReg n == R) = false) →
        σ'.regs.get? R = σ.regs.get? R) :=
  chainFactsDemo_seg σ i u 0x80003538#64 vm L [] hG hpc hmi hL hkeys
    (chainFactsDemo_facts σ L [] h) hwf hi

#print axioms chainFactsDemo_facts
#print axioms chainFactsDemo_row

end Vsa.Sim
