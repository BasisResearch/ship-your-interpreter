import Vsa.Sim.SegEvalSound
import Vsa.Sim.FrameCalc
import Vsa.Sim.GeomFacts
import Vsa.Sim.BlockDecode

open Lean Elab Command Term Meta
open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

syntax dcPair := "(" term:max ", " term:max ")"

syntax dcBlock := "[" dcPair,* "]" (" terminator " term)? (";;")?

syntax (name := deriveCaseCmd)
  "#derive_case " ident " chain " dcBlock+ : command

private def mkBody (pairs : Array (TSyntax ``dcPair)) : CommandElabM (TSyntax `term) := do
  let lines ← pairs.mapM fun p =>
    match p with
    | `(dcPair| ($pc, $w)) => `(mkLine $pc $w)
    | _ => throwErrorAt p "malformed (pc, word) pair"
  `([$lines,*])

private def mkBlock (pairs : Array (TSyntax ``dcPair)) (t? : Option (TSyntax `term)) :
    CommandElabM (TSyntax `term) := do
  let body ← mkBody pairs
  let termStx ←
    match t? with
    | some t => `(some $t)
    | none => `(none)
  `({ body := $body, term := $termStx })

@[command_elab deriveCaseCmd]
def elabDeriveCase : CommandElab := fun stx => do
  match stx with
  | `(command| #derive_case $name:ident chain $blocks:dcBlock*) => do
    let mut blks := #[]
    for b in blocks do
      match b with
      | `(dcBlock| [ $pairs,* ] $[terminator $t?]? $[;;]?) =>
        blks := blks.push (← mkBlock pairs.getElems t?)
      | _ => throwErrorAt b "malformed block"
    elabCommand <|← `(command|
      def $name : List BBlock := [$blks,*])
    let segName := mkIdent (name.getId.appendAfter "_seg")
    elabCommand <|← `(command|

      theorem $segName (σ : MState) (i u : Nat) (pc0 vm : BitVec 64)
          (L : GRegs) (lds : List (List (BitVec 8)))
          (hG : GoodState σ)
          (hpc : σ.regs.get? Register.PC = some pc0)
          (hmi : σ.regs.get? Register.minstret = some vm)
          (hL : GHolds σ L) (hkeys : KeysOK (keysG L))
          (hfacts : ChainFacts σ.mem σ.mem L lds $name)
          (hwf : ChainOK pc0 (keysG L) $name)
          (hi : i < 2) :
          let out := evalBlocks $name (SegEvalState.init L lds)
          ∃ (σ' : MState) (i' : Nat),
            Steps ⟨σ, i, u⟩ ⟨σ', i', u + evalBlocksFuel $name⟩ ∧ i' < 2 ∧ GoodState σ' ∧
            σ'.mem = writeLog σ.mem out.log ∧ σ'.sailOutput = σ.sailOutput ∧
            σ'.regs.get? Register.PC = some (evalBlocksPC pc0 (SegEvalState.init L lds) $name) ∧
            (∃ w, σ'.regs.get? Register.minstret = some w) ∧
            GHolds σ' out.regs ∧
            (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
              (∀ n ∈ wrChain $name, (gprReg n == R) = false) →
              σ'.regs.get? R = σ.regs.get? R) :=
        segEval_sound $name σ i u pc0 vm L lds hG hpc hmi hL hkeys hfacts hwf hi)
  | _ => throwUnsupportedSyntax

end Vsa.Sim
