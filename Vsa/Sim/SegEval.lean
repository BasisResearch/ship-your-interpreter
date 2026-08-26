import Vsa.Sim.BlockTerm
import Vsa.Sim.WriteLogNF

/-!
# `SegEval` — first-order reflected evaluation of machine segments

`BlockMem` and `BlockTerm` already prove the instruction and terminator semantics.
This module gives their computed results one canonical first-order interface.
The evaluator carries only register pins, positional load bytes, and a write log.
It never reduces `ExtHashMap`; concrete memory is reconstructed once with
`writeLog` by `SegEvalSound`.

Timing witness (2026-08-26): `lake build Vsa.Sim.SegEval` completed the touched
target in 8.1s. The reflected leaves remain the existing per-block `ChainOK`
kernel decisions.
-/

open LeanRV64DExecutable Vsa

namespace Vsa.Sim

/-- First-order state used while reflecting a segment. -/
structure SegEvalState where
  regs : GRegs
  loads : List (List (BitVec 8))
  log : List WEntry

/-- Empty-log entry state for a segment. -/
def SegEvalState.init (regs : GRegs) (loads : List (List (BitVec 8))) : SegEvalState :=
  { regs, loads, log := [] }

/-- Evaluate one basic block on the abstract state.

The optional terminator changes only control flow. `runGM` and `wlogM` compute
the body effects. The log is appended, so every block seam has one normal form.
-/
def evalBlock (s : SegEvalState) (b : BBlock) : SegEvalState :=
  { regs := runGM b.body s.regs s.loads
    loads := ldsRunM b.body s.loads
    log := s.log ++ wlogM b.body s.regs s.loads }

/-- Structurally evaluate a path of basic blocks. -/
def evalBlocks : List BBlock → SegEvalState → SegEvalState
  | [], s => s
  | b :: bs, s => evalBlocks bs (evalBlock s b)

/-- Reflected final control-flow target. -/
def evalBlocksPC (pc : BitVec 64) (s : SegEvalState) (bs : List BBlock) : BitVec 64 :=
  chainEndPC pc s.regs s.loads bs

/-- Number of reflected machine steps. -/
def evalBlocksFuel (bs : List BBlock) : Nat := chainLen bs

@[simp] theorem evalBlocks_nil (s : SegEvalState) : evalBlocks [] s = s := rfl

@[simp] theorem evalBlocks_cons (b : BBlock) (bs : List BBlock) (s : SegEvalState) :
    evalBlocks (b :: bs) s = evalBlocks bs (evalBlock s b) := rfl

/-- The reflected register component is `BlockTerm`'s register fold. -/
theorem evalBlocks_regs : ∀ (bs : List BBlock) (s : SegEvalState),
    (evalBlocks bs s).regs = runChain bs s.regs s.loads
  | [], _ => rfl
  | b :: bs, s => evalBlocks_regs bs (evalBlock s b)

/-- The reflected positional-load component is the corresponding body fold. -/
theorem evalBlocks_loads : ∀ (bs : List BBlock) (s : SegEvalState),
    (evalBlocks bs s).loads =
      bs.foldl (fun loads b => ldsRunM b.body loads) s.loads
  | [], _ => rfl
  | b :: bs, s => by
      rw [evalBlocks_cons, evalBlocks_loads]
      simp only [evalBlock, List.foldl_cons]

/-- Applying the accumulated first-order log equals `BlockTerm`'s threaded
memory calculation. This is the single abstract-to-concrete memory seam. -/
theorem writeLog_evalBlocks : ∀ (bs : List BBlock) (s : SegEvalState)
    (m : Std.ExtHashMap Nat (BitVec 8)),
    writeLog m (evalBlocks bs s).log =
      memChain bs (writeLog m s.log) s.regs s.loads
  | [], _, _ => rfl
  | b :: bs, s, m => by
      rw [evalBlocks_cons, writeLog_evalBlocks bs (evalBlock s b) m]
      simp only [evalBlock, memChain]
      rw [writeLog_append]

/-- Empty-log specialization used by the soundness bridge. -/
theorem writeLog_evalBlocks_init (bs : List BBlock) (m : Std.ExtHashMap Nat (BitVec 8))
    (regs : GRegs) (loads : List (List (BitVec 8))) :
    writeLog m (evalBlocks bs (SegEvalState.init regs loads)).log =
      memChain bs m regs loads := by
  simpa only [SegEvalState.init, writeLog] using
    writeLog_evalBlocks bs (SegEvalState.init regs loads) m

@[simp] theorem evalBlocks_init_regs_nil (regs : GRegs)
    (loads : List (List (BitVec 8))) :
    (evalBlocks [] (SegEvalState.init regs loads)).regs = regs := rfl

#print axioms writeLog_evalBlocks
#print axioms writeLog_evalBlocks_init
#print axioms evalBlocks_regs

end Vsa.Sim
