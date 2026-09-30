import Vsa.Sim.BlockTerm
import Vsa.Sim.WriteLogNF

open LeanRV64DExecutable Vsa

namespace Vsa.Sim

structure SegEvalState where
  regs : GRegs
  loads : List (List (BitVec 8))
  log : List WEntry

def SegEvalState.init (regs : GRegs) (loads : List (List (BitVec 8))) : SegEvalState :=
  { regs, loads, log := [] }

def evalBlock (s : SegEvalState) (b : BBlock) : SegEvalState :=
  { regs := runGM b.body s.regs s.loads
    loads := ldsRunM b.body s.loads
    log := s.log ++ wlogM b.body s.regs s.loads }

def evalBlocks : List BBlock → SegEvalState → SegEvalState
  | [], s => s
  | b :: bs, s => evalBlocks bs (evalBlock s b)

def evalBlocksPC (pc : BitVec 64) (s : SegEvalState) (bs : List BBlock) : BitVec 64 :=
  chainEndPC pc s.regs s.loads bs

def evalBlocksFuel (bs : List BBlock) : Nat := chainLen bs

@[simp] theorem evalBlocks_nil (s : SegEvalState) : evalBlocks [] s = s := rfl

@[simp] theorem evalBlocks_cons (b : BBlock) (bs : List BBlock) (s : SegEvalState) :
    evalBlocks (b :: bs) s = evalBlocks bs (evalBlock s b) := rfl

theorem evalBlocks_regs : ∀ (bs : List BBlock) (s : SegEvalState),
    (evalBlocks bs s).regs = runChain bs s.regs s.loads
  | [], _ => rfl
  | b :: bs, s => evalBlocks_regs bs (evalBlock s b)

theorem writeLog_evalBlocks : ∀ (bs : List BBlock) (s : SegEvalState)
    (m : Std.ExtHashMap Nat (BitVec 8)),
    writeLog m (evalBlocks bs s).log =
      memChain bs (writeLog m s.log) s.regs s.loads
  | [], _, _ => rfl
  | b :: bs, s, m => by
      rw [evalBlocks_cons, writeLog_evalBlocks bs (evalBlock s b) m]
      simp only [evalBlock, memChain]
      rw [writeLog_append]

theorem writeLog_evalBlocks_init (bs : List BBlock) (m : Std.ExtHashMap Nat (BitVec 8))
    (regs : GRegs) (loads : List (List (BitVec 8))) :
    writeLog m (evalBlocks bs (SegEvalState.init regs loads)).log =
      memChain bs m regs loads := by
  simpa only [SegEvalState.init, writeLog, List.foldl_nil] using
    writeLog_evalBlocks bs (SegEvalState.init regs loads) m

@[simp] theorem evalBlocks_init_regs_nil (regs : GRegs)
    (loads : List (List (BitVec 8))) :
    (evalBlocks [] (SegEvalState.init regs loads)).regs = regs := rfl

end Vsa.Sim
