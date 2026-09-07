import Vsa.Sim.OutputAliasLoaded
import Vsa.Sim.SegEvalSound
import Vsa.Sim.WriteLogRead

/-! Reached state for concrete trace certificates. Each transition consumes
actual Machine.Steps and the exact reflected read obligations. -/

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr

namespace Vsa.Sim.OutputAliasLoaded

/-- Every initial lookup reduces through the finite RAM byte interface. -/
def snapshotInitialRead (a : Nat) : Option (BitVec 8) :=
  if 0x80000000 ≤ a ∧ a < 0x88000000 then some (snapshotByte a) else none

theorem snapshot_logRead (log : List WEntry) (a : Nat) :
    (writeLog snapshotMem log)[a]? = logRead snapshotInitialRead log a :=
  writeLog_getElem?_logRead_of_initial snapshotMem snapshotInitialRead
    snapshot_lookup log a

structure TraceData where
  pc : BitVec 64
  regs : GRegs
  log : List WEntry
  out : Array String
  payload : BitVec 4

structure TraceHolds (d : TraceData) (c : Config) : Prop where
  good : GoodState c.σ
  tick : c.tick < 2
  pc : c.σ.regs.get? Register.PC = some d.pc
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  regs : GHolds c.σ d.regs
  mem : c.σ.mem = writeLog snapshotMem d.log
  out : c.σ.sailOutput = d.out
  payload : c.σ.regs.get? Register.htif_payload_writes = some d.payload

def TraceData.afterSegment (d : TraceData) (bs : List BBlock)
    (lds : List (List (BitVec 8))) : TraceData :=
  let result := evalBlocks bs (SegEvalState.init d.regs lds)
  { pc := evalBlocksPC d.pc (SegEvalState.init d.regs lds) bs
    regs := result.regs
    log := d.log ++ result.log
    out := d.out
    payload := d.payload }

/-- Segment certificates preserve the full reached trace state, including HTIF. -/
theorem TraceHolds.segment {d : TraceData} {c : Config}
    (h : TraceHolds d c) (bs : List BBlock) (lds : List (List (BitVec 8)))
    (hkeys : KeysOK (keysG d.regs))
    (hfacts : ChainFacts (writeLog snapshotMem d.log) (writeLog snapshotMem d.log)
      d.regs lds bs)
    (hwf : ChainOK d.pc (keysG d.regs) bs)
    (hpayload : ∀ n ∈ wrChain bs, (gprReg n == Register.htif_payload_writes) = false) :
    ∃ c', Steps c c' ∧ TraceHolds (d.afterSegment bs lds) c' := by
  obtain ⟨vm, hvm⟩ := h.minstret
  have hcf : ChainFacts c.σ.mem c.σ.mem d.regs lds bs := by
    rw [h.mem]
    exact hfacts
  obtain ⟨σ', i', hs, hi', hG', hm', ho', hp', hmi', hr', hf'⟩ :=
    segEval_sound bs c.σ c.tick c.steps d.pc vm d.regs lds
      h.good h.pc hvm h.regs hkeys hcf hwf h.tick
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs, ?_⟩
  exact {
    good := hG'
    tick := hi'
    pc := hp'
    minstret := hmi'
    regs := hr'
    mem := by
      change σ'.mem = writeLog snapshotMem
        (d.log ++ (evalBlocks bs (SegEvalState.init d.regs lds)).log)
      rw [writeLog_append, ← h.mem]
      exact hm'
    out := ho'.trans h.out
    payload := (hf' Register.htif_payload_writes (by decide) hpayload).trans h.payload }

#print axioms snapshot_logRead
#print axioms TraceHolds.segment

end Vsa.Sim.OutputAliasLoaded
