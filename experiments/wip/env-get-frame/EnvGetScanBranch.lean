import EnvGetScanState

open LeanRV64DExecutable Sail Vsa
open Vsa.Machine (Config Steps)
open Vsa.MemRepr Vsa.RuntimeRepr

namespace Vsa.Sim.EnvGetReflected

/-- The result branch preserves every saved register and the return address. -/
def scanBranchKeep (R : Register) : Bool :=
  Vsa.Alloc.AbiPreserved R || R == Register.x1

theorem scanBranchKeep_noise : ∀ R ∈ noiseRegs, scanBranchKeep R = false := by decide

def scanBranchSeg (taken : Bool) : List BBlock :=
  if taken then env_getX2c6cTSeg else env_getX2c6cFSeg

def scanBranchPC (taken : Bool) : BitVec 64 :=
  if taken then 0x80002c54#64 else 0x80002c70#64

/-- A branch endpoint retains the semantic scan and the outer register frame. -/
structure ScanBranchResult
    (g : (R : Register) → Option (RegisterType R))
    (env name out count pn ra sp : BitVec 64) (i : Nat) (taken : Bool)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem) (before after : Config) : Prop where
  steps : Steps before after
  scan : ScanSt g (scanBranchPC taken) env name out count pn ra sp i
    f nameStr N phiF phiC m0 after
  output : after.σ.sailOutput = before.σ.sailOutput
  kept_frame : ∀ R, kept R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute either generated result-branch polarity from its actual `a0`.
The same segment result supplies the scan carrier and register frame. -/
theorem scan_branch
    (g : (R : Register) → Option (RegisterType R))
    (env name out count pn ra sp : BitVec 64) (i : Nat) (taken : Bool)
    (f : Vsa.While.Frame) (nameStr : String) (N : NativeAddrs)
    (phiF phiC : Vsa.While.Addr → Nat) (m0 : Mem) (c : Config)
    (hSt : ScanSt g 0x80002c6c#64 env name out count pn ra sp i
      f nameStr N phiF phiC m0 c)
    (x : BitVec 64) (hx : c.σ.regs.get? Register.x10 = some x)
    (hbranch : (x != 0#64) = taken) :
    ∃ after, ScanBranchResult g env name out count pn ra sp i taken
      f nameStr N phiF phiC m0 c after := by
  let L : GRegs := [(10, x)]
  have hL : GHolds c.σ L := ⟨by simpa [gprGet] using hx, trivial⟩
  have hloaded := hSt.loadedG
  have hfacts : ChainFacts c.σ.mem c.σ.mem L [] (scanBranchSeg taken) := by
    cases taken <;> chain_facts hloaded with "Vsa.Sim.Code.env_get_at_" <;>
      exact hbranch
  have hmemLog : writeLog c.σ.mem
      (evalBlocks (scanBranchSeg taken) (SegEvalState.init L [])).log = c.σ.mem := by
    cases taken <;> rfl
  have hpcEval : evalBlocksPC 0x80002c6c#64
      (SegEvalState.init L []) (scanBranchSeg taken) = scanBranchPC taken := by
    cases taken <;> rfl
  obtain ⟨vm, hvm⟩ := hSt.minstret
  obtain ⟨after, h⟩ := segEval_selected_framed (scanBranchSeg taken) L []
    0x80002c6c#64 vm (fun _ => False) scanBranchKeep [] c
    hSt.good hSt.pc hvm hL (by show KeysOK [10]; decide) hfacts
    (by cases taken <;> show ChainOK 0x80002c6c#64 [10] _ <;> decide)
    hSt.tick (fun _ _ => by rw [hmemLog]) scanBranchKeep_noise
    (by cases taken <;> decide) trivial
  have habi : ∀ R, Vsa.Alloc.AbiPreserved R = true →
      after.σ.regs.get? R = c.σ.regs.get? R := by
    intro R hR
    exact h.reg_frame R (by simp [scanBranchKeep, hR])
  have hra : after.σ.regs.get? Register.x1 = some ra :=
    (h.reg_frame Register.x1 (by decide)).trans hSt.ra
  refine ⟨after,
    { steps := h.steps
      scan := ScanSt.transport hSt h.good h.tick (h.mem.trans hmemLog)
        (hpcEval ▸ h.pc) hra habi
      output := h.output
      kept_frame := fun R hR => habi R (kept_abi R hR) }⟩

#print axioms scanBranchKeep_noise
#print axioms scan_branch

end Vsa.Sim.EnvGetReflected
