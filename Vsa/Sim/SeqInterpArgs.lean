import Vsa.Sim.rows.LoopHeadArgSetupSeg
import Vsa.Sim.InitialExecSites
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.WordLoadData
import Vsa.Sim.FrameMeta
import Vsa.Sim.SegEffect
import Vsa.Sim.Code.Interp_run

namespace Vsa.Sim.SeqInterpArgs

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.Machine Vsa.Alloc

/-- Bounds for the two words read while setting up a statement call. -/
structure Geometry (sp interp : BitVec 64) : Prop where
  stackLo : 0x80000000 ≤ sp.toNat
  stackHi : sp.toNat + 8 ≤ 0x100000000
  stackHtif : sp.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ sp.toNat
  interpLo : 0x80000000 ≤ interp.toNat
  interpHi : interp.toNat + 8 ≤ 0x100000000
  interpHtif : interp.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ interp.toNat

/-- Both reflected loads use words from the current memory. -/
structure Data (m : Mem) (sp stmt interp env : BitVec 64)
    (inputBytes envBytes : List (BitVec 8)) : Prop where
  facts : ChainFacts m m (loopHeadArgSetupL sp stmt) [inputBytes, envBytes]
    loopHeadArgSetupSeg
  input : bytesVal .ld inputBytes = interp
  environment : bytesVal .ld envBytes = env

theorem data (m : Mem) (sp stmt interp env : BitVec 64)
    (G : Geometry sp interp) (code : Code.Interp_runLoaded m)
    (saved : read64 m sp.toNat = some interp.toNat)
    (environment : read64 m interp.toNat = some env.toNat) :
    ∃ inputBytes envBytes, Data m sp stmt interp env inputBytes envBytes := by
  let L := loopHeadArgSetupL sp stmt
  let ldInput := mkLine 0x80004460#64 0x00013783#32
  let setRet := mkLine 0x80004464#64 0x05810693#32
  let setStmt := mkLine 0x80004468#64 0x00048593#32
  let ldEnv := mkLine 0x8000446c#64 0x0007b603#32
  have stackAddr : (eaddrM ldInput L).toNat = sp.toNat := by
    change (sp + 0#64).toNat = sp.toNat
    rw [BitVec.add_zero]
  obtain ⟨inputBytes, I⟩ := wordLoadFacts_of_read64 m L ldInput interp rfl
    (by rw [stackAddr]; exact G.stackLo) (by rw [stackAddr]; exact G.stackHi)
    (by rw [stackAddr]; exact G.stackHtif) (by rw [stackAddr]; exact saved)
  let Lenv := runGM [ldInput, setRet, setStmt] L [inputBytes]
  have envAddr : (eaddrM ldEnv Lenv).toNat = interp.toNat := by
    change (bytesVal .ld inputBytes + 0#64).toNat = interp.toNat
    rw [I.value, BitVec.add_zero]
  obtain ⟨envBytes, E⟩ := wordLoadFacts_of_read64 m Lenv ldEnv env rfl
    (by rw [envAddr]; exact G.interpLo) (by rw [envAddr]; exact G.interpHi)
    (by rw [envAddr]; exact G.interpHtif) (by rw [envAddr]; exact environment)
  refine ⟨inputBytes, envBytes, ?_, I.value, E.value⟩
  chain_facts code with "Vsa.Sim.Code.interp_run_at_"
  all_goals first | exact I.facts | exact E.facts

/-- The statement entry retains all arguments and the caller's ABI registers. -/
structure Post (sp stmt interp env : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80003fe0#64
  ra : after.σ.regs.get? Register.x1 = some 0x80004478#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  args : GHolds after.σ [(10, interp), (11, stmt), (12, env), (13, sp + 88#64),
    (2, sp), (9, stmt)]
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the existing argument span and generated statement-call instruction. -/
theorem run (sp stmt interp env : BitVec 64) (before : Config)
    (G : Geometry sp interp) (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some 0x80004460#64)
    (minstret : ∃ w, before.σ.regs.get? Register.minstret = some w)
    (registers : GHolds before.σ (loopHeadArgSetupL sp stmt))
    (code : Code.Interp_runLoaded before.σ.mem)
    (saved : read64 before.σ.mem sp.toNat = some interp.toNat)
    (environment : read64 before.σ.mem interp.toNat = some env.toNat) :
    ∃ after, Steps before after ∧ Post sp stmt interp env before after := by
  obtain ⟨inputBytes, envBytes, D⟩ := data before.σ.mem sp stmt interp env G code
    saved environment
  obtain ⟨after, C⟩ := bridgeOfSegFull loopHeadArgSetupSeg (loopHeadArgSetupL sp stmt)
    [inputBytes, envBytes] 0x80004460#64 0x80003fe0#64 0x80004478#64 before
    good pc minstret tick registers (by change KeysOK [2, 9]; decide) D.facts
    (by change ChainOK 0x80004460#64 [2, 9] loopHeadArgSetupSeg; decide)
    (by change KeysOK [10, 12, 11, 13, 15, 2, 9]; decide)
    (by change ∀ n ∈ ([10, 12, 11, 13, 15, 2, 9] : List Nat), n ≠ 1; decide) (by
      intro middle hg ht hp hmi hm _
      have hm' : middle.σ.mem = before.σ.mem := hm.trans (by rfl)
      obtain ⟨vm, hvm⟩ := hmi
      obtain ⟨next, parity, step, tick', good', mem', obs⟩ :=
        site_80004474_initialExec middle.σ middle.tick middle.steps 0x80004474#64 vm
          hg hp hvm (hm'.symm ▸ code) rfl ht
      exact ⟨⟨next, parity, middle.steps + 1⟩,
        jalCallFacts_of_obs step tick' good' mem' obs (by decide)⟩)
  refine ⟨after, C.run,
    { good := C.good, tick := C.tick, pc := C.pc, ra := C.ra, minstret := C.minstret
      args := ?_, memory := C.mem.trans (by rfl), output := C.output, frame := ?_ }⟩
  · apply gholds_selected (hregs := C.registers)
    change some (bytesVal .ld inputBytes + 0#64) = some interp ∧
      some (stmt + 0#64) = some stmt ∧ some (bytesVal .ld envBytes) = some env ∧
      some (sp + 88#64) = some (sp + 88#64) ∧ some sp = some sp ∧
      some stmt = some stmt ∧ True
    simp only [D.input, D.environment, BitVec.add_zero, and_true]
  · intro R hR
    exact C.frame R (noise_ne_abi hR)
      (wrChain_ne_abi (by decide : WrChainAvoidAbi loopHeadArgSetupSeg) hR)
      (abiPreserved_ne hR (by decide))

#print axioms data
#print axioms run

end Vsa.Sim.SeqInterpArgs
