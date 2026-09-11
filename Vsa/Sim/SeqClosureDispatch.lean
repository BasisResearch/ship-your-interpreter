import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.WordLoadData
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.InterpSpillReads
import Vsa.Sim.SequenceDispatchSites
import Vsa.Sim.SegEffect
import Vsa.Sim.FrameMeta
import Vsa.Sim.EvalSimCommon

namespace Vsa.Sim.SeqClosureDispatch

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.Machine
open Vsa.RuntimeRepr

#derive_case seg chain
  [(0x80003354#64, 0x00883783#32),
   (0x80003358#64, 0x00341713#32),
   (0x8000335c#64, 0x09010693#32),
   (0x80003360#64, 0x00e787b3#32),
   (0x80003364#64, 0x0007b583#32),
   (0x80003368#64, 0x00098613#32),
   (0x8000336c#64, 0x00090513#32),
   (0x80003370#64, 0x01013023#32)]

def input (body sp interp env : BitVec 64) (index : Nat) : GRegs :=
  [(16, body), (8, BitVec.ofNat 64 index), (2, sp), (18, interp), (19, env)]

/-- Bounds of the two pointer reads and the one saved-body store. -/
structure Geometry (body base sp : BitVec 64) (index : Nat) : Prop where
  bodyLo : 0x80000000 ≤ body.toNat + 8
  bodyHi : body.toNat + 16 ≤ 0x100000000
  bodyHtif : body.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ body.toNat + 8
  cellLo : 0x80000000 ≤ base.toNat + 8 * index
  cellHi : base.toNat + 8 * index + 8 ≤ 0x100000000
  cellHtif : base.toNat + 8 * index + 8 ≤ tohostAddr ∨
    tohostAddr + 8 ≤ base.toNat + 8 * index
  stackLo : 0x80000000 ≤ sp.toNat
  stackHi : sp.toNat + 8 ≤ 0x100000000
  stackHtif : tohostAddr + 16 ≤ sp.toNat
  stackAlign : sp.toNat % 8 = 0
  codeOff : sp.toNat + 8 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sp.toNat

/-- Reflected loads use the exact body-array and selected-statement words. -/
structure Data (m : Mem) (body sp interp env base stmt : BitVec 64) (index : Nat)
    (baseBytes stmtBytes : List (BitVec 8)) : Prop where
  facts : ChainFacts m m (input body sp interp env index) [baseBytes, stmtBytes] seg
  baseValue : bytesVal .ld baseBytes = base
  stmtValue : bytesVal .ld stmtBytes = stmt

theorem data (m : Mem) (body sp interp env base stmt : BitVec 64) (index : Nat)
    (G : Geometry body base sp index) (code : Code.Eval_exprLoaded m)
    (baseRead : read64 m (body.toNat + 8) = some base.toNat)
    (stmtRead : read64 m (base.toNat + 8 * index) = some stmt.toNat) :
    ∃ baseBytes stmtBytes, Data m body sp interp env base stmt index baseBytes stmtBytes := by
  let L := input body sp interp env index
  let ldBase := mkLine 0x80003354#64 0x00883783#32
  let shift := mkLine 0x80003358#64 0x00341713#32
  let retSlot := mkLine 0x8000335c#64 0x09010693#32
  let cell := mkLine 0x80003360#64 0x00e787b3#32
  let ldStmt := mkLine 0x80003364#64 0x0007b583#32
  have baseAddr : (eaddrM ldBase L).toNat = body.toNat + 8 := by
    change (body + 8#64).toNat = body.toNat + 8
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.bodyHi; change body.toNat + 8 < 2^64; omega)]
    rfl
  obtain ⟨baseBytes, B⟩ := wordLoadFacts_of_read64 m L ldBase base rfl
    (by rw [baseAddr]; exact G.bodyLo) (by rw [baseAddr]; exact G.bodyHi)
    (by rw [baseAddr]; exact G.bodyHtif) (by rw [baseAddr]; exact baseRead)
  let Lstmt := runGM [ldBase, shift, retSlot, cell] L [baseBytes]
  have cellAddr : (eaddrM ldStmt Lstmt).toNat = base.toNat + 8 * index := by
    change (bytesVal .ld baseBytes + (BitVec.ofNat 64 index <<< 3) + 0#64).toNat = _
    rw [B.value, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat]
    have hi : index < 2^64 := by have := G.cellHi; omega
    rw [Nat.mod_eq_of_lt hi]
    simp only [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by have := G.cellHi; omega), Nat.mod_eq_of_lt (by
      have := G.cellHi; omega)]
    omega
  obtain ⟨stmtBytes, S⟩ := wordLoadFacts_of_read64 m Lstmt ldStmt stmt rfl
    (by rw [cellAddr]; exact G.cellLo) (by rw [cellAddr]; exact G.cellHi)
    (by rw [cellAddr]; exact G.cellHtif) (by rw [cellAddr]; exact stmtRead)
  refine ⟨baseBytes, stmtBytes, ?_, B.value, S.value⟩
  chain_facts code with "Vsa.Sim.Code.eval_expr_at_"
  · exact B.facts
  · exact S.facts
  · apply memFacts_sd_frame
    · rfl
    · change 0x80000000 ≤ (sp + 0#64).toNat
      simpa using G.stackLo
    · change (sp + 0#64).toNat + 8 ≤ 0x100000000
      simpa using G.stackHi
    · change tohostAddr + 16 ≤ (sp + 0#64).toNat
      simpa using G.stackHtif
    · change (sp + 0#64).toNat % 8 = 0
      simpa using G.stackAlign

/-- The dispatch writes exactly the saved body word at the caller's stack pointer. -/
theorem log (body sp interp env : BitVec 64) (index : Nat)
    (baseBytes stmtBytes : List (BitVec 8)) :
    (evalBlocks seg (SegEvalState.init (input body sp interp env index)
      [baseBytes, stmtBytes])).log = [(sp.toNat, 8, body)] := by
  change [((sp + 0#64).toNat, 8, body)] = _
  rw [BitVec.add_zero]

/-- The actual call endpoint retains arguments, the saved word, and its full frame. -/
structure Post (body sp interp env stmt : BitVec 64) (index : Nat)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80003fe0#64
  ra : after.σ.regs.get? Register.x1 = some 0x80003378#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  args : GHolds after.σ [(10, interp), (11, stmt), (12, env), (13, sp + 144#64),
    (2, sp), (8, BitVec.ofNat 64 index), (16, body), (18, interp), (19, env)]
  memory : after.σ.mem = writeLog before.σ.mem [(sp.toNat, 8, body)]
  savedBody : read64 after.σ.mem sp.toNat = some body.toNat
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreservedNoise R → after.σ.regs.get? R = before.σ.regs.get? R

theorem run (body sp interp env base stmt : BitVec 64) (index : Nat)
    (before : Config) (G : Geometry body base sp index)
    (hg : GoodState before.σ) (ht : before.tick < 2)
    (hp : before.σ.regs.get? Register.PC = some 0x80003354#64)
    (hmi : ∃ w, before.σ.regs.get? Register.minstret = some w)
    (hr : GHolds before.σ (input body sp interp env index))
    (code : Code.Eval_exprLoaded before.σ.mem)
    (baseRead : read64 before.σ.mem (body.toNat + 8) = some base.toNat)
    (stmtRead : read64 before.σ.mem (base.toNat + 8 * index) = some stmt.toNat) :
    ∃ after, Steps before after ∧ Post body sp interp env stmt index before after := by
  obtain ⟨baseBytes, stmtBytes, D⟩ := data before.σ.mem body sp interp env base stmt index
    G code baseRead stmtRead
  obtain ⟨after, C⟩ := bridgeOfSegFull seg (input body sp interp env index)
    [baseBytes, stmtBytes] 0x80003354#64 0x80003fe0#64 0x80003378#64 before
    hg hp hmi ht hr (by change KeysOK [16, 8, 2, 18, 19]; decide) D.facts
    (by change ChainOK 0x80003354#64 [16, 8, 2, 18, 19] seg; decide)
    (by change KeysOK [10, 12, 11, 15, 13, 14, 16, 8, 2, 18, 19]; decide)
    (by change ∀ n ∈ ([10, 12, 11, 15, 13, 14, 16, 8, 2, 18, 19] : List Nat), n ≠ 1; decide) (by
      intro middle good tick pc minstret memory _
      have mem : middle.σ.mem = writeLog before.σ.mem [(sp.toNat, 8, body)] :=
        memory.trans (congrArg (writeLog before.σ.mem) (log body sp interp env index _ _))
      have code' : Code.Eval_exprLoaded middle.σ.mem := by
        apply loaded_eval_expr_agreeP before.σ.mem middle.σ.mem _ code
        intro k hk
        rw [mem]
        apply (writeLog_out before.σ.mem [(sp.toNat, 8, body)] k ?_).symm
        have := G.codeOff
        simp only [OutL, and_true]
        omega
      obtain ⟨vm, hvm⟩ := minstret
      obtain ⟨next, parity, step, tick', good', mem', obs⟩ :=
        site_80003374_sequenceDispatch middle.σ middle.tick middle.steps 0x80003374#64 vm
          good pc hvm code' rfl tick
      exact ⟨⟨next, parity, middle.steps + 1⟩,
        jalCallFacts_of_obs step tick' good' mem' obs (by decide)⟩)
  have memory := C.mem.trans (congrArg (writeLog before.σ.mem) (log body sp interp env index _ _))
  refine ⟨after, C.run,
    { good := C.good, tick := C.tick, pc := C.pc, ra := C.ra, minstret := C.minstret
      args := ?_, memory := memory, savedBody := ?_, output := C.output, frame := ?_ }⟩
  · apply gholds_selected (hregs := C.registers)
    change some (interp + 0#64) = some interp ∧ some (bytesVal .ld stmtBytes) = some stmt ∧
      some (env + 0#64) = some env ∧ some (sp + 144#64) = some (sp + 144#64) ∧
      some sp = some sp ∧ some (BitVec.ofNat 64 index) = some (BitVec.ofNat 64 index) ∧
      some body = some body ∧ some interp = some interp ∧ some env = some env ∧ True
    simp only [D.stmtValue, BitVec.add_zero, and_true]
  · rw [memory]
    exact read64_of_writeLog_at before.σ.mem [(sp.toNat, 8, body)] 0 _ _ rfl (by
      simp [OutLRange])
  · intro R hR
    exact C.frame R (noise_ne_abi hR.1)
      (wrChain_ne_abi (by decide : WrChainAvoidAbi seg) hR.1)
      (abiPreserved_ne hR.1 (by decide))

#print axioms data
#print axioms log
#print axioms run

end Vsa.Sim.SeqClosureDispatch
