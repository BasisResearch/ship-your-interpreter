import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.WordLoadData
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.InterpSpillReads
import Vsa.Sim.ExecBlockSites
import Vsa.Sim.ExecRecCommon
import Vsa.Sim.SegEffect
import Vsa.Sim.FrameMeta

namespace Vsa.Sim.SeqBlockDispatch

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.Machine Vsa.RuntimeRepr Vsa.Alloc

#derive_case seg chain
  [(0x800041a4#64, 0x00843783#32),
   (0x800041a8#64, 0x00381713#32),
   (0x800041ac#64, 0x00090693#32),
   (0x800041b0#64, 0x00e787b3#32),
   (0x800041b4#64, 0x0007b583#32),
   (0x800041b8#64, 0x00098613#32),
   (0x800041bc#64, 0x00048513#32),
   (0x800041c0#64, 0x01013423#32)]

def input (block sp interp env aRet : BitVec 64) (index : Nat) : GRegs :=
  [(8, block), (16, BitVec.ofNat 64 index), (2, sp), (9, interp), (19, env), (18, aRet)]

/-- Bounds for the block array read, selected pointer read, and saved index write. -/
structure Geometry (block base sp : BitVec 64) (index : Nat) : Prop where
  blockLo : 0x80000000 ≤ block.toNat + 8
  blockHi : block.toNat + 16 ≤ 0x100000000
  blockHtif : block.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ block.toNat + 8
  cellLo : 0x80000000 ≤ base.toNat + 8 * index
  cellHi : base.toNat + 8 * index + 8 ≤ 0x100000000
  cellHtif : base.toNat + 8 * index + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ base.toNat + 8 * index
  stackLo : 0x80000000 ≤ sp.toNat
  stackHi : sp.toNat + 16 ≤ 0x100000000
  stackHtif : tohostAddr + 16 ≤ sp.toNat
  stackAlign : sp.toNat % 8 = 0
  codeOff : sp.toNat + 16 ≤ 0x80003fe0 ∨ 0x800043ec ≤ sp.toNat + 8

/-- Exact pointer words used by the reflected block dispatch. -/
structure Data (m : Mem) (block sp interp env aRet base stmt : BitVec 64) (index : Nat)
    (baseBytes stmtBytes : List (BitVec 8)) : Prop where
  facts : ChainFacts m m (input block sp interp env aRet index) [baseBytes, stmtBytes] seg
  baseValue : bytesVal .ld baseBytes = base
  stmtValue : bytesVal .ld stmtBytes = stmt

theorem data (m : Mem) (block sp interp env aRet base stmt : BitVec 64) (index : Nat)
    (G : Geometry block base sp index) (code : Code.Exec_stmtLoaded m)
    (baseRead : read64 m (block.toNat + 8) = some base.toNat)
    (stmtRead : read64 m (base.toNat + 8 * index) = some stmt.toNat) :
    ∃ baseBytes stmtBytes, Data m block sp interp env aRet base stmt index baseBytes stmtBytes := by
  let L := input block sp interp env aRet index
  let ldBase := mkLine 0x800041a4#64 0x00843783#32
  let shift := mkLine 0x800041a8#64 0x00381713#32
  let retSlot := mkLine 0x800041ac#64 0x00090693#32
  let cell := mkLine 0x800041b0#64 0x00e787b3#32
  let ldStmt := mkLine 0x800041b4#64 0x0007b583#32
  have baseAddr : (eaddrM ldBase L).toNat = block.toNat + 8 := by
    change (block + 8#64).toNat = block.toNat + 8
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := G.blockHi; change block.toNat + 8 < 2^64; omega)]
    rfl
  obtain ⟨baseBytes, B⟩ := wordLoadFacts_of_read64 m L ldBase base rfl
    (by rw [baseAddr]; exact G.blockLo) (by rw [baseAddr]; exact G.blockHi)
    (by rw [baseAddr]; exact G.blockHtif) (by rw [baseAddr]; exact baseRead)
  let Lstmt := runGM [ldBase, shift, retSlot, cell] L [baseBytes]
  have cellAddr : (eaddrM ldStmt Lstmt).toNat = base.toNat + 8 * index := by
    change (bytesVal .ld baseBytes + (BitVec.ofNat 64 index <<< 3) + 0#64).toNat = _
    rw [B.value, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
    have hi : index < 2^64 := by have := G.cellHi; omega
    rw [Nat.mod_eq_of_lt hi]
    simp only [Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by have := G.cellHi; omega), Nat.mod_eq_of_lt (by
      have := G.cellHi; omega)]
    omega
  obtain ⟨stmtBytes, S⟩ := wordLoadFacts_of_read64 m Lstmt ldStmt stmt rfl
    (by rw [cellAddr]; exact G.cellLo) (by rw [cellAddr]; exact G.cellHi)
    (by rw [cellAddr]; exact G.cellHtif) (by rw [cellAddr]; exact stmtRead)
  have savedAddr : (sp + 8#64).toNat = sp.toNat + 8 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := G.stackHi; change sp.toNat + 8 < 2^64; omega)]
    rfl
  refine ⟨baseBytes, stmtBytes, ?_, B.value, S.value⟩
  chain_facts code with "Vsa.Sim.Code.exec_stmt_at_"
  · exact B.facts
  · exact S.facts
  · apply memFacts_sd_frame
    · rfl
    · change 0x80000000 ≤ (sp + 8#64).toNat
      rw [savedAddr]; have := G.stackLo; omega
    · change (sp + 8#64).toNat + 8 ≤ 0x100000000
      rw [savedAddr]; exact G.stackHi
    · change tohostAddr + 16 ≤ (sp + 8#64).toNat
      rw [savedAddr]; have := G.stackHtif; omega
    · change (sp + 8#64).toNat % 8 = 0
      rw [savedAddr]; have := G.stackAlign; omega

/-- The actual call endpoint retains arguments and the exact saved-index write. -/
structure Post (block sp interp env aRet stmt : BitVec 64) (index : Nat)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80003fe0#64
  ra : after.σ.regs.get? Register.x1 = some 0x800041c8#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  args : GHolds after.σ [(10, interp), (11, stmt), (12, env), (13, aRet),
    (2, sp), (8, block), (16, BitVec.ofNat 64 index), (9, interp), (18, aRet), (19, env)]
  memory : after.σ.mem = writeLog before.σ.mem [(sp.toNat + 8, 8, BitVec.ofNat 64 index)]
  savedIndex : read64 after.σ.mem (sp.toNat + 8) = some index
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreservedNoise R → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the block argument span and existing statement-call proof. -/
theorem run (block sp interp env aRet base stmt : BitVec 64) (index : Nat)
    (before : Config) (G : Geometry block base sp index)
    (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some 0x800041a4#64)
    (minstret : ∃ w, before.σ.regs.get? Register.minstret = some w)
    (registers : GHolds before.σ (input block sp interp env aRet index))
    (code : Code.Exec_stmtLoaded before.σ.mem)
    (baseRead : read64 before.σ.mem (block.toNat + 8) = some base.toNat)
    (stmtRead : read64 before.σ.mem (base.toNat + 8 * index) = some stmt.toNat) :
    ∃ after, Steps before after ∧ Post block sp interp env aRet stmt index before after := by
  obtain ⟨baseBytes, stmtBytes, D⟩ := data before.σ.mem block sp interp env aRet base stmt index
    G code baseRead stmtRead
  have savedAddr : (sp + 8#64).toNat = sp.toNat + 8 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := G.stackHi; change sp.toNat + 8 < 2^64; omega)]
    rfl
  have log : (evalBlocks seg (SegEvalState.init (input block sp interp env aRet index)
      [baseBytes, stmtBytes])).log = [(sp.toNat + 8, 8, BitVec.ofNat 64 index)] := by
    change [((sp + 8#64).toNat, 8, BitVec.ofNat 64 index)] = _
    rw [savedAddr]
  obtain ⟨after, C⟩ := bridgeOfSegFull seg (input block sp interp env aRet index)
    [baseBytes, stmtBytes] 0x800041a4#64 0x80003fe0#64 0x800041c8#64 before
    good pc minstret tick registers (by change KeysOK [8, 16, 2, 9, 19, 18]; decide) D.facts
    (by change ChainOK 0x800041a4#64 [8, 16, 2, 9, 19, 18] seg; decide)
    (by change KeysOK [10, 12, 11, 15, 13, 14, 8, 16, 2, 9, 19, 18]; decide)
    (by change ∀ n ∈ ([10, 12, 11, 15, 13, 14, 8, 16, 2, 9, 19, 18] : List Nat), n ≠ 1; decide) (by
      intro middle hg ht hp hmi hm _
      have mem : middle.σ.mem = writeLog before.σ.mem [(sp.toNat + 8, 8, BitVec.ofNat 64 index)] :=
        hm.trans (congrArg (writeLog before.σ.mem) log)
      have code' : Code.Exec_stmtLoaded middle.σ.mem := by
        apply loaded_exec_stmt_agreeP before.σ.mem middle.σ.mem _ code
        intro k hk
        rw [mem]
        apply (writeLog_out before.σ.mem [(sp.toNat + 8, 8, BitVec.ofNat 64 index)] k ?_).symm
        simp only [OutL, and_true]
        have := G.codeOff
        omega
      obtain ⟨vm, hvm⟩ := hmi
      obtain ⟨next, parity, step, tick', good', mem', obs⟩ :=
        site_800041c4_es middle.σ middle.tick middle.steps 0x800041c4#64 vm hg hp hvm code' rfl ht
      exact ⟨⟨next, parity, middle.steps + 1⟩,
        jalCallFacts_of_obs step tick' good' mem' obs (by decide)⟩)
  have memory := C.mem.trans (congrArg (writeLog before.σ.mem) log)
  refine ⟨after, C.run,
    { good := C.good, tick := C.tick, pc := C.pc, ra := C.ra, minstret := C.minstret
      args := ?_, memory := memory, savedIndex := ?_, output := C.output, frame := ?_ }⟩
  · apply gholds_selected (hregs := C.registers)
    change some (interp + 0#64) = some interp ∧ some (bytesVal .ld stmtBytes) = some stmt ∧
      some (env + 0#64) = some env ∧ some (aRet + 0#64) = some aRet ∧
      some sp = some sp ∧ some block = some block ∧ some (BitVec.ofNat 64 index) = some (BitVec.ofNat 64 index) ∧
      some interp = some interp ∧ some aRet = some aRet ∧ some env = some env ∧ True
    simp only [D.stmtValue, BitVec.add_zero, and_true]
  · rw [memory]
    have hn : (BitVec.ofNat 64 index).toNat = index :=
      Nat.mod_eq_of_lt (by have := G.cellHi; omega)
    simpa only [hn] using
      read64_of_writeLog_at before.σ.mem [(sp.toNat + 8, 8, BitVec.ofNat 64 index)]
        0 _ _ rfl (by simp [OutLRange])
  · intro R hR
    exact C.frame R (noise_ne_abi hR.1)
      (wrChain_ne_abi (by decide : WrChainAvoidAbi seg) hR.1)
      (abiPreserved_ne hR.1 (by decide))

#print axioms data
#print axioms run

end Vsa.Sim.SeqBlockDispatch
