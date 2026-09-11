import Vsa.Sim.SeqClosureNormalExitResume
import Vsa.Sim.WordLoadData
import Vsa.Sim.SegEffect
import Vsa.Sim.FrameMeta

namespace Vsa.Sim.SeqBlockNormal

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

#derive_case continueSeg chain
  []
    terminator ⟨0x800041c8#64, 0xec051ae3#32, 0xe3#8, 0x1a#8, 0x05#8, 0xec#8,
      .br bop.BNE false, 10, 0, 0x1ed4#13, 0#21, 0#12⟩ ;;
  [(0x800041cc#64, 0x00813803#32),
   (0x800041d0#64, 0x01042703#32),
   (0x800041d4#64, 0x00180813#32),
   (0x800041d8#64, 0x0008079b#32)]
    terminator ⟨0x800041dc#64, 0xfce7c4e3#32, 0xe3#8, 0xc4#8, 0xe7#8, 0xfc#8,
      .br bop.BLT true, 15, 14, 0x1fc8#13, 0#21, 0#12⟩

#derive_case finalSeg chain
  []
    terminator ⟨0x800041c8#64, 0xec051ae3#32, 0xe3#8, 0x1a#8, 0x05#8, 0xec#8,
      .br bop.BNE false, 10, 0, 0x1ed4#13, 0#21, 0#12⟩ ;;
  [(0x800041cc#64, 0x00813803#32),
   (0x800041d0#64, 0x01042703#32),
   (0x800041d4#64, 0x00180813#32),
   (0x800041d8#64, 0x0008079b#32)]
    terminator ⟨0x800041dc#64, 0xfce7c4e3#32, 0xe3#8, 0xc4#8, 0xe7#8, 0xfc#8,
      .br bop.BLT false, 15, 14, 0x1fc8#13, 0#21, 0#12⟩ ;;
  [(0x800041e0#64, 0x00000513#32)]
    terminator ⟨0x800041e4#64, 0xeb9ff06f#32, 0x6f#8, 0xf0#8, 0x9f#8, 0xeb#8,
      .j, 0, 0, 0#13, 0x1ffeb8#21, 0#12⟩

def seg (more : Bool) : List BBlock := if more then continueSeg else finalSeg

def input (sp block : BitVec 64) : GRegs := [(10, 0#64), (2, sp), (8, block)]

def exitPC (more : Bool) : BitVec 64 := if more then 0x800041a4#64 else 0x8000409c#64

/-- Bounds for the saved index and the block's count word. -/
structure Geometry (sp block : BitVec 64) : Prop where
  stackLo : 0x80000000 ≤ sp.toNat + 8
  stackHi : sp.toNat + 16 ≤ 0x100000000
  stackHtif : sp.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ sp.toNat + 8
  countLo : 0x80000000 ≤ block.toNat + 16
  countHi : block.toNat + 20 ≤ 0x100000000
  countHtif : block.toNat + 20 ≤ tohostAddr ∨ tohostAddr + 8 ≤ block.toNat + 16

/-- Actual normal return, saved index, count, and the selected loop branch. -/
structure Pre (sp block : BitVec 64) (index count : Nat) (more : Bool)
    (cfg : Config) : Prop where
  good : GoodState cfg.σ
  tick : cfg.tick < 2
  pc : cfg.σ.regs.get? Register.PC = some 0x800041c8#64
  minstret : ∃ w, cfg.σ.regs.get? Register.minstret = some w
  registers : GHolds cfg.σ (input sp block)
  geometry : Geometry sp block
  nextBound : index + 1 ≤ count
  countBound : count < 2^31
  branch : decide (index + 1 < count) = more
  savedIndex : read64 cfg.σ.mem (sp.toNat + 8) = some index
  blockCount : read32 cfg.σ.mem (block.toNat + 16) = some count
  code : Code.Exec_stmtLoaded cfg.σ.mem

private theorem indexSext (n : Nat) (bound : n < 2^31) :
    wvalM (mkLine 0x800041d8#64 0x0008079b#32) [(16, BitVec.ofNat 64 n)] [] =
      BitVec.ofNat 64 n := by
  have extract : BitVec.extractLsb' 0 32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  simpa [wvalM, srcVal, lookupG, mkLine, decodeM, Sail.BitVec.extractLsb,
    BitVec.extractLsb, extract,
    show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 by decide] using
    seqClosureNormal_sext n bound

/-- Reflected facts use the saved index and immutable count from this return. -/
theorem Pre.facts {sp block : BitVec 64} {index count : Nat} {more : Bool} {cfg : Config}
    (h : Pre sp block index count more cfg) :
    ∃ indexBytes,
      ChainFacts cfg.σ.mem cfg.σ.mem (input sp block)
        [indexBytes, seqClosureNormalCountBytes cfg.σ.mem (block.toNat + 16)] (seg more) ∧
      bytesVal .ld indexBytes = BitVec.ofNat 64 index := by
  let ldIndex := mkLine 0x800041cc#64 0x00813803#32
  let ldCount := mkLine 0x800041d0#64 0x01042703#32
  have stackAddr : (eaddrM ldIndex (input sp block)).toNat = sp.toNat + 8 := by
    change (sp + 8#64).toNat = sp.toNat + 8
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := h.geometry.stackHi; change sp.toNat + 8 < 2^64; omega)]
    rfl
  have indexNat : (BitVec.ofNat 64 index).toNat = index :=
    Nat.mod_eq_of_lt (by have := h.nextBound; have := h.countBound; omega)
  obtain ⟨indexBytes, I⟩ := wordLoadFacts_of_read64 cfg.σ.mem (input sp block) ldIndex
    (BitVec.ofNat 64 index) rfl
    (by rw [stackAddr]; exact h.geometry.stackLo)
    (by rw [stackAddr]; exact h.geometry.stackHi)
    (by rw [stackAddr]; exact h.geometry.stackHtif)
    (by rw [stackAddr, indexNat]; exact h.savedIndex)
  have countAddr : (eaddrM ldCount (stepGM ldIndex (input sp block) indexBytes)).toNat =
      block.toNat + 16 := by
    change (block + 16#64).toNat = block.toNat + 16
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := h.geometry.countHi; change block.toNat + 16 < 2^64; omega)]
    rfl
  have countFacts : MemFacts cfg.σ.mem (stepGM ldIndex (input sp block) indexBytes)
      (seqClosureNormalCountBytes cfg.σ.mem (block.toNat + 16)) ldCount := by
    unfold MemFacts
    change (0x80000000 ≤ (eaddrM ldCount (stepGM ldIndex (input sp block) indexBytes)).toNat ∧
      (eaddrM ldCount (stepGM ldIndex (input sp block) indexBytes)).toNat + 4 ≤ 0x100000000 ∧
      ((eaddrM ldCount (stepGM ldIndex (input sp block) indexBytes)).toNat + 4 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (eaddrM ldCount (stepGM ldIndex (input sp block) indexBytes)).toNat)) ∧ _
    rw [countAddr]
    exact ⟨⟨h.geometry.countLo, h.geometry.countHi, h.geometry.countHtif⟩,
      by simp [LPins4, seqClosureNormalCountBytes]⟩
  have countValue := seqClosureNormalCount_value _ _ count h.countBound h.blockCount
  have increment : BitVec.ofNat 64 index + 1#64 = BitVec.ofNat 64 (index + 1) := by
    rw [← BitVec.ofNat_add]
  have sext := indexSext (index + 1) (by have := h.nextBound; have := h.countBound; omega)
  have signed (n : Nat) (bound : n < 2^31) : (BitVec.ofNat 64 n).toInt = (n : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), if_pos (by omega)]
  have branch : guardB bop.BLT (BitVec.ofNat 64 (index + 1)) (BitVec.ofNat 64 count) = more := by
    unfold guardB zopz0zI_s
    rw [signed count h.countBound, signed (index + 1) (by
      have := h.nextBound; have := h.countBound; omega)]
    change decide (((index + 1 : Nat) : Int) < (count : Int)) = more
    by_cases less : index + 1 < count
    · have lessInt : ((index + 1 : Nat) : Int) < (count : Int) := by omega
      rw [decide_eq_true lessInt]
      simpa only [decide_eq_true less] using h.branch
    · have notLessInt : ¬ ((index + 1 : Nat) : Int) < (count : Int) := by omega
      rw [decide_eq_false notLessInt]
      simpa only [decide_eq_false less] using h.branch
  refine ⟨indexBytes, ?_, I.value⟩
  cases more <;> simp only [seg, Bool.false_eq_true, if_false, if_true]
  all_goals
    chain_facts h.code with "Vsa.Sim.Code.exec_stmt_at_"
    · rfl
    · exact I.facts
    · exact countFacts
    · change guardB bop.BLT
        (wvalM (mkLine 0x800041d8#64 0x0008079b#32)
          [(16, bytesVal .ld indexBytes + 1#64)] [])
        (bytesVal .lw (seqClosureNormalCountBytes cfg.σ.mem (block.toNat + 16))) = _
      rw [I.value, increment, sext, countValue]
      exact branch

/-- The reached index, normal status, and unchanged memory of either route. -/
structure Post (sp block : BitVec 64) (index : Nat) (more : Bool)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (exitPC more)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  registers : GHolds after.σ [(2, sp), (8, block), (16, BitVec.ofNat 64 (index + 1)), (10, 0#64)]
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the selected normal route through the existing segment evaluator. -/
theorem run {sp block : BitVec 64} {index count : Nat} {more : Bool} {before : Config}
    (h : Pre sp block index count more before) :
    ∃ after, Steps before after ∧ Post sp block index more before after := by
  obtain ⟨indexBytes, facts, indexValue⟩ := h.facts
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (seg more) (input sp block)
    [indexBytes, seqClosureNormalCountBytes before.σ.mem (block.toNat + 16)]
    0x800041c8#64 vm (fun _ => False) AbiPreserved
    [(2, sp), (8, block), (16, BitVec.ofNat 64 (index + 1)), (10, 0#64)] before
    h.good h.pc hvm h.registers (by change KeysOK [10, 2, 8]; decide) facts
    (by cases more <;> change ChainOK 0x800041c8#64 [10, 2, 8] _ <;> decide) h.tick
    (by intro k _; cases more <;> rfl) (by decide) (by cases more <;> decide) (by
      cases more <;>
        change some sp = some sp ∧ some block = some block ∧
          some (bytesVal .ld indexBytes + 1#64) = some (BitVec.ofNat 64 (index + 1)) ∧
          some 0#64 = some 0#64 ∧ True
      all_goals simp only [indexValue, ← BitVec.ofNat_add, and_true])
  refine ⟨after, C.steps, C.good, C.tick, ?_, C.minstret, C.selected_regs, ?_, C.output, C.reg_frame⟩
  · cases more <;> exact C.pc
  · cases more <;> exact C.mem

#print axioms Pre.facts
#print axioms run

end Vsa.Sim.SeqBlockNormal
