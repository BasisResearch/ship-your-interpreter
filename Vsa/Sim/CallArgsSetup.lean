import Vsa.Sim.CallCalleeRun
import Vsa.Sim.rows.CallClosureArgLoopEntryGen
import Vsa.Sim.EnvGetReflected.EnvGetCountHead

namespace Vsa.Sim.CallArgsSetup

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

#derive_case countSeg chain
  [(0x800031c0#64, 0x01842783#32),
   (0x800031c4#64, 0x02000713#32)]
    terminator ⟨0x800031c8#64, 0x5ef744e3#32, 0xe3#8, 0x44#8, 0xf7#8, 0x5e#8,
      .br bop.BLT false, 14, 15, 0x0de8#13, 0#21, 0#12⟩

#derive_case emptyInitSeg chain
  [(0x800031cc#64, 0x3f713c23#32),
   (0x800031d0#64, 0x00013683#32),
   (0x800031d4#64, 0x00000813#32)]
    terminator ⟨0x800031d8#64, 0x06f05e63#32, 0x63#8, 0x5e#8, 0xf0#8, 0x06#8,
      .br bop.BGE true, 0, 15, 0x007c#13, 0#21, 0#12⟩

/-- The empty route is the taken polarity of the existing initializer. -/
def initSeg (empty : Bool) : List BBlock :=
  if empty then emptyInitSeg else callClosureArgLoopEntrySeg

def seg (empty : Bool) : List BBlock := countSeg ++ initSeg empty

def input (node sp saved7 : BitVec 64) : GRegs := [(8, node), (2, sp), (23, saved7)]
def loads (m : Mem) (node sp : BitVec 64) : List (List (BitVec 8)) :=
  [wordLds4 m (node.toNat + 24), EvalChildArm.wordLds8 m sp.toNat]
def nextPC (empty : Bool) : BitVec 64 := if empty then 0x80003254#64 else 0x800031dc#64

/-- The argument count comes from the represented call; the environment was saved by callee staging. -/
structure Pre (node sp saved7 env : BitVec 64) (count : Nat) (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x800031c0#64
  regs : GHolds before.σ (input node sp saved7)
  geometry : BinaryPrefix.Geometry node sp
  countRead : read32 before.σ.mem (node.toNat + 24) = some count
  countBound : count ≤ 32
  envRead : read64 before.σ.mem sp.toNat = some env.toNat
  code : Code.Eval_exprLoaded before.σ.mem

/-- Both setup routes retain the same saved s7 word and start at argument index zero. -/
structure Post (node sp saved7 env : BitVec 64) (count : Nat) (empty : Bool)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (nextPC empty)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ [(8, node), (2, sp), (23, saved7), (13, env), (15, BitVec.ofNat 64 count), (16, 0#64)]
  empty_iff : empty = true ↔ count = 0
  memory : after.σ.mem = writeLog before.σ.mem [(sp.toNat + 1016, 8, saved7)]
  saved7Read : read64 after.σ.mem (sp.toNat + 1016) = some saved7.toNat
  outside : ∀ k, ¬ (sp.toNat + 1016 ≤ k ∧ k < sp.toNat + 1024) → before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

private theorem countGuard (count : Nat) (bound : count ≤ 32) :
    guardB bop.BLT 32#64 (BitVec.ofNat 64 count) = false := by
  have signed : (BitVec.ofNat 64 count).toInt = (count : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), if_pos (by omega)]
  unfold guardB zopz0zI_s
  rw [signed]
  change decide ((32 : Int) < count) = false
  simp only [decide_eq_false_iff_not]
  omega

/-- Discharge both branches from the actual bounded count and saved environment. -/
theorem Pre.facts {node sp saved7 env : BitVec 64} {count : Nat} {before : Config}
    (h : Pre node sp saved7 env count before) :
    ChainFacts before.σ.mem before.σ.mem (input node sp saved7) (loads before.σ.mem node sp)
      (seg (decide (count = 0))) := by
  have value := bytesVal_lw_wordLds4 before.σ.mem (node.toNat + 24) count
    (by have := h.countBound; omega) h.countRead
  have address : (node + 24#64).toNat = node.toNat + 24 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := h.geometry.nodeHi; change node.toNat + 24 < 2^64; omega)]
    rfl
  have savedAddr : (sp + 1016#64).toNat = sp.toNat + 1016 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := h.geometry.stackHi; change sp.toNat + 1016 < 2^64; omega)]
    rfl
  have countLoad : MemFacts before.σ.mem (input node sp saved7)
      (wordLds4 before.σ.mem (node.toNat + 24)) (mkLine 0x800031c0#64 0x01842783#32) := by
    change (0x80000000 ≤ (node + 24#64).toNat ∧ (node + 24#64).toNat + 4 ≤ 0x100000000 ∧
      ((node + 24#64).toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (node + 24#64).toNat)) ∧
      LPins4 before.σ.mem (node + 24#64).toNat _
    rw [address]
    exact ⟨⟨by have := h.geometry.nodeLo; omega, by have := h.geometry.nodeHi; omega,
      by have := h.geometry.nodeHtif; omega⟩, rfl, rfl, rfl, rfl⟩
  have emptyGuard : guardB bop.BGE 0#64 (BitVec.ofNat 64 count) = decide (count = 0) := by
    by_cases hz : count = 0
    · subst count; exact blez_guard_zero
    · simpa [hz, guardB] using blez_guard_pos count (by omega) (by have := h.countBound; omega)
  generalize he : decide (count = 0) = empty
  cases empty <;> simp only [seg, initSeg, Bool.false_eq_true, if_false, if_true] <;> chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
  all_goals first
    | exact countLoad
    | change guardB bop.BLT 32#64 (bytesVal .lw (wordLds4 before.σ.mem (node.toNat + 24))) = false
      rw [value]; exact countGuard count h.countBound
    | exact BinaryPrefix.store_facts h.geometry 1016 rfl rfl rfl (by decide) (by decide)
    | change guardB bop.BGE 0#64 (bytesVal .lw (wordLds4 before.σ.mem (node.toNat + 24))) = _
      rw [value]; exact emptyGuard.trans he
    | change (0x80000000 ≤ (sp + 0#64).toNat ∧ (sp + 0#64).toNat + 8 ≤ 0x100000000 ∧
        ((sp + 0#64).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (sp + 0#64).toNat)) ∧ LPins8
        (writeMap8 before.σ.mem (sp + 1016#64).toNat (sdData_val saved7)) (sp + 0#64).toNat
        (EvalChildArm.wordLds8 before.σ.mem sp.toNat)
      rw [savedAddr, BitVec.add_zero]
      refine ⟨⟨h.geometry.stackLo, by have := h.geometry.stackHi; omega,
        Or.inr (by have := h.geometry.stackHtif; omega)⟩, ?_⟩
      simp (disch := omega) [LPins8, EvalChildArm.wordLds8, getElem_writeMap8_disjoint]
      exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Execute argument setup to the loop head or the empty-argument dispatch. -/
theorem run {node sp saved7 env : BitVec 64} {count : Nat} {before : Config}
    (h : Pre node sp saved7 env count before) :
    ∃ after empty, Steps before after ∧ Post node sp saved7 env count empty before after := by
  let empty := decide (count = 0)
  have value := bytesVal_lw_wordLds4 before.σ.mem (node.toNat + 24) count
    (by have := h.countBound; omega) h.countRead
  have environment := EvalChildArm.bytesVal_ld_wordLds before.σ.mem sp.toNat env h.envRead
  have savedAddr : (sp + 1016#64).toNat = sp.toNat + 1016 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := h.geometry.stackHi; change sp.toNat + 1016 < 2^64; omega)]
    rfl
  have log : (evalBlocks (seg empty) (SegEvalState.init (input node sp saved7)
      (loads before.σ.mem node sp))).log = [(sp.toNat + 1016, 8, saved7)] := by
    generalize empty = b
    cases b <;> change [((sp + 1016#64).toNat, 8, saved7)] = _ <;> rw [savedAddr]
  have project : GProjects (evalBlocks (seg empty) (SegEvalState.init (input node sp saved7)
      (loads before.σ.mem node sp))).regs
      [(8, node), (2, sp), (23, saved7), (13, env), (15, BitVec.ofNat 64 count), (16, 0#64)] := by
    generalize empty = b
    cases b <;> simp [GProjects, seg, initSeg, countSeg, emptyInitSeg, callClosureArgLoopEntrySeg, input, loads,
      evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM, stepLdsM, ldsRunM, wvalM,
      srcVal, lookupG, eraseG, mkLine, decodeM, value, environment, sext_zero]
  obtain ⟨vm, hvm⟩ := h.good.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (seg empty) (input node sp saved7)
    (loads before.σ.mem node sp) 0x800031c0#64 vm
    (fun k => sp.toNat + 1016 ≤ k ∧ k < sp.toNat + 1024) AbiPreserved _ before
    h.good h.pc hvm h.regs (by change KeysOK [8, 2, 23]; decide) h.facts
    (by generalize empty = b; cases b <;> change ChainOK 0x800031c0#64 [8, 2, 23] _ <;> decide) h.tick
    (by intro k hk; rw [log]; symm; apply writeLog_out; simp only [OutL, and_true]; omega)
    (by decide) (by generalize empty = b; cases b <;> decide) project
  have memory := C.mem.trans (congrArg (writeLog before.σ.mem) log)
  refine ⟨after, empty, C.steps,
    { good := C.good, tick := C.tick, pc := ?_, minstret := C.minstret, regs := C.selected_regs
      empty_iff := by simp [empty], memory := memory, saved7Read := ?_
      outside := C.outside, output := C.output, frame := C.reg_frame }⟩
  · have pc := C.pc
    generalize he : empty = b at pc ⊢
    cases b <;> exact pc
  · rw [memory]
    exact read64_of_writeLog_at before.σ.mem [(sp.toNat + 1016, 8, saved7)] 0 _ _ rfl (by simp [OutLRange])

end Vsa.Sim.CallArgsSetup
