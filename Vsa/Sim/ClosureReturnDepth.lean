import Vsa.Sim.ClosureCallReturnReads
import Vsa.Sim.rows.CallClosureBodyExit
import Vsa.Sim.rows.CallClosureRetClass
import Vsa.Sim.rows.CallClosureNormalRet

namespace Vsa.Sim.ClosureReturnDepth

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

def seg (returns : Bool) : List BBlock :=
  if returns then callClosureBodyExitRetSeg ++ callClosureRetClassSeg else callClosureNormalDepthSeg

def entryPC (returns : Bool) : BitVec 64 := if returns then 0x80003378#64 else 0x80003954#64
def exitPC (returns : Bool) : BitVec 64 := if returns then 0x8000339c#64 else 0x80003964#64
def input (interp sret : BitVec 64) (returns : Bool) : GRegs :=
  [(18, interp), (9, sret)] ++ if returns then [(10, 3#64)] else []
def selected (interp sret : BitVec 64) (returns : Bool) : GRegs :=
  [(18, interp), (9, sret), (10, if returns then 3#64 else sret)]

/-- Physical bounds for the interpreter depth word. -/
structure Geometry (interp : BitVec 64) : Prop where
  lo : 0x80000000 ≤ interp.toNat + 8
  hi : interp.toNat + 12 ≤ 0x100000000
  htif : tohostAddr + 16 ≤ interp.toNat + 8
  align : interp.toNat % 4 = 0

/-- Actual body status and the depth word preserved through the body run. -/
structure Pre (interp sret : BitVec 64) (depth : Nat) (returns : Bool) (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some (entryPC returns)
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  regs : GHolds before.σ (input interp sret returns)
  geometry : Geometry interp
  depthRead : read32 before.σ.mem (interp.toNat + 8) = some (depth + 1)
  bound : depth < 1000
  code : Code.Eval_exprLoaded before.σ.mem

theorem Geometry.address {interp : BitVec 64} (G : Geometry interp) :
    (interp + 8#64).toNat = interp.toNat + 8 := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by have := G.hi; change interp.toNat + 8 < 2^64; omega)]
  rfl

/-- The emitted 32-bit decrement restores the caller's bounded depth. -/
theorem decrement (depth : Nat) (bound : depth < 1000) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb
      (BitVec.ofNat 64 (depth + 1) + sign_extend (m := 64) (0xfff#12)) 31 0) =
      BitVec.ofNat 64 depth := by
  have sum : BitVec.ofNat 64 (depth + 1) + sign_extend (m := 64) (0xfff#12) =
      BitVec.ofNat 64 depth := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    rw [show BitVec.ofNat 64 1 + sign_extend (m := 64) (0xfff#12) = 0#64 by decide,
      BitVec.add_zero]
  rw [sum]
  apply BitVec.eq_of_toNat_eq
  have slice : Sail.BitVec.extractLsb (BitVec.ofNat 64 depth) 31 0 = BitVec.ofNat 32 depth := by
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat (31 - 0 + 1) ((BitVec.ofNat 64 depth).toNat >>> 0)).toNat = _
    simp only [Nat.shiftRight_zero, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show depth < 2^64 by omega)]
  change ((Sail.BitVec.extractLsb (BitVec.ofNat 64 depth) 31 0).signExtend 64).toNat = _
  rw [slice, BitVec.toNat_signExtend]
  have msb : (BitVec.ofNat 32 depth).msb = false := by
    rw [BitVec.msb_eq_getLsbD_last]
    simp only [BitVec.getLsbD_ofNat]
    rw [Nat.testBit_lt_two_pow (by omega)]
    rfl
  rw [msb, if_neg (by simp), Nat.add_zero, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem Pre.facts {interp sret : BitVec 64} {depth : Nat} {returns : Bool} {before : Config}
    (h : Pre interp sret depth returns before) :
    ChainFacts before.σ.mem before.σ.mem (input interp sret returns)
      [wordLds4 before.σ.mem (interp.toNat + 8)] (seg returns) := by
  have loadFacts {L : GRegs} {a : MInstr} (kind : a.kind = .lw)
      (address : (eaddrM a L).toNat = interp.toNat + 8) :
      MemFacts before.σ.mem L (wordLds4 before.σ.mem (interp.toNat + 8)) a := by
    simp only [MemFacts, kind, address]
    exact ⟨⟨h.geometry.lo, by have := h.geometry.hi; omega,
      Or.inr (by have := h.geometry.htif; omega)⟩, by simp [LPins4, wordLds4]⟩
  have storeFacts : 0x80000000 ≤ (interp + 8#64).toNat ∧
      (interp + 8#64).toNat + 4 ≤ 0x100000000 ∧
      tohostAddr + 16 ≤ (interp + 8#64).toNat ∧ (interp + 8#64).toNat % 4 = 0 := by
    rw [h.geometry.address]
    exact ⟨h.geometry.lo, by have := h.geometry.hi; omega, h.geometry.htif,
      by have := h.geometry.align; omega⟩
  cases returns <;> simp only [seg, Bool.false_eq_true, if_false, if_true]
  · chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
    · exact loadFacts rfl h.geometry.address
    · exact storeFacts
  · chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
    · change guardB bop.BEQ 3#64 0#64 = false; decide
    · exact loadFacts rfl h.geometry.address
    · exact storeFacts
    · change guardB bop.BGEU 1#64
        (sign_extend (m := 64) (Sail.BitVec.extractLsb (3#64 + sign_extend (m := 64) (0xfff#12)) 31 0)) = false
      decide
    · change guardB bop.BNE 3#64 3#64 = false; decide

theorem Pre.log {interp sret : BitVec 64} {depth : Nat} {returns : Bool} {before : Config}
    (h : Pre interp sret depth returns before) :
    (evalBlocks (seg returns) (SegEvalState.init (input interp sret returns)
      [wordLds4 before.σ.mem (interp.toNat + 8)])).log =
      [(interp.toNat + 8, 4, BitVec.ofNat 64 depth)] := by
  have value := bytesVal_lw_wordLds4 before.σ.mem (interp.toNat + 8) (depth + 1)
    (by have := h.bound; omega) h.depthRead
  cases returns <;>
    simp [seg, input, callClosureNormalDepthSeg, callClosureBodyExitRetSeg, callClosureRetClassSeg,
      evalBlocks, evalBlock, SegEvalState.init, wlogM, wentryM, widthOfM, runGM, stepGM,
      stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, eaddrM,
      value, decrement depth h.bound]
  all_goals have := h.geometry.hi; omega

/-- The depth word is restored; the return-copy or null-call instruction is next. -/
structure Post (interp sret : BitVec 64) (depth : Nat) (returns : Bool)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (exitPC returns)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ (selected interp sret returns)
  memory : after.σ.mem = writeLog before.σ.mem [(interp.toNat + 8, 4, BitVec.ofNat 64 depth)]
  outside : ∀ k, ¬ (interp.toNat + 8 ≤ k ∧ k < interp.toNat + 12) →
    before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiPreserved R = true → after.σ.regs.get? R = before.σ.regs.get? R

theorem run {interp sret : BitVec 64} {depth : Nat} {returns : Bool} {before : Config}
    (h : Pre interp sret depth returns before) :
    ∃ after, Steps before after ∧ Post interp sret depth returns before after := by
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (seg returns) (input interp sret returns)
    [wordLds4 before.σ.mem (interp.toNat + 8)] (entryPC returns) vm
    (fun k => interp.toNat + 8 ≤ k ∧ k < interp.toNat + 12) AbiPreserved
    (selected interp sret returns) before h.good h.pc hvm h.regs
    (by cases returns
        · change KeysOK [18, 9]; decide
        · change KeysOK [18, 9, 10]; decide) h.facts
    (by cases returns
        · change ChainOK 0x80003954#64 [18, 9] callClosureNormalDepthSeg; decide
        · change ChainOK 0x80003378#64 [18, 9, 10] (callClosureBodyExitRetSeg ++ callClosureRetClassSeg); decide) h.tick
    (by
      intro k hk
      rw [h.log]
      symm
      apply writeLog_out
      change (k < interp.toNat + 8 ∨ interp.toNat + 8 + 4 ≤ k) ∧ True
      exact ⟨by omega, trivial⟩)
    (by decide) (by cases returns <;> decide)
    (by cases returns <;> simp [GProjects, selected, seg, input, callClosureNormalDepthSeg,
      callClosureBodyExitRetSeg, callClosureRetClassSeg, evalBlocks, evalBlock, SegEvalState.init,
      runGM, stepGM, stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM])
  exact ⟨after, C.steps,
    { good := C.good, tick := C.tick, pc := by cases returns <;> exact C.pc
      minstret := C.minstret, regs := C.selected_regs
      memory := C.mem.trans (congrArg (writeLog before.σ.mem) h.log)
      outside := C.outside, output := C.output, frame := C.reg_frame }⟩

end Vsa.Sim.ClosureReturnDepth
