import Vsa.Sim.ClosureReturnDepth
import Vsa.Sim.rows.CallClosureRetCopyGen

namespace Vsa.Sim.ClosureReturnJoin

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

def seg (returns : Bool) : List BBlock :=
  if returns then callClosureRetCopySeg else callClosureNormalJoinSeg
def entryPC (returns : Bool) : BitVec 64 := if returns then 0x8000339c#64 else 0x80003968#64
def keep (R : Register) : Bool := AbiPreserved R && !(R == .x19) && !(R == .x21) && !(R == .x23)
def loads (m : Mem) (sp : BitVec 64) (returns : Bool) : List (List (BitVec 8)) :=
  (if returns then [EvalChildArm.wordLds8 m (sp.toNat + 144),
    EvalChildArm.wordLds8 m (sp.toNat + 152), EvalChildArm.wordLds8 m (sp.toNat + 160)] else []) ++
  [EvalChildArm.wordLds8 m (sp.toNat + 1048), EvalChildArm.wordLds8 m (sp.toNat + 1032),
    EvalChildArm.wordLds8 m (sp.toNat + 1016)]
def writes (m : Mem) (sp sret : BitVec 64) (returns : Bool) : List WEntry :=
  if returns then
    [(sret.toNat, 8, bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 144))),
     (sret.toNat + 8, 8, bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 152))),
     (sret.toNat + 16, 8, bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 160)))]
  else []

/-- Physical source slots and the caller's value destination. -/
structure Geometry (sp sret : BitVec 64) : Prop where
  stackLo : 0x80000000 ≤ sp.toNat
  stackHi : sp.toNat + 1056 ≤ 0x100000000
  stackHtif : tohostAddr + 16 ≤ sp.toNat
  retLo : 0x80000000 ≤ sret.toNat
  retHi : sret.toNat + 24 ≤ 0x100000000
  retHtif : tohostAddr + 16 ≤ sret.toNat
  retAlign : sret.toNat % 8 = 0

/-- Actual return loads after depth restoration and, on normal exit, value_null. -/
structure Pre (sp sret saved5 saved3 saved7 : BitVec 64) (returns : Bool) (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some (entryPC returns)
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  regs : GHolds before.σ (callClosureRetCopyL sp sret)
  geometry : Geometry sp sret
  saved5Read : read64 before.σ.mem (sp.toNat + 1032) = some saved5.toNat
  saved3Read : read64 before.σ.mem (sp.toNat + 1048) = some saved3.toNat
  saved7Read : read64 before.σ.mem (sp.toNat + 1016) = some saved7.toNat
  code : Code.Eval_exprLoaded before.σ.mem

theorem Geometry.stackAddr {sp sret : BitVec 64} (G : Geometry sp sret)
    (off : Nat) (bound : off ≤ 1056) : (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 2^64 by omega),
    Nat.mod_eq_of_lt (show sp.toNat + off < 2^64 by have := G.stackHi; omega)]

theorem Geometry.retAddr {sp sret : BitVec 64} (G : Geometry sp sret)
    (off : Nat) (bound : off ≤ 24) : (sret + BitVec.ofNat 64 off).toNat = sret.toNat + off := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show off < 2^64 by omega),
    Nat.mod_eq_of_lt (show sret.toNat + off < 2^64 by have := G.retHi; omega)]

theorem Pre.facts {sp sret saved5 saved3 saved7 : BitVec 64} {returns : Bool} {before : Config}
    (h : Pre sp sret saved5 saved3 saved7 returns before) :
    ChainFacts before.σ.mem before.σ.mem (callClosureRetCopyL sp sret)
      (loads before.σ.mem sp returns) (seg returns) := by
  have loadFacts {L : GRegs} {a : MInstr} (off : Nat) (bound : off + 8 ≤ 1056)
      (kind : a.kind = .ld) (address : (eaddrM a L).toNat = sp.toNat + off) :
      MemFacts before.σ.mem L (EvalChildArm.wordLds8 before.σ.mem (sp.toNat + off)) a := by
    simp only [MemFacts, kind, address]
    exact ⟨⟨by have := h.geometry.stackLo; omega, by have := h.geometry.stackHi; omega,
      Or.inr (by have := h.geometry.stackHtif; omega)⟩, by simp [LPins8, EvalChildArm.wordLds8]⟩
  have storeFacts {m : Mem} {L : GRegs} {a : MInstr} (bs : List (BitVec 8))
      (off : Nat) (bound : off + 8 ≤ 24) (align : off % 8 = 0)
      (kind : a.kind = .sd) (address : (eaddrM a L).toNat = sret.toNat + off) : MemFacts m L bs a := by
    apply memFacts_sd_frame m L a bs kind
    · rw [address]; have := h.geometry.retLo; omega
    · rw [address]; have := h.geometry.retHi; omega
    · rw [address]; have := h.geometry.retHtif; omega
    · rw [address, Nat.add_mod, h.geometry.retAlign, align]
  cases returns <;> simp only [seg, Bool.false_eq_true, if_false, if_true]
  · chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
    · exact loadFacts 1048 (by decide) rfl (h.geometry.stackAddr _ (by decide))
    · exact loadFacts 1032 (by decide) rfl (h.geometry.stackAddr _ (by decide))
    · exact loadFacts 1016 (by decide) rfl (h.geometry.stackAddr _ (by decide))
  · chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
    · exact loadFacts 144 (by decide) rfl (h.geometry.stackAddr _ (by decide))
    · exact loadFacts 152 (by decide) rfl (h.geometry.stackAddr _ (by decide))
    · exact loadFacts 160 (by decide) rfl (h.geometry.stackAddr _ (by decide))
    · exact loadFacts 1048 (by decide) rfl (h.geometry.stackAddr _ (by decide))
    · exact loadFacts 1032 (by decide) rfl (h.geometry.stackAddr _ (by decide))
    · exact loadFacts 1016 (by decide) rfl (h.geometry.stackAddr _ (by decide))
    · exact storeFacts _ 0 (by decide) (by decide) rfl (h.geometry.retAddr _ (by decide))
    · exact storeFacts _ 8 (by decide) (by decide) rfl (h.geometry.retAddr _ (by decide))
    · exact storeFacts _ 16 (by decide) (by decide) rfl (h.geometry.retAddr _ (by decide))

theorem Pre.log {sp sret saved5 saved3 saved7 : BitVec 64} {returns : Bool} {before : Config}
    (h : Pre sp sret saved5 saved3 saved7 returns before) :
    (evalBlocks (seg returns) (SegEvalState.init (callClosureRetCopyL sp sret)
      (loads before.σ.mem sp returns))).log = writes before.σ.mem sp sret returns := by
  cases returns
  · rfl
  · simp [seg, writes, loads, callClosureRetCopySeg, callClosureRetCopyL, evalBlocks, evalBlock,
      SegEvalState.init, wlogM, wentryM, widthOfM, runGM, stepGM, stepLdsM, ldsRunM,
      wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, eaddrM]
    all_goals have := h.geometry.retHi; omega

/-- Both routes restore the caller registers and reach the shared eval_expr epilogue. -/
structure Post (sp sret saved5 saved3 saved7 : BitVec 64) (returns : Bool)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x800033ec#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ [(2, sp), (9, sret), (19, saved3), (21, saved5), (23, saved7)]
  memory : after.σ.mem = writeLog before.σ.mem (writes before.σ.mem sp sret returns)
  copied : returns = true → ∀ j, j < 24 →
    after.σ.mem[sret.toNat + j]? = some ((before.σ.mem[sp.toNat + 144 + j]?).getD 0)
  outside : ∀ k, ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → before.σ.mem[k]? = after.σ.mem[k]?
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, keep R = true → after.σ.regs.get? R = before.σ.regs.get? R

theorem run {sp sret saved5 saved3 saved7 : BitVec 64} {returns : Bool} {before : Config}
    (h : Pre sp sret saved5 saved3 saved7 returns before) :
    ∃ after, Steps before after ∧ Post sp sret saved5 saved3 saved7 returns before after := by
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (seg returns) (callClosureRetCopyL sp sret)
    (loads before.σ.mem sp returns) (entryPC returns) vm
    (fun k => sret.toNat ≤ k ∧ k < sret.toNat + 24) keep
    [(2, sp), (9, sret), (19, saved3), (21, saved5), (23, saved7)] before
    h.good h.pc hvm h.regs (by change KeysOK [2, 9]; decide) h.facts
    (by cases returns
        · change ChainOK 0x80003968#64 [2, 9] callClosureNormalJoinSeg; decide
        · change ChainOK 0x8000339c#64 [2, 9] callClosureRetCopySeg; decide) h.tick
    (by
      intro k hk
      rw [h.log]
      symm
      apply writeLog_out
      cases returns
      · trivial
      · simp only [writes, if_true, OutL, and_true]
        exact ⟨by omega, by omega, by omega⟩)
    (by decide) (by cases returns <;> decide)
    (by
      have s5 := EvalChildArm.bytesVal_ld_wordLds before.σ.mem (sp.toNat + 1032) saved5 h.saved5Read
      have s3 := EvalChildArm.bytesVal_ld_wordLds before.σ.mem (sp.toNat + 1048) saved3 h.saved3Read
      have s7 := EvalChildArm.bytesVal_ld_wordLds before.σ.mem (sp.toNat + 1016) saved7 h.saved7Read
      cases returns <;> simp [GProjects, seg, loads, callClosureRetCopyL, callClosureRetCopySeg,
        callClosureNormalJoinSeg, evalBlocks, evalBlock, SegEvalState.init, runGM, stepGM,
        stepLdsM, ldsRunM, wvalM, srcVal, lookupG, eraseG, mkLine, decodeM, s5, s3, s7])
  refine ⟨after, C.steps,
    { good := C.good, tick := C.tick, pc := by cases returns <;> exact C.pc
      minstret := C.minstret, regs := C.selected_regs
      memory := C.mem.trans (congrArg (writeLog before.σ.mem) h.log)
      copied := ?_, outside := C.outside, output := C.output, frame := C.reg_frame }⟩
  intro ret
  subst returns
  rw [C.mem, h.log]
  have memory : writeLog before.σ.mem (writes before.σ.mem sp sret true) =
      copy3Log before.σ.mem (sp.toNat + 144) sret.toNat := by
    simp only [writes, if_true, copy3Log, show sp.toNat + 144 + 8 = sp.toNat + 152 by omega,
      show sp.toNat + 144 + 16 = sp.toNat + 160 by omega]
    rfl
  rw [memory]
  exact copy3_total _ _ _

end Vsa.Sim.ClosureReturnJoin
