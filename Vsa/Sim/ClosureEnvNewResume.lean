import Vsa.Sim.rows.CallClosureEnvNewRet
import Vsa.Sim.rows.StrdupTailJalSeams
import Vsa.Sim.WordLoadData
import Vsa.Sim.InterpSpillReads
import Vsa.Sim.SegEffect
import Vsa.Sim.FrameMeta
import Vsa.Sim.HelperCall

namespace Vsa.Sim.ClosureEnvNewResume

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

def seg (hasParams : Bool) : List BBlock :=
  if hasParams then callClosureEnvNewRetFoldSeg else callClosureEnvNewRetBypassSeg

def exitPC (hasParams : Bool) : BitVec 64 :=
  if hasParams then 0x800032dc#64 else 0x80003324#64

def keep (R : Register) : Bool :=
  AbiPreserved R && !(R == .x8) && !(R == .x19) && !(R == .x22)

def writes (sp savedS6 : BitVec 64) (hasParams : Bool) : List WEntry :=
  if hasParams then [(sp.toNat + 1024, 8, savedS6)] else []

def selected (sp fresh savedS6 : BitVec 64) (count : Nat) (hasParams : Bool) : GRegs :=
  [(2, sp), (19, fresh)] ++
    if hasParams then [(8, sp + 240#64), (22, BitVec.ofNat 64 count <<< 3), (15, 0#64)]
    else [(22, savedS6), (15, BitVec.ofNat 64 count)]

/-- Stack bounds for the saved argument count and caller's s6 slot. -/
structure Geometry (sp : BitVec 64) : Prop where
  lo : 0x80000000 ≤ sp.toNat
  hi : sp.toNat + 1032 ≤ 0x100000000
  htif : tohostAddr + 16 ≤ sp.toNat
  align : sp.toNat % 8 = 0

/-- The saved count selects either parameter binding or immediate body setup. -/
structure Pre (sp fresh savedS6 : BitVec 64) (count : Nat) (hasParams : Bool)
    (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x800032c0#64
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  regs : GHolds before.σ (callClosureEnvNewRetL sp fresh savedS6)
  geometry : Geometry sp
  countRead : read64 before.σ.mem sp.toNat = some count
  countBound : count < 2^31
  branch : decide (0 < count) = hasParams
  code : Code.Eval_exprLoaded before.σ.mem

theorem Geometry.spillAddr {sp : BitVec 64} (h : Geometry sp) :
    (sp + 1024#64).toNat = sp.toNat + 1024 := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
    have := h.hi; change sp.toNat + 1024 < 2^64; omega)]
  rfl

theorem Pre.facts {sp fresh savedS6 : BitVec 64} {count : Nat} {hasParams : Bool}
    {before : Config} (h : Pre sp fresh savedS6 count hasParams before) :
    ∃ countBytes,
      ChainFacts before.σ.mem before.σ.mem (callClosureEnvNewRetL sp fresh savedS6)
        [countBytes] (seg hasParams) ∧
      bytesVal .ld countBytes = BitVec.ofNat 64 count := by
  let L := callClosureEnvNewRetL sp fresh savedS6
  let ldCount := mkLine 0x800032c0#64 0x00013783#32
  have addr : (eaddrM ldCount L).toNat = sp.toNat := by
    change (sp + 0#64).toNat = sp.toNat
    rw [BitVec.add_zero]
  obtain ⟨countBytes, B⟩ := wordLoadFacts_of_read64 before.σ.mem L ldCount
    (BitVec.ofNat 64 count) rfl
    (by rw [addr]; exact h.geometry.lo)
    (by rw [addr]; have := h.geometry.hi; omega)
    (by rw [addr]; right; have := h.geometry.htif; omega)
    (by rw [addr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := h.countBound; omega)]
        exact h.countRead)
  have signed : (BitVec.ofNat 64 count).toInt = (count : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := h.countBound; omega),
      if_pos (by have := h.countBound; omega)]
  have branch : guardB bop.BGE (0#64) (bytesVal .ld countBytes) = !hasParams := by
    rw [B.value]
    unfold guardB zopz0zKzJ_s
    rw [signed]
    change decide ((count : Int) ≤ 0) = !hasParams
    rw [← h.branch]
    by_cases pos : 0 < count
    · simp [pos, show count ≠ 0 by omega]
    · simp [show count = 0 by omega]
  refine ⟨countBytes, ?_, B.value⟩
  cases hasParams <;> simp only [seg, Bool.false_eq_true, if_false, if_true]
  · chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
    · exact B.facts
    · exact branch
  · chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
    · exact B.facts
    · exact branch
    · apply memFacts_sd_frame
      · rfl
      · change 0x80000000 ≤ (sp + 1024#64).toNat
        rw [h.geometry.spillAddr]
        have := h.geometry.lo; omega
      · change (sp + 1024#64).toNat + 8 ≤ 0x100000000
        rw [h.geometry.spillAddr]
        exact h.geometry.hi
      · change tohostAddr + 16 ≤ (sp + 1024#64).toNat
        rw [h.geometry.spillAddr]
        have := h.geometry.htif; omega
      · change (sp + 1024#64).toNat % 8 = 0
        rw [h.geometry.spillAddr]
        have := h.geometry.align; omega

theorem log (sp fresh savedS6 : BitVec 64) (hasParams : Bool)
    (countBytes : List (BitVec 8)) (G : Geometry sp) :
    (evalBlocks (seg hasParams) (SegEvalState.init
      (callClosureEnvNewRetL sp fresh savedS6) [countBytes])).log =
      writes sp savedS6 hasParams := by
  cases hasParams
  · rfl
  · change [((sp + 1024#64).toNat, 8, savedS6)] = [(sp.toNat + 1024, 8, savedS6)]
    rw [G.spillAddr]

/-- The reached route retains the fresh scope, exact stack write, and caller frame. -/
structure Post (sp fresh savedS6 : BitVec 64) (count : Nat) (hasParams : Bool)
    (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (exitPC hasParams)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  regs : GHolds after.σ (selected sp fresh savedS6 count hasParams)
  memory : after.σ.mem = writeLog before.σ.mem (writes sp savedS6 hasParams)
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, keep R = true → after.σ.regs.get? R = before.σ.regs.get? R

theorem run {sp fresh savedS6 : BitVec 64} {count : Nat} {hasParams : Bool}
    {before : Config} (h : Pre sp fresh savedS6 count hasParams before) :
    ∃ after, Steps before after ∧ Post sp fresh savedS6 count hasParams before after := by
  obtain ⟨countBytes, facts, value⟩ := h.facts
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (seg hasParams)
    (callClosureEnvNewRetL sp fresh savedS6) [countBytes] 0x800032c0#64 vm
    (fun k => sp.toNat + 1024 ≤ k ∧ k < sp.toNat + 1032) keep
    (selected sp fresh savedS6 count hasParams) before
    h.good h.pc hvm h.regs (by change KeysOK [2, 10, 22]; decide) facts
    (by cases hasParams <;> change ChainOK 0x800032c0#64 [2, 10, 22] _ <;> decide)
    h.tick (by
      intro k hk
      change ¬ (sp.toNat + 1024 ≤ k ∧ k < sp.toNat + 1032) at hk
      rw [log sp fresh savedS6 hasParams countBytes h.geometry]
      symm
      apply writeLog_out
      cases hasParams
      · trivial
      · change (k < sp.toNat + 1024 ∨ sp.toNat + 1024 + 8 ≤ k) ∧ True
        exact ⟨by omega, trivial⟩)
    (by decide) (by cases hasParams <;> decide) (by
      cases hasParams
      · change some sp = some sp ∧ some (fresh + 0#64) = some fresh ∧
          some savedS6 = some savedS6 ∧ some (bytesVal .ld countBytes) =
          some (BitVec.ofNat 64 count) ∧ True
        simp only [value, BitVec.add_zero, and_true]
      · change some sp = some sp ∧ some (fresh + 0#64) = some fresh ∧
          some (sp + 240#64) = some (sp + 240#64) ∧
          some (bytesVal .ld countBytes <<< 3) = some (BitVec.ofNat 64 count <<< 3) ∧
          some 0#64 = some 0#64 ∧ True
        simp only [value, BitVec.add_zero, and_true])
  exact ⟨after, C.steps,
    { good := C.good, tick := C.tick, pc := by cases hasParams <;> exact C.pc
      minstret := C.minstret, regs := C.selected_regs
      memory := C.mem.trans (congrArg (writeLog before.σ.mem)
        (log sp fresh savedS6 hasParams countBytes h.geometry))
      output := C.output, frame := C.reg_frame }⟩

#print axioms Pre.facts
#print axioms run

end Vsa.Sim.ClosureEnvNewResume
