import Vsa.Sim.rows.LoopHeadDispatchSeg
import Vsa.Sim.WordLoadData
import Vsa.Sim.Code.Interp_run
import Vsa.Sim.SegEffect
import Vsa.Sim.FrameMeta

namespace Vsa.Sim.SeqInterpHead

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.Machine Vsa.Alloc

def keep (R : Register) : Bool := AbiPreserved R && !(R == Register.x9)

/-- Bounds for the script flag and selected statement pointer. -/
structure Geometry (sp cursor : BitVec 64) : Prop where
  stackLo : 0x80000000 ≤ sp.toNat + 8
  stackHi : sp.toNat + 16 ≤ 0x100000000
  stackHtif : sp.toNat + 16 ≤ tohostAddr ∨ tohostAddr + 8 ≤ sp.toNat + 8
  cursorLo : 0x80000000 ≤ cursor.toNat
  cursorHi : cursor.toNat + 8 ≤ 0x100000000
  cursorHtif : cursor.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ cursor.toNat

/-- The reflected branch reads the actual zero flag and statement pointer. -/
structure Data (m : Mem) (sp cursor stmt : BitVec 64)
    (flagBytes stmtBytes : List (BitVec 8)) : Prop where
  facts : ChainFacts m m (loopHeadDispatchL sp cursor) [flagBytes, stmtBytes]
    loopHeadDispatchSeg
  script : bytesVal .ld flagBytes = 0#64
  statement : bytesVal .ld stmtBytes = stmt

theorem data (m : Mem) (sp cursor stmt : BitVec 64)
    (G : Geometry sp cursor) (code : Code.Interp_runLoaded m)
    (script : read64 m (sp.toNat + 8) = some 0)
    (statement : read64 m cursor.toNat = some stmt.toNat) :
    ∃ flagBytes stmtBytes, Data m sp cursor stmt flagBytes stmtBytes := by
  let L := loopHeadDispatchL sp cursor
  let ldFlag := mkLine 0x8000448c#64 0x00813783#32
  let ldStmt := mkLine 0x80004490#64 0x00043483#32
  have flagAddr : (eaddrM ldFlag L).toNat = sp.toNat + 8 := by
    change (sp + 8#64).toNat = sp.toNat + 8
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := G.stackHi; change sp.toNat + 8 < 2^64; omega)]
    rfl
  obtain ⟨flagBytes, F⟩ := wordLoadFacts_of_read64 m L ldFlag 0#64 rfl
    (by rw [flagAddr]; exact G.stackLo) (by rw [flagAddr]; exact G.stackHi)
    (by rw [flagAddr]; exact G.stackHtif) (by rw [flagAddr]; exact script)
  have stmtAddr : (eaddrM ldStmt (stepGM ldFlag L flagBytes)).toNat = cursor.toNat := by
    change (cursor + 0#64).toNat = cursor.toNat
    rw [BitVec.add_zero]
  obtain ⟨stmtBytes, S⟩ := wordLoadFacts_of_read64 m (stepGM ldFlag L flagBytes)
    ldStmt stmt rfl (by rw [stmtAddr]; exact G.cursorLo)
    (by rw [stmtAddr]; exact G.cursorHi) (by rw [stmtAddr]; exact G.cursorHtif)
    (by rw [stmtAddr]; exact statement)
  refine ⟨flagBytes, stmtBytes, ?_, F.value, S.value⟩
  chain_facts code with "Vsa.Sim.Code.interp_run_at_"
  · exact F.facts
  · exact S.facts
  · change guardB bop.BEQ (bytesVal .ld flagBytes) 0#64 = true
    rw [F.value]
    rfl

/-- Dispatch selects the statement in s1 without changing memory. -/
structure Post (sp cursor stmt : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80004458#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  registers : GHolds after.σ [(2, sp), (8, cursor), (9, stmt)]
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, keep R = true → after.σ.regs.get? R = before.σ.regs.get? R
  count : after.steps = before.steps + 3

/-- Execute the existing loop-head span with its selected registers and full ABI frame. -/
theorem run (sp cursor stmt : BitVec 64) (before : Config)
    (G : Geometry sp cursor) (good : GoodState before.σ) (tick : before.tick < 2)
    (pc : before.σ.regs.get? Register.PC = some 0x8000448c#64)
    (minstret : ∃ w, before.σ.regs.get? Register.minstret = some w)
    (registers : GHolds before.σ (loopHeadDispatchL sp cursor))
    (code : Code.Interp_runLoaded before.σ.mem)
    (script : read64 before.σ.mem (sp.toNat + 8) = some 0)
    (statement : read64 before.σ.mem cursor.toNat = some stmt.toNat) :
    ∃ after, Steps before after ∧ Post sp cursor stmt before after := by
  obtain ⟨flagBytes, stmtBytes, D⟩ := data before.σ.mem sp cursor stmt G code script statement
  obtain ⟨vm, hvm⟩ := minstret
  obtain ⟨after, C⟩ := segEval_selected_counted loopHeadDispatchSeg
    (loopHeadDispatchL sp cursor) [flagBytes, stmtBytes] 0x8000448c#64 vm
    (fun _ => False) keep [(2, sp), (8, cursor), (9, stmt)] before good pc hvm
    registers (by change KeysOK [2, 8]; decide) D.facts
    (by change ChainOK 0x8000448c#64 [2, 8] loopHeadDispatchSeg; decide) tick
    (by intro k _; rfl) (by decide) (by decide) (by
      change some sp = some sp ∧ some cursor = some cursor ∧
        some (bytesVal .ld stmtBytes) = some stmt ∧ True
      simp only [D.statement, and_true])
  exact ⟨after, C.steps, C.good, C.tick, C.pc, C.minstret, C.selected_regs,
    C.mem, C.output, C.reg_frame, C.count⟩

#print axioms data
#print axioms run

end Vsa.Sim.SeqInterpHead
