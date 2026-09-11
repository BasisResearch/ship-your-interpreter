import Vsa.Sim.rows.CallClosureBodyEntry
import Vsa.Sim.rows.StrdupTailJalSeams
import Vsa.Sim.HelperCall
import Vsa.Sim.WordLoadData
import Vsa.Sim.SegEffect
import Vsa.Sim.FrameMeta

namespace Vsa.Sim.ClosureBodyDispatch

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

def seg (nonempty : Bool) : List BBlock :=
  if nonempty then callClosureBodyEntrySeg else callClosureBodyBypassSeg

def exitPC (nonempty : Bool) : BitVec 64 :=
  if nonempty then 0x80003354#64 else 0x80003954#64

/-- Bounds for the closure's body pointer and the body's statement count. -/
structure Geometry (closure body : BitVec 64) : Prop where
  closureLo : 0x80000000 ≤ closure.toNat + 32
  closureHi : closure.toNat + 40 ≤ 0x100000000
  closureHtif : closure.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 8 ≤ closure.toNat + 32
  bodyLo : 0x80000000 ≤ body.toNat + 16
  bodyHi : body.toNat + 20 ≤ 0x100000000
  bodyHtif : body.toNat + 20 ≤ tohostAddr ∨ tohostAddr + 8 ≤ body.toNat + 16

/-- The represented body determines both loads and the entry branch. -/
structure Pre (closure body : BitVec 64) (count : Nat) (nonempty : Bool)
    (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x8000332c#64
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  closureReg : before.σ.regs.get? Register.x21 = some closure
  geometry : Geometry closure body
  bodyRead : read64 before.σ.mem (closure.toNat + 32) = some body.toNat
  countRead : read32 before.σ.mem (body.toNat + 16) = some count
  countBound : count < 2^31
  branch : decide (0 < count) = nonempty
  code : Code.Eval_exprLoaded before.σ.mem

/-- Derive reflected load facts from the reached closure and body header. -/
theorem Pre.facts {closure body : BitVec 64} {count : Nat} {nonempty : Bool} {before : Config}
    (h : Pre closure body count nonempty before) :
    ∃ bodyBytes,
      ChainFacts before.σ.mem before.σ.mem (callClosureBodyEntryL closure)
        [bodyBytes, wordLds4 before.σ.mem (body.toNat + 16)] (seg nonempty) ∧
      bytesVal .ld bodyBytes = body := by
  let L := callClosureBodyEntryL closure
  let ldBody := mkLine 0x8000332c#64 0x020ab803#32
  let zeroIndex := mkLine 0x80003330#64 0x00000413#32
  let ldCount := mkLine 0x80003334#64 0x01082783#32
  have bodyAddr : (eaddrM ldBody L).toNat = closure.toNat + 32 := by
    change (closure + 32#64).toNat = closure.toNat + 32
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := h.geometry.closureHi; change closure.toNat + 32 < 2^64; omega)]
    rfl
  obtain ⟨bodyBytes, B⟩ := wordLoadFacts_of_read64 before.σ.mem L ldBody body rfl
    (by rw [bodyAddr]; exact h.geometry.closureLo)
    (by rw [bodyAddr]; exact h.geometry.closureHi)
    (by rw [bodyAddr]; exact h.geometry.closureHtif)
    (by rw [bodyAddr]; exact h.bodyRead)
  let Lcount := runGM [ldBody, zeroIndex] L [bodyBytes]
  have countAddr : (eaddrM ldCount Lcount).toNat = body.toNat + 16 := by
    change (bytesVal .ld bodyBytes + 16#64).toNat = body.toNat + 16
    rw [B.value, BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := h.geometry.bodyHi; change body.toNat + 16 < 2^64; omega)]
    rfl
  have countFacts : MemFacts before.σ.mem Lcount
      (wordLds4 before.σ.mem (body.toNat + 16)) ldCount := by
    unfold MemFacts
    change (0x80000000 ≤ (eaddrM ldCount Lcount).toNat ∧
      (eaddrM ldCount Lcount).toNat + 4 ≤ 0x100000000 ∧
      ((eaddrM ldCount Lcount).toNat + 4 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (eaddrM ldCount Lcount).toNat)) ∧ _
    rw [countAddr]
    exact ⟨⟨h.geometry.bodyLo, h.geometry.bodyHi, h.geometry.bodyHtif⟩,
      by simp [LPins4, wordLds4]⟩
  have countValue := bytesVal_lw_wordLds4 before.σ.mem (body.toNat + 16) count
    h.countBound h.countRead
  have signed : (BitVec.ofNat 64 count).toInt = (count : Int) := by
    rw [BitVec.toInt_eq_toNat_cond, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by have := h.countBound; omega), if_pos (by have := h.countBound; omega)]
  have branch : guardB bop.BLT (0#64) (BitVec.ofNat 64 count) = nonempty := by
    unfold guardB zopz0zI_s
    rw [signed]
    change decide ((0 : Int) < (count : Int)) = nonempty
    simpa only [Int.natCast_pos] using h.branch
  refine ⟨bodyBytes, ?_, B.value⟩
  cases nonempty <;> simp only [seg, Bool.false_eq_true, if_false, if_true]
  all_goals
    chain_facts h.code with "Vsa.Sim.Code.eval_expr_at_"
    · exact B.facts
    · exact countFacts
    · change guardB bop.BLT (0#64)
        (bytesVal .lw (wordLds4 before.σ.mem (body.toNat + 16))) = _
      rw [countValue]
      exact branch

/-- Both body-entry routes retain the selected body, zero index, and exact memory. -/
structure Post (body : BitVec 64) (nonempty : Bool) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some (exitPC nonempty)
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  bodyReg : after.σ.regs.get? Register.x16 = some body
  indexReg : after.σ.regs.get? Register.x8 = some 0#64
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, AbiExceptS0 R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Execute the existing body-entry segment at its represented count. -/
theorem run {closure body : BitVec 64} {count : Nat} {nonempty : Bool} {before : Config}
    (h : Pre closure body count nonempty before) :
    ∃ after, Steps before after ∧ Post body nonempty before after := by
  obtain ⟨bodyBytes, facts, bodyValue⟩ := h.facts
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed (seg nonempty) (callClosureBodyEntryL closure)
    [bodyBytes, wordLds4 before.σ.mem (body.toNat + 16)] 0x8000332c#64 vm
    (fun _ => False) AbiExceptS0 [(16, body), (8, 0#64)] before
    h.good h.pc hvm ⟨h.closureReg, trivial⟩ (by change KeysOK [21]; decide) facts
    (by cases nonempty <;> change ChainOK 0x8000332c#64 [21] _ <;> decide) h.tick
    (by intro k _; cases nonempty <;> rfl) (by decide) (by cases nonempty <;> decide) (by
      cases nonempty <;> change some (bytesVal .ld bodyBytes) = some body ∧
        some 0#64 = some 0#64 ∧ True
      all_goals simp only [bodyValue, and_true])
  obtain ⟨bodyReg, indexReg, _⟩ := C.selected_regs
  refine ⟨after, C.steps,
    { good := C.good, tick := C.tick, pc := ?_, minstret := C.minstret
      bodyReg := bodyReg, indexReg := indexReg, memory := ?_, output := C.output
      frame := C.reg_frame }⟩
  · cases nonempty <;> exact C.pc
  · cases nonempty <;> exact C.mem

#print axioms Pre.facts
#print axioms run

end Vsa.Sim.ClosureBodyDispatch
