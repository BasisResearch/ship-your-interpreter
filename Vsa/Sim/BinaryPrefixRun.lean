import Vsa.Sim.BinaryPrefixSegments
import Vsa.Sim.InterpSpillReads

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.Machine

namespace Vsa.Sim.BinaryPrefix

/-- Execute the generated left prefix, retaining its exact stores and ABI frame. -/
theorem first_counted (node sp saved env left : BitVec 64) (bs : List (BitVec 8))
    (c : Config) (hg : GoodState c.σ) (ht : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x800034e8#64)
    (hregs : GHolds c.σ (firstInput node sp saved env))
    (hfacts : ChainFacts c.σ.mem c.σ.mem (firstInput node sp saved env) [bs] firstSeg)
    (hleft : bytesVal .ld bs = left) (hsp : sp.toNat + 1056 ≤ 0x100000000) :
    ∃ after, CountedSelectedFramedSegResult firstSeg (firstInput node sp saved env) [bs]
      0x800034e8#64 (firstFoot sp) firstKeep
      [(12, left), (10, sp + 120#64), (2, sp), (19, saved), (13, env)] c after := by
  obtain ⟨vm, hvm⟩ := hg.minstret
  apply segEval_selected_counted firstSeg (firstInput node sp saved env) [bs]
    0x800034e8#64 vm (firstFoot sp) firstKeep _ c hg hpc hvm hregs
    (by show KeysOK [12, 2, 19, 13]; decide) hfacts
    (by show ChainOK 0x800034e8#64 [12, 2, 19, 13] firstSeg; decide) ht
  · rw [first_log node sp saved env bs hsp]
    exact first_outside c.σ.mem sp saved env
  · decide
  · decide
  · exact first_regs node sp saved env left bs hleft

/-- Execute the right prefix from the actual left-result words. -/
theorem second_counted (node sp interp right env kind payload : BitVec 64)
    (br be bk bp : List (BitVec 8))
    (c : Config) (hg : GoodState c.σ) (ht : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x800034fc#64)
    (hregs : GHolds c.σ (secondInput node sp interp))
    (hfacts : ChainFacts c.σ.mem c.σ.mem (secondInput node sp interp)
      [br, be, bk, bp] secondSeg)
    (hr : bytesVal .ld br = right) (he : bytesVal .ld be = env)
    (hk : bytesVal .lw bk = kind) (hp : bytesVal .ld bp = payload) :
    ∃ after, CountedSelectedFramedSegResult secondSeg (secondInput node sp interp)
      [br, be, bk, bp] 0x800034fc#64 (secondFoot sp) secondKeep
      [(12, right), (13, env), (16, kind), (10, sp + 144#64), (11, interp),
       (19, payload), (2, sp), (8, node), (18, interp)] c after := by
  obtain ⟨vm, hvm⟩ := hg.minstret
  apply segEval_selected_counted secondSeg (secondInput node sp interp)
    [br, be, bk, bp] 0x800034fc#64 vm (secondFoot sp) secondKeep _ c hg hpc hvm hregs
    (by show KeysOK [8, 2, 18]; decide) hfacts
    (by show ChainOK 0x800034fc#64 [8, 2, 18] secondSeg; decide) ht
  · rw [second_log]
    exact second_outside c.σ.mem sp (bytesVal .lw bk)
  · decide
  · decide
  · exact second_regs node sp interp right env kind payload br be bk bp hr he hk hp

/-- The first prefix supplies both saved words needed after the left child. -/
structure FirstSaved (m : Mem) (sp saved env : BitVec 64) : Prop where
  saved : read64 m (sp.toNat + 1048) = some saved.toNat
  environment : read64 m sp.toNat = some env.toNat

theorem first_saved (m : Mem) (sp saved env : BitVec 64) :
    FirstSaved (writeLog m (firstLog sp saved env)) sp saved env := by
  constructor
  · exact read64_of_writeLog_at m (firstLog sp saved env) 0 _ _ rfl
      (by simp [firstLog, OutLRange, Nat.add_assoc])
  · exact read64_of_writeLog_at m (firstLog sp saved env) 1 _ _ rfl
      (by simp [firstLog, OutLRange, Nat.add_assoc])

#print axioms first_counted
#print axioms second_counted
#print axioms first_saved


/-- Project the original prefix result from the counted execution. -/
theorem first_framed (node sp saved env left : BitVec 64) (bs : List (BitVec 8))
    (c : Config) (hg : GoodState c.σ) (ht : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x800034e8#64)
    (hregs : GHolds c.σ (firstInput node sp saved env))
    (hfacts : ChainFacts c.σ.mem c.σ.mem (firstInput node sp saved env) [bs] firstSeg)
    (hleft : bytesVal .ld bs = left) (hsp : sp.toNat + 1056 ≤ 0x100000000) :
    ∃ after, SelectedFramedSegResult firstSeg (firstInput node sp saved env) [bs]
      0x800034e8#64 (firstFoot sp) firstKeep
      [(12, left), (10, sp + 120#64), (2, sp), (19, saved), (13, env)] c after := by
  obtain ⟨after, result⟩ := first_counted node sp saved env left bs c hg ht hpc hregs hfacts hleft hsp
  exact ⟨after, result.toSelectedFramedSegResult⟩

/-- Project the original prefix result from the counted execution. -/
theorem second_framed (node sp interp right env kind payload : BitVec 64)
    (br be bk bp : List (BitVec 8))
    (c : Config) (hg : GoodState c.σ) (ht : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x800034fc#64)
    (hregs : GHolds c.σ (secondInput node sp interp))
    (hfacts : ChainFacts c.σ.mem c.σ.mem (secondInput node sp interp)
      [br, be, bk, bp] secondSeg)
    (hr : bytesVal .ld br = right) (he : bytesVal .ld be = env)
    (hk : bytesVal .lw bk = kind) (hp : bytesVal .ld bp = payload) :
    ∃ after, SelectedFramedSegResult secondSeg (secondInput node sp interp)
      [br, be, bk, bp] 0x800034fc#64 (secondFoot sp) secondKeep
      [(12, right), (13, env), (16, kind), (10, sp + 144#64), (11, interp),
       (19, payload), (2, sp), (8, node), (18, interp)] c after := by
  obtain ⟨after, result⟩ := second_counted node sp interp right env kind payload br be bk bp c hg ht hpc hregs hfacts hr he hk hp
  exact ⟨after, result.toSelectedFramedSegResult⟩

#print axioms first_framed
#print axioms second_framed

end Vsa.Sim.BinaryPrefix
