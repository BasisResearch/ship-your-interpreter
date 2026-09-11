import Vsa.Sim.SegEffect
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.WriteLogNF

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.Machine

namespace Vsa.Sim.BinaryPrefix

#derive_case firstSeg chain
  [(0x800034e8#64, 0x01063603#32),
   (0x800034ec#64, 0x07810513#32),
   (0x800034f0#64, 0x41313c23#32),
   (0x800034f4#64, 0x00d13023#32)]

#derive_case secondSeg chain
  [(0x800034fc#64, 0x01843603#32),
   (0x80003500#64, 0x00013683#32),
   (0x80003504#64, 0x07812803#32),
   (0x80003508#64, 0x09010513#32),
   (0x8000350c#64, 0x00090593#32),
   (0x80003510#64, 0x08013983#32),
   (0x80003514#64, 0x01013023#32)]

def firstInput (node sp saved env : BitVec 64) : GRegs :=
  [(12, node), (2, sp), (19, saved), (13, env)]

def secondInput (node sp interp : BitVec 64) : GRegs :=
  [(8, node), (2, sp), (18, interp)]

def firstKeep (R : Register) : Bool :=
  !(noiseRegs.contains R) && R != Register.x10 && R != Register.x12

def secondKeep (R : Register) : Bool :=
  !(noiseRegs.contains R) &&
    !([Register.x10, .x11, .x12, .x13, .x16, .x19].contains R)

def firstLog (sp saved env : BitVec 64) : List WEntry :=
  [(sp.toNat + 1048, 8, saved), (sp.toNat, 8, env)]

def firstFoot (sp : BitVec 64) (k : Nat) : Prop :=
  (sp.toNat + 1048 ≤ k ∧ k < sp.toNat + 1056) ∨
  (sp.toNat ≤ k ∧ k < sp.toNat + 8)

def secondFoot (sp : BitVec 64) (k : Nat) : Prop :=
  sp.toNat ≤ k ∧ k < sp.toNat + 8

/-- The left argument prefix writes only its two saved words. -/
theorem first_log (node sp saved env : BitVec 64) (bs : List (BitVec 8))
    (hsp : sp.toNat + 1056 ≤ 0x100000000) :
    (evalBlocks firstSeg (SegEvalState.init (firstInput node sp saved env) [bs])).log =
      firstLog sp saved env := by
  change [((sp + sign_extend (m := 64) (0x418#12)).toNat, 8, saved),
    ((sp + sign_extend (m := 64) (0#12)).toNat, 8, env)] = _
  rw [show sign_extend (m := 64) (0x418#12) = 1048#64 from by decide,
    show sign_extend (m := 64) (0#12) = 0#64 from by decide, BitVec.add_zero]
  simp only [BitVec.toNat_add]
  change [((sp.toNat + 1048) % 2^64, 8, saved), (sp.toNat, 8, env)] = _
  rw [Nat.mod_eq_of_lt (by omega)]
  rfl

/-- The right argument prefix respills the left kind into the argument slot. -/
theorem second_log (node sp interp : BitVec 64)
    (right env kind payload : List (BitVec 8)) :
    (evalBlocks secondSeg (SegEvalState.init (secondInput node sp interp)
      [right, env, kind, payload])).log = [(sp.toNat, 8, bytesVal .lw kind)] := by
  change [((sp + sign_extend (m := 64) (0#12)).toNat, 8, bytesVal .lw kind)] = _
  rw [show sign_extend (m := 64) (0#12) = 0#64 from by decide, BitVec.add_zero]

theorem first_outside (m : Mem) (sp saved env : BitVec 64) :
    ∀ k, ¬ firstFoot sp k → m[k]? = (writeLog m (firstLog sp saved env))[k]? := by
  intro k hk
  apply (writeLog_out m (firstLog sp saved env) k ?_).symm
  simp only [firstLog, OutL, and_true]
  unfold firstFoot at hk
  omega

theorem second_outside (m : Mem) (sp kind : BitVec 64) :
    ∀ k, ¬ secondFoot sp k → m[k]? = (writeLog m [(sp.toNat, 8, kind)])[k]? := by
  intro k hk
  apply (writeLog_out m [(sp.toNat, 8, kind)] k ?_).symm
  simp only [OutL, and_true]
  unfold secondFoot at hk
  omega

theorem first_regs (node sp saved env left : BitVec 64) (bs : List (BitVec 8))
    (hleft : bytesVal .ld bs = left) :
    GProjects (evalBlocks firstSeg (SegEvalState.init (firstInput node sp saved env) [bs])).regs
      [(12, left), (10, sp + 120#64), (2, sp), (19, saved), (13, env)] := by
  change some (bytesVal .ld bs) = some left ∧
    some (sp + sign_extend (m := 64) (0x078#12)) = some (sp + 120#64) ∧
    some sp = some sp ∧ some saved = some saved ∧ some env = some env ∧ True
  simp only [hleft,
    show sign_extend (m := 64) (0x078#12) = 120#64 from by decide, and_true]

theorem second_regs (node sp interp right env kind payload : BitVec 64)
    (br be bk bp : List (BitVec 8))
    (hr : bytesVal .ld br = right) (he : bytesVal .ld be = env)
    (hk : bytesVal .lw bk = kind) (hp : bytesVal .ld bp = payload) :
    GProjects (evalBlocks secondSeg (SegEvalState.init (secondInput node sp interp)
      [br, be, bk, bp])).regs
      [(12, right), (13, env), (16, kind), (10, sp + 144#64), (11, interp),
       (19, payload), (2, sp), (8, node), (18, interp)] := by
  change some (bytesVal .ld br) = some right ∧ some (bytesVal .ld be) = some env ∧
    some (bytesVal .lw bk) = some kind ∧
    some (sp + sign_extend (m := 64) (0x090#12)) = some (sp + 144#64) ∧
    some (interp + sign_extend (m := 64) (0#12)) = some interp ∧
    some (bytesVal .ld bp) = some payload ∧ some sp = some sp ∧
    some node = some node ∧ some interp = some interp ∧ True
  simp only [hr, he, hk, hp,
    show sign_extend (m := 64) (0x090#12) = 144#64 from by decide,
    show sign_extend (m := 64) (0#12) = 0#64 from by decide, BitVec.add_zero, and_true]

#print axioms first_log
#print axioms second_log
#print axioms first_outside
#print axioms second_outside
#print axioms first_regs
#print axioms second_regs

end Vsa.Sim.BinaryPrefix
