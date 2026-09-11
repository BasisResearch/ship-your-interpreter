import Vsa.Sim.CallArgStage
import Vsa.Sim.rows.ArgsReturnCopy
import Vsa.Sim.BinarySecondData
import Vsa.Sim.RuntimeOwnershipCopy
import Vsa.Sim.HelperCall

namespace Vsa.Sim.CallArgReturn

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

def seg (more : Bool) : List BBlock := if more then argsReturnMoreSeg else argsReturnDoneSeg
def nextPC (more : Bool) : BitVec 64 := if more then 0x800031dc#64 else 0x80003254#64
def slot (sp : BitVec 64) (index : Nat) : Nat := sp.toNat + 240 + 24 * index
def loads (m : Mem) (sp : BitVec 64) : List (List (BitVec 8)) :=
  [EvalChildArm.wordLds8 m (sp.toNat + 64), EvalChildArm.wordLds8 m sp.toNat,
   EvalChildArm.wordLds8 m (sp.toNat + 16), EvalChildArm.wordLds8 m (sp.toNat + 24),
   EvalChildArm.wordLds8 m (sp.toNat + 72), EvalChildArm.wordLds8 m (sp.toNat + 8),
   EvalChildArm.wordLds8 m (sp.toNat + 80)]
def writes (m : Mem) (sp : BitVec 64) (index : Nat) : List WEntry :=
  [(slot sp index, 8, bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 64))),
   (slot sp index + 8, 8, bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 72))),
   (slot sp index + 16, 8, bytesVal .ld (EvalChildArm.wordLds8 m (sp.toNat + 80)))]

/-- Resolve each signed store displacement to the indexed argument slot. -/
theorem storeAddress {node base sp : BitVec 64} {index count : Nat}
    (G : CallArgStage.Geometry node base sp index count) (off : Nat) (bound : off ≤ 16) :
    (CallArgStage.destination sp index + BitVec.ofNat 64 (2^64 - 768 + off)).toNat =
      slot sp index + off := by
  rw [BitVec.toNat_add, G.destinationAddress, BitVec.toNat_ofNat]
  have := G.caller.stackHi
  have := G.indexBound
  have := G.countBound
  unfold slot
  omega

/-- Each copied word lies inside the aligned caller argument array. -/
theorem storeFacts {node base sp : BitVec 64} {index count : Nat}
    (G : CallArgStage.Geometry node base sp index count) {m : Mem} {L : GRegs}
    {a : MInstr} {bs : List (BitVec 8)} (off : Nat) (bound : off ≤ 16) (aligned : off % 8 = 0)
    (kind : a.kind = .sd) (address : (eaddrM a L).toNat = slot sp index + off) :
    MemFacts m L bs a := by
  apply memFacts_sd_frame m L a bs kind
  all_goals
    rw [address]
    unfold slot
    have := G.caller.stackLo
    have := G.caller.stackHi
    have := G.caller.stackHtif
    have := G.caller.stackAlign
    have := G.indexBound
    have := G.countBound
    omega

/-- The reflected stores copy exactly the returned three words. -/
theorem log {node base sp : BitVec 64} {index count : Nat}
    (G : CallArgStage.Geometry node base sp index count) (m : Mem) (env : BitVec 64)
    (saved : CallArgStage.Saved m sp env index count) (more : Bool) :
    (evalBlocks (seg more) (SegEvalState.init (argsReturnL sp) (loads m sp))).log = writes m sp index := by
  have value := EvalChildArm.bytesVal_ld_wordLds m sp.toNat (CallArgStage.destination sp index) saved.destinationRead
  have d0 : sign_extend (m := 64) (0xd00#12) = BitVec.ofNat 64 (2^64 - 768 + 0) := by decide
  have d8 : sign_extend (m := 64) (0xd08#12) = BitVec.ofNat 64 (2^64 - 768 + 8) := by decide
  have d16 : sign_extend (m := 64) (0xd10#12) = BitVec.ofNat 64 (2^64 - 768 + 16) := by decide
  cases more <;>
    change [((bytesVal .ld (EvalChildArm.wordLds8 m sp.toNat) + sign_extend (m := 64) (0xd00#12)).toNat, 8, _),
      ((bytesVal .ld (EvalChildArm.wordLds8 m sp.toNat) + sign_extend (m := 64) (0xd08#12)).toNat, 8, _),
      ((bytesVal .ld (EvalChildArm.wordLds8 m sp.toNat) + sign_extend (m := 64) (0xd10#12)).toNat, 8, _)] = _
  all_goals
    rw [value, d0, d8, d16]
    rw [storeAddress G 0 (by decide), storeAddress G 8 (by decide), storeAddress G 16 (by decide), Nat.add_zero]
    rfl

/-- Every byte in the argument slot is the corresponding returned byte. -/
theorem copied (m : Mem) (sp : BitVec 64) (index : Nat) :
    ∀ j, j < 24 → (writeLog m (writes m sp index))[slot sp index + j]? =
      some ((m[sp.toNat + 64 + j]?).getD 0) := by
  intro j hj
  exact copy3_total m (sp.toNat + 64) (slot sp index) j hj

/-- The saved bounded index selects the back edge or completed-argument route. -/
theorem branch (index count : Nat) (indexBound : index < count) (countBound : count ≤ 32) :
    guardB bop.BNE (BitVec.ofNat 64 index + 1#64) (BitVec.ofNat 64 count) =
      decide (index + 1 < count) := by
  change guardB bop.BNE (BitVec.ofNat 64 index + BitVec.ofNat 64 1) _ = _
  rw [← BitVec.ofNat_add]
  by_cases more : index + 1 < count
  · have different : BitVec.ofNat 64 (index + 1) ≠ BitVec.ofNat 64 count := by
      intro eq
      have eqNat := congrArg BitVec.toNat eq
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show index + 1 < 2^64 by omega),
        Nat.mod_eq_of_lt (show count < 2^64 by omega)] at eqNat
      omega
    simp [guardB, more, different]
  · have last : count = index + 1 := by omega
    simp [guardB, last]

end Vsa.Sim.CallArgReturn
