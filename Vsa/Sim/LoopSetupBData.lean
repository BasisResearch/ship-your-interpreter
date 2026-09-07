import Vsa.Sim.LoopSetupData

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine

namespace Vsa.Sim

/-- Both setup-B loads and their reflected values, tied to one entry memory. -/
structure LoopSetupBData (c : Config) (stmts count : BitVec 64)
    (countBytes stmtBytes : List (BitVec 8)) : Prop where
  entry : SegEntryData driveLoopSetupBSeg
    (driveLoopSetupBL 0x87fffc50#64 (BitVec.ofNat 64 LayoutInstance.gpEntry))
    [countBytes, stmtBytes] c.σ.mem c
  length : bytesVal .ld countBytes = count
  statements : bytesVal .ld stmtBytes = stmts

/-- Setup-B consumes the two words retained by the actual entry prefix. -/
theorem loopSetupB_data {c : Config} {stmts count : BitVec 64}
    (hcode : Code.Interp_runLoaded c.σ.mem)
    (hsp : c.σ.regs.get? Register.x2 = some (0x87fffc50#64 : BitVec 64))
    (hgp : c.σ.regs.get? Register.x3 = some (BitVec.ofNat 64 LayoutInstance.gpEntry))
    (hcount : read64 c.σ.mem 0x87fffc60 = some count.toNat)
    (hstmts : read64 c.σ.mem 0x87fffc68 = some stmts.toNat) :
    ∃ countBytes stmtBytes, LoopSetupBData c stmts count countBytes stmtBytes := by
  let L := driveLoopSetupBL 0x87fffc50#64 (BitVec.ofNat 64 LayoutInstance.gpEntry)
  let ldCount := mkLine 0x80004438#64 0x01013783#32
  let ldStmts := mkLine 0x8000443c#64 0x01813403#32
  obtain ⟨countBytes, C⟩ := wordLoadFacts_of_read64 c.σ.mem L ldCount count
    rfl (by decide) (by decide) (by decide) hcount
  obtain ⟨stmtBytes, A⟩ := wordLoadFacts_of_read64 c.σ.mem
    (stepGM ldCount L countBytes) ldStmts stmts
    rfl (by change 0x80000000 ≤ (0x87fffc68 : Nat); decide)
    (by change (0x87fffc68 : Nat) + 8 ≤ 0x100000000; decide)
    (by change (0x87fffc68 : Nat) + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ 0x87fffc68; decide)
    hstmts
  refine ⟨countBytes, stmtBytes, ⟨rfl, ⟨hsp, hgp, trivial⟩, by decide, ?_⟩,
    C.value, A.value⟩
  chain_facts hcode with "Vsa.Sim.Code.interp_run_at_"
  all_goals first | exact C.facts | exact A.facts

/-- Initial loop-head registers and all saved arguments at the actual endpoint. -/
structure InitialLoopHeadFacts (inp : BitVec 64) (stmts count : Nat)
    (before after : Config) : Prop extends
    ReadySegFacts inp before before after 0x8000448c#64,
    LoopHeadRegs after 0x87fffc50#64 (BitVec.ofNat 64 stmts)
      (BitVec.ofNat 64 stmts + (BitVec.ofNat 64 count <<< 3)) where
  saved : InterpSpillReads after.σ.mem inp (BitVec.ofNat 64 stmts)
    (BitVec.ofNat 64 count) 0#64
  gp : after.σ.regs.get? Register.x3 = some (BitVec.ofNat 64 LayoutInstance.gpEntry)
  breakFlag : after.σ.regs.get? Register.x19 = some (3#64 : BitVec 64)
  continueFlag : after.σ.regs.get? Register.x20 = some (1#64 : BitVec 64)
  impure : after.σ.regs.get? Register.x22 = some (0x8001b970#64 : BitVec 64)

/-- The live nonempty entry boundary executes both setup rows to the loop head. -/
theorem readyLoopHead_of_ready
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (hcount : 0 < count) : ∃ after, InitialLoopHeadFacts inp stmts count c after := by
  obtain ⟨cA, S⟩ := readyCountSaved_of_ready F false (by simp [Nat.ne_of_gt hcount])
  obtain ⟨cb, ab, D⟩ := loopSetupB_data S.preservation.run_code S.sp S.gp
    S.saved.length S.saved.statements
  obtain ⟨after, B⟩ := hLoopB_ready_of_data inp c 0x87fffc50#64
    (BitVec.ofNat 64 LayoutInstance.gpEntry) [cb, ab] cA.σ.mem cA S.preservation
    S.pc S.good S.tick S.minstret D.entry
  have cursor := gholds_lookup _ B.registers
    (show lookupG 8 _ = some (BitVec.ofNat 64 stmts) from by
      change some (bytesVal .ld ab) = some (BitVec.ofNat 64 stmts)
      rw [D.statements])
  have finish := gholds_lookup _ B.registers
    (show lookupG 18 _ = some (BitVec.ofNat 64 stmts + (BitVec.ofNat 64 count <<< 3)) from by
      change some (bytesVal .ld ab + (bytesVal .ld cb <<< 3)) = _
      rw [D.statements, D.length])
  refine ⟨after, { B.toReadySegFacts with run := S.run.trans B.run },
    ⟨?_, cursor, finish⟩, B.mem.symm ▸ S.saved, ?_, ?_, ?_, ?_⟩
  · exact gholds_lookup _ B.registers (show lookupG 2 _ = some 0x87fffc50#64 from rfl)
  · exact gholds_lookup _ B.registers (show lookupG 3 _ = some _ from rfl)
  · exact gholds_lookup _ B.registers (show lookupG 19 _ = some 3#64 from rfl)
  · exact gholds_lookup _ B.registers (show lookupG 20 _ = some 1#64 from rfl)
  · exact gholds_lookup _ B.registers (show lookupG 22 _ = some 0x8001b970#64 from rfl)

#print axioms loopSetupB_data
#print axioms readyLoopHead_of_ready
end Vsa.Sim
