import Vsa.Sim.DriveToLoopHeadSpans
import Vsa.Sim.WordLoadData

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine

namespace Vsa.Sim

/-- Both count-test rows use the same saved count load and signed comparison. -/
theorem loopSetup_count_data {c : Config} {count : Nat} (taken : Bool)
    (hcode : Code.Interp_runLoaded c.σ.mem)
    (hsp : c.σ.regs.get? Register.x2 = some (0x87fffc50#64 : BitVec 64))
    (ha0 : c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64))
    (hcount : read64 c.σ.mem 0x87fffc60 = some count)
    (hbound : count < 2^31) (hbranch : decide (count = 0) = taken) :
    ∃ lds, SegEntryData (if taken then driveLoopEmptySeg else driveLoopSetupASeg)
      (driveLoopSetupAL 0x87fffc50#64 0#64) lds c.σ.mem c := by
  let v := BitVec.ofNat 64 count
  have hv : v.toNat = count := Nat.mod_eq_of_lt (by omega)
  have hread : read64 c.σ.mem 0x87fffc60 = some v.toNat := by rw [hv]; exact hcount
  obtain ⟨bs, W⟩ := wordLoadFacts_of_read64 c.σ.mem
    (driveLoopSetupAL 0x87fffc50#64 0#64) (mkLine 0x8000442c#64 0x01013783#32) v
    rfl (by decide) (by decide) (by decide) hread
  have hb := W.value
  have hload := W.facts
  have hg : guardB bop.BGE 0#64 v = taken := by
    have hi : v.toInt = (count : Int) := by
      rw [BitVec.toInt_eq_toNat_of_lt (by rw [hv]; omega), hv]
    simp only [guardB, zopz0zKzJ_s, hi]
    simpa using hbranch
  have hterm : TermFactsT
      (runGM [(mkLine 0x8000442c#64 0x01013783#32),
        (mkLine 0x80004430#64 0x00050a93#32)]
        (driveLoopSetupAL 0x87fffc50#64 0#64) [bs])
      ⟨0x80004434#64, 0x0ef05063#32, 0x63#8, 0x50#8, 0xf0#8, 0x0e#8,
        .br bop.BGE taken, 0, 15, 0x00e0#13, 0#21, 0#12⟩ := by
    change guardB bop.BGE 0#64 (bytesVal .ld bs) = taken
    rw [hb]
    exact hg
  refine ⟨[bs], rfl, ⟨hsp, ha0, trivial⟩, by decide, ?_⟩
  cases taken <;> chain_facts hcode with "Vsa.Sim.Code.interp_run_at_"
  all_goals first | exact hload | exact hterm

#print axioms loopSetup_count_data
/-- The count-test endpoint retains the exact data needed by setup-B. -/
structure ReadyCountSavedFacts (inp : BitVec 64) (stmts count : Nat)
    (before after : Config) (taken : Bool) : Prop extends
    ReadySegFacts inp before before after
      (if taken then 0x80004514#64 else 0x80004438#64) where
  saved : InterpSpillReads after.σ.mem inp (BitVec.ofNat 64 stmts)
    (BitVec.ofNat 64 count) 0#64
  sp : after.σ.regs.get? Register.x2 = some (0x87fffc50#64 : BitVec 64)
  gp : after.σ.regs.get? Register.x3 = some (BitVec.ofNat 64 LayoutInstance.gpEntry)

/-- The existing RAM bound fixes signed count-test polarity at the actual endpoint. -/
theorem readyCountSaved_of_ready
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (taken : Bool) (hbranch : decide (count = 0) = taken) :
    ∃ after, ReadyCountSavedFacts inp stmts count c after taken := by
  have hbound : count < 2^31 := by have := F.stmts_ram; omega
  obtain ⟨c2, J⟩ := readySetjmpSaved_of_ready F
  have hcount : read64 c2.σ.mem 0x87fffc60 = some count := by
    have hv : (BitVec.ofNat 64 count).toNat = count := Nat.mod_eq_of_lt (by omega)
    simpa only [hv] using J.saved.length
  obtain ⟨lds, D⟩ := loopSetup_count_data taken J.preservation.run_code J.sp J.result
    hcount hbound hbranch
  obtain ⟨after, S⟩ := hLoopCount_ready_of_data inp c taken 0x87fffc50#64 lds c2.σ.mem c2
    J.preservation J.pc J.good J.tick J.minstret D
  exact ⟨after, { S.toReadySegFacts with run := J.run.trans S.run },
    S.mem.symm ▸ J.saved, S.sp, S.gp.trans J.gp⟩

/-- Compatibility view of the actual count-test endpoint. -/
theorem readyCountTest_closed
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (taken : Bool) (hbranch : decide (count = 0) = taken) :
    ReadySegLanded inp c c (if taken then 0x80004514#64 else 0x80004438#64) := by
  obtain ⟨after, S⟩ := readyCountSaved_of_ready F taken hbranch
  exact ⟨after, S.run, S.pc, S.good, S.tick, S.minstret, S.preservation⟩

#print axioms readyCountSaved_of_ready

/-- Actual nonempty entry prefix; all setup data comes from its own saved words. -/
theorem readySetupA_closed
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (hcount : 0 < count) : ReadySegLanded inp c c 0x80004438#64 :=
  readyCountTest_closed F false (by simp [Nat.ne_of_gt hcount])

/-- Actual empty entry prefix through the taken count branch. -/
theorem readyEmpty_closed
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {N : NativeAddrs} {A : Arena} {φf φc : Vsa.While.Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A φf φc aLeft)
    (hcount : count = 0) : ReadySegLanded inp c c 0x80004514#64 :=
  readyCountTest_closed F true (by simp [hcount])

/-- The complete empty-program entry span from the live loaded boundary. -/
theorem entryEmptySpan_of_loaded : EntryEmptySpan LayoutInstance.interpRunLayout := by
  apply entryEmptySpan_of_ready_route
  intro c stmts count inp N A φf φc aLeft hp F
  exact readyEmpty_closed F hp.2

#print axioms readyCountTest_closed
#print axioms readySetupA_closed
#print axioms readyEmpty_closed
#print axioms entryEmptySpan_of_loaded
end Vsa.Sim
