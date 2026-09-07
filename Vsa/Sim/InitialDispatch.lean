import Vsa.Sim.InitialAstReads
import Vsa.Sim.rows.LoopHeadDispatchSeg
import Vsa.Sim.SegToTripleFramed

namespace Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

/-- Both actual dispatch words and their reflected statement pointer. -/
structure InitialDispatchData (c : Config) (stmts aStmt : Nat)
    (flagBytes stmtBytes : List (BitVec 8)) : Prop where
  entry : SegEntryData loopHeadDispatchSeg
    (loopHeadDispatchL 0x87fffc50#64 (BitVec.ofNat 64 stmts))
    [flagBytes, stmtBytes] c.σ.mem c
  script : bytesVal .ld flagBytes = 0#64
  statement : bytesVal .ld stmtBytes = BitVec.ofNat 64 aStmt

/-- Owned initial dispatch reads both words from the reached memory. -/
theorem OwnedLoopHeadFacts.dispatchData
    {inp : BitVec 64} {stmts count : Nat} {before after : Config}
    {s : Stmt} {ss : List Stmt} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {D : RuntimeOwnership.InitialOwnershipData}
    (H : OwnedLoopHeadFacts inp stmts count before after (s :: ss) N A phiF phiC D)
    {aStmt : Nat}
    (R : StmtReadAccess after.σ.mem LayoutInstance.stackSL D.shared stmts aStmt s) :
    ∃ flagBytes stmtBytes, InitialDispatchData after stmts aStmt flagBytes stmtBytes := by
  let L := loopHeadDispatchL 0x87fffc50#64 (BitVec.ofNat 64 stmts)
  let ldFlag := mkLine 0x8000448c#64 0x00813783#32
  let ldStmt := mkLine 0x80004490#64 0x00043483#32
  have hs : (BitVec.ofNat 64 stmts).toNat = stmts :=
    Nat.mod_eq_of_lt (by have := R.slotGeometry.ram_hi; change stmts + 8 ≤ 0x100000000 at this; omega)
  have ht := R.fields (.word32 0) (by simp [stmtReadFields])
  have hp : (BitVec.ofNat 64 aStmt).toNat = aStmt :=
    Nat.mod_eq_of_lt (by have := ht.ram_hi; change aStmt + 0 + 4 ≤ 0x100000000 at this; omega)
  obtain ⟨flagBytes, W⟩ := wordLoadFacts_of_read64 after.σ.mem L ldFlag 0#64
    rfl (by change 0x80000000 ≤ (0x87fffc58 : Nat); decide)
    (by change (0x87fffc58 : Nat) + 8 ≤ 0x100000000; decide)
    (by change (0x87fffc58 : Nat) + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ 0x87fffc58; decide)
    H.saved.script
  have hea : (eaddrM ldStmt (stepGM ldFlag L flagBytes)).toNat = stmts := by
    change (BitVec.ofNat 64 stmts + 0#64).toNat = stmts
    simpa using hs
  obtain ⟨stmtBytes, S⟩ := wordLoadFacts_of_read64 after.σ.mem
    (stepGM ldFlag L flagBytes) ldStmt (BitVec.ofNat 64 aStmt) rfl
    (by rw [hea]; exact R.slotGeometry.ram_lo)
    (by rw [hea]; exact R.slotGeometry.ram_hi)
    (by rw [hea]; have := R.slotGeometry.htif; omega)
    (by rw [hea, hp]; exact R.pointer.read)
  have hterm : TermFactsT
      (runGM [ldFlag, ldStmt] L [flagBytes, stmtBytes])
      ⟨0x80004494#64, 0xfc0782e3#32, 0xe3#8, 0x82#8, 0x07#8, 0xfc#8,
        .br bop.BEQ true, 15, 0, 0x1fc4#13, 0#21, 0#12⟩ := by
    change guardB bop.BEQ (bytesVal .ld flagBytes) 0#64 = true
    rw [W.value]
    rfl
  refine ⟨flagBytes, stmtBytes, ⟨rfl, ⟨H.sp_reg, H.cursor_reg, trivial⟩, by change KeysOK [2, 8]; decide, ?_⟩,
    W.value, S.value⟩
  have hcode := H.preservation.run_code
  chain_facts hcode with "Vsa.Sim.Code.interp_run_at_"
  all_goals first | exact W.facts | exact S.facts | exact hterm

#print axioms OwnedLoopHeadFacts.dispatchData

/-- Read-only execution transports the prefix facts through actual equalities. -/
theorem ReadyLandingFacts.readOnly
    {inp : BitVec 64} {initial before after : Config}
    (P : ReadyLandingFacts inp initial before)
    (hm : after.σ.mem = before.σ.mem)
    (ho : after.σ.sailOutput = before.σ.sailOutput)
    (hl : after.σ.regs.get? Register.x21 = before.σ.regs.get? Register.x21)
    (ht : after.σ.regs.get? Register.htif_payload_writes =
      before.σ.regs.get? Register.htif_payload_writes) :
    ReadyLandingFacts inp initial after := by
  exact
    { mem_extends := hm.symm ▸ P.mem_extends
      outside_prefix := fun k hk => (P.outside_prefix k hk).trans
        (congrArg (fun m : Mem => m[k]?) hm.symm)
      output := by unfold output; rw [ho]; exact P.output
      run_code := hm.symm ▸ P.run_code
      return_latch := hl.trans P.return_latch
      htif_payload := ht.trans P.htif_payload }

/-- Runtime representations depend on the reached memory alone. -/
theorem ReadyRuntimeFacts.mem_eq
    {before after : Config} {stmts count : Nat} {p : Program}
    {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
    {D : RuntimeOwnership.InitialOwnershipData}
    (F : ReadyRuntimeFacts before stmts count p N A phiF phiC D)
    (hm : after.σ.mem = before.σ.mem) :
    ReadyRuntimeFacts after stmts count p N A phiF phiC D := by
  exact ⟨hm.symm ▸ F.heap, hm.symm ▸ F.arrays, hm.symm ▸ F.program, hm.symm ▸ F.store⟩

/-- Loop registers retained while dispatch selects the first statement. -/
def initialLoopKeep (stmts count : Nat) : GRegs :=
  [(2, 0x87fffc50#64), (3, BitVec.ofNat 64 LayoutInstance.gpEntry),
   (8, BitVec.ofNat 64 stmts),
   (18, BitVec.ofNat 64 stmts + (BitVec.ofNat 64 count <<< 3)),
   (19, 3#64), (20, 1#64), (22, 0x8001b970#64)]

/-- The actual loop head supplies the entire retained register list. -/
theorem OwnedLoopHeadFacts.keep
    {inp : BitVec 64} {stmts count : Nat} {before head : Config}
    {p : Program} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {D : RuntimeOwnership.InitialOwnershipData}
    (H : OwnedLoopHeadFacts inp stmts count before head p N A phiF phiC D) :
    GHolds head.σ (initialLoopKeep stmts count) :=
  ⟨H.sp_reg, H.gp, H.cursor_reg, H.finish_reg, H.breakFlag, H.continueFlag, H.impure, trivial⟩

/-- The actual dispatch endpoint retains the selected statement and all initial ownership. -/
structure OwnedInitialDispatchFacts (inp : BitVec 64) (stmts count aStmt : Nat)
    (before after : Config) (s : Stmt) (ss : List Stmt)
    (N : NativeAddrs) (A : Arena) (phiF phiC : Addr → Nat)
    (D : RuntimeOwnership.InitialOwnershipData) : Prop extends
    ReadySegFacts inp before before after 0x80004458#64,
    ReadyRuntimeFacts after stmts count (s :: ss) N A phiF phiC D where
  sp : after.σ.regs.get? Register.x2 = some (0x87fffc50#64 : BitVec 64)
  statement : after.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 aStmt)
  access : StmtReadAccess after.σ.mem LayoutInstance.stackSL D.shared stmts aStmt s
  saved : InterpSpillReads after.σ.mem inp (BitVec.ofNat 64 stmts)
    (BitVec.ofNat 64 count) 0#64
  callABI : ExecSeqCallABI .interpRun after.σ.mem after.σ.regs.get? phiF 0
    0x87fffc50#64 0x87fffca8#64
  cursor : ExecSeqCursorRepr .interpRun after.σ.mem phiF 0 (s :: ss)
    0x87fffc50#64 0x87fffca8#64 after.σ.regs.get?
  keep : GHolds after.σ (initialLoopKeep stmts count)
  initial : RuntimeOwnership.InitialOwned before.σ.mem A LayoutInstance.stackSL
    phiF phiC stmts count D

/-- The first dispatch executes from owned array access, without extra read premises. -/
theorem OwnedLoopHeadFacts.dispatch
    {inp : BitVec 64} {stmts count : Nat} {before head : Config}
    {s : Stmt} {ss : List Stmt} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {D : RuntimeOwnership.InitialOwnershipData}
    (H : OwnedLoopHeadFacts inp stmts count before head (s :: ss) N A phiF phiC D) :
    ∃ after aStmt, OwnedInitialDispatchFacts inp stmts count aStmt before after s ss
      N A phiF phiC D := by
  obtain ⟨aStmt, R⟩ := H.firstRead
  obtain ⟨flagBytes, stmtBytes, F⟩ := H.dispatchData R
  obtain ⟨vm, hvm⟩ := H.minstret
  obtain ⟨σ', i', hsteps, hi', hG', hmem', hout', hpc', hmi', hregs, hframe⟩ :=
    segEval_sound loopHeadDispatchSeg head.σ head.tick head.steps 0x8000448c#64 vm
      (loopHeadDispatchL 0x87fffc50#64 (BitVec.ofNat 64 stmts)) [flagBytes, stmtBytes]
      H.good H.pc hvm F.entry.hL F.entry.keys F.entry.facts
      (by change ChainOK 0x8000448c#64 [2, 8] loopHeadDispatchSeg; decide) H.tick
  let after : Config := ⟨σ', i', head.steps + evalBlocksFuel loopHeadDispatchSeg⟩
  have hm : after.σ.mem = head.σ.mem := hmem'.trans (by rfl)
  have P : ReadyLandingFacts inp before after := H.preservation.readOnly hm hout'
    (hframe Register.x21 (by decide) (by decide))
    (hframe Register.htif_payload_writes (by decide) (by decide))
  have hkeep : GHolds after.σ (initialLoopKeep stmts count) :=
    gholds_keep_of_frame (initialLoopKeep stmts count)
      (by have hf : FrameOK [2, 3, 8, 18, 19, 20, 22] loopHeadDispatchSeg := by decide
          exact hf.1) hframe H.keep
  have hsp : after.σ.regs.get? Register.x2 = some (0x87fffc50#64 : BitVec 64) :=
    gholds_lookup _ hkeep
    (show lookupG 2 (initialLoopKeep stmts count) = some 0x87fffc50#64 from rfl)
  have hcursor : after.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 stmts) :=
    gholds_lookup _ hkeep
    (show lookupG 8 (initialLoopKeep stmts count) = some (BitVec.ofNat 64 stmts) from rfl)
  have hfinish : after.σ.regs.get? Register.x18 =
      some (BitVec.ofNat 64 stmts + (BitVec.ofNat 64 count <<< 3)) :=
    gholds_lookup _ hkeep
    (show lookupG 18 (initialLoopKeep stmts count) =
      some (BitVec.ofNat 64 stmts + (BitVec.ofNat 64 count <<< 3)) from rfl)
  refine ⟨after, aStmt, ⟨H.run.trans hsteps, hpc', hG', hi', hmi', P⟩,
    H.toReadyRuntimeFacts.mem_eq hm, hsp, ?_, hm.symm ▸ R,
    hm.symm ▸ H.saved, ?_, ?_, hkeep, H.initial⟩
  · exact gholds_lookup _ hregs (show lookupG 9 _ = some (BitVec.ofNat 64 aStmt) from by
      change some (bytesVal .ld stmtBytes) = some (BitVec.ofNat 64 aStmt)
      rw [F.statement])
  · simpa only [ExecSeqCallABI, hm] using H.callABI
  · simpa only [ExecSeqCursorRepr, hm, hsp.trans H.sp_reg.symm,
      hcursor.trans H.cursor_reg.symm, hfinish.trans H.finish_reg.symm] using H.cursor

/-- Every live represented nonempty program executes its first dispatch. -/
theorem readyInitialDispatch_owned
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {s : Stmt} {ss : List Stmt} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A phiF phiC aLeft)
    (hp : ProgramRepr c.σ.mem stmts count (s :: ss)) :
    ∃ after aStmt D, OwnedInitialDispatchFacts inp stmts count aStmt c after s ss
      N A phiF phiC D := by
  obtain ⟨head, D, H⟩ := readyLoopHead_owned F hp (by simp)
  obtain ⟨after, aStmt, R⟩ := H.dispatch
  exact ⟨after, aStmt, D, R⟩

#print axioms OwnedLoopHeadFacts.keep
#print axioms ReadyLandingFacts.readOnly
#print axioms ReadyRuntimeFacts.mem_eq
#print axioms OwnedLoopHeadFacts.dispatch
#print axioms readyInitialDispatch_owned
end Vsa.Sim
