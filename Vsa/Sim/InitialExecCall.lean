import Vsa.Sim.InitialExecArgsData
import Vsa.Sim.InitialExecSites
import Vsa.Sim.BridgeSegFull

namespace Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

/-- Exact incoming registers of the first statement call. -/
def initialExecArgs (inp : BitVec 64) (aStmt env : Nat) : GRegs :=
  [(2, 0x87fffc50#64), (9, BitVec.ofNat 64 aStmt), (10, inp),
   (11, BitVec.ofNat 64 aStmt), (12, BitVec.ofNat 64 env),
   (13, 0x87fffca8#64), (1, 0x80004478#64)]

/-- The first statement callee is reached with actual arguments and retained ownership. -/
structure OwnedInitialExecFacts (inp : BitVec 64) (stmts count aStmt : Nat)
    (before dispatch initialized after : Config) (s : Stmt) (ss : List Stmt)
    (N : NativeAddrs) (A : Arena) (phiF phiC : Addr → Nat)
    (D : RuntimeOwnership.InitialOwnershipData) : Prop extends
    ReadySegFacts inp before before after 0x80003fe0#64,
    ReadyRuntimeFacts after stmts count (s :: ss) N A phiF phiC D where
  nullReturn : OwnedInitialNullFacts inp stmts count aStmt before dispatch initialized
    s ss N A phiF phiC D
  mem : after.σ.mem = initialized.σ.mem
  arguments : GHolds after.σ (initialExecArgs inp aStmt (phiF 0))
  frame : ∀ R, (∀ r ∈ noiseRegs, (r == R) = false) →
    (∀ n ∈ wrChain loopHeadArgSetupSeg, (gprReg n == R) = false) →
    (Register.x1 == R) = false → after.σ.regs.get? R = initialized.σ.regs.get? R

/-- Execute argument setup and its JAL using the two reached memory reads. -/
theorem OwnedInitialNullFacts.execCall
    {inp : BitVec 64} {stmts count aStmt : Nat} {before dispatch initialized : Config}
    {s : Stmt} {ss : List Stmt} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {D : RuntimeOwnership.InitialOwnershipData} {aLeft : Nat}
    (H : OwnedInitialNullFacts inp stmts count aStmt before dispatch initialized s ss N A phiF phiC D)
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft) :
    ∃ after, OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D := by
  obtain ⟨inputBytes, envBytes, Adata⟩ := H.argsData F
  obtain ⟨after, C⟩ := bridgeOfSegFull loopHeadArgSetupSeg
    (loopHeadArgSetupL 0x87fffc50#64 (BitVec.ofNat 64 aStmt)) [inputBytes, envBytes]
    0x80004460#64 0x80003fe0#64 0x80004478#64 initialized H.good H.pc H.minstret H.tick
    Adata.entry.hL Adata.entry.keys Adata.entry.facts
    (by change ChainOK 0x80004460#64 [2, 9] loopHeadArgSetupSeg; decide)
    (by change KeysOK [10, 12, 11, 13, 15, 2, 9]; decide)
    (by change ∀ n ∈ ([10, 12, 11, 13, 15, 2, 9] : List Nat), n ≠ 1; decide)
    (by
      intro middle hg ht hp hmi hm _
      have hm' : middle.σ.mem = initialized.σ.mem := hm.trans (by rfl)
      obtain ⟨vm, hvm⟩ := hmi
      obtain ⟨s2, i2, hs2, hi2, hg2, hm2, ho2⟩ :=
        site_80004474_initialExec middle.σ middle.tick middle.steps 0x80004474#64 vm
          hg hp hvm (hm'.symm ▸ H.preservation.run_code) rfl ht
      exact ⟨⟨s2, i2, middle.steps + 1⟩, jalCallFacts_of_obs hs2 hi2 hg2 hm2 ho2 (by decide)⟩)
  have hm : after.σ.mem = initialized.σ.mem := C.mem.trans (by rfl)
  have P := H.preservation.readOnly hm C.output
    (C.frame Register.x21 (by decide) (by decide) (by decide))
    (C.frame Register.htif_payload_writes (by decide) (by decide) (by decide))
  refine ⟨after, ⟨H.run.trans C.run, C.pc, C.good, C.tick, C.minstret, P⟩,
    H.toReadyRuntimeFacts.mem_eq hm, H, hm, ?_, C.frame⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, C.ra, trivial⟩
  · exact gholds_lookup _ C.registers (show lookupG 2 _ = some 0x87fffc50#64 from rfl)
  · exact gholds_lookup _ C.registers (show lookupG 9 _ = some (BitVec.ofNat 64 aStmt) from rfl)
  · exact gholds_lookup _ C.registers (show lookupG 10 _ = some inp from by
      change some (bytesVal .ld inputBytes + 0#64) = some inp
      rw [Adata.input, BitVec.add_zero])
  · exact gholds_lookup _ C.registers (show lookupG 11 _ = some (BitVec.ofNat 64 aStmt) from by
      change some (BitVec.ofNat 64 aStmt + 0#64) = some (BitVec.ofNat 64 aStmt)
      rw [BitVec.add_zero])
  · exact gholds_lookup _ C.registers (show lookupG 12 _ = some (BitVec.ofNat 64 (phiF 0)) from by
      change some (bytesVal .ld envBytes) = some (BitVec.ofNat 64 (phiF 0))
      rw [Adata.environment])
  · exact gholds_lookup _ C.registers (show lookupG 13 _ = some 0x87fffca8#64 from rfl)

/-- Every represented nonempty initial program reaches its first statement call. -/
theorem readyInitialExec_owned
    {c : Config} {stmts count : Nat} {inp : BitVec 64}
    {s : Stmt} {ss : List Stmt} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts c stmts count inp N A phiF phiC aLeft)
    (hp : ProgramRepr c.σ.mem stmts count (s :: ss)) :
    ∃ dispatch initialized after aStmt D,
      OwnedInitialExecFacts inp stmts count aStmt c dispatch initialized after s ss N A phiF phiC D := by
  obtain ⟨dispatch, initialized, aStmt, D, H⟩ := readyInitialNull_owned F hp
  obtain ⟨after, C⟩ := H.execCall F
  exact ⟨dispatch, initialized, after, aStmt, D, C⟩

#print axioms OwnedInitialNullFacts.execCall
#print axioms readyInitialExec_owned
end Vsa.Sim

namespace Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

variable {inp : BitVec 64} {stmts count aStmt : Nat}
  {before dispatch initialized after : Config} {s : Stmt} {ss : List Stmt}
  {N : NativeAddrs} {A : Arena} {phiF phiC : Addr → Nat}
  {D : RuntimeOwnership.InitialOwnershipData}

/-- The statement callee receives the same four interpreter spill words. -/
theorem OwnedInitialExecFacts.saved
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) :
    InterpSpillReads after.σ.mem inp (BitVec.ofNat 64 stmts) (BitVec.ofNat 64 count) 0#64 :=
  H.mem.symm ▸ H.nullReturn.saved

/-- Exact owned AST access survives the read-only argument setup and call. -/
theorem OwnedInitialExecFacts.access
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) :
    StmtReadAccess after.σ.mem LayoutInstance.stackSL D.shared stmts aStmt s :=
  H.mem.symm ▸ H.nullReturn.access

/-- The actual incoming statement pointer has the exact dispatch-load geometry. -/
theorem OwnedInitialExecFacts.tag
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) :
    AstReadGeometry LayoutInstance.stackSL (BitVec.ofNat 64 aStmt).toNat 4 := by
  have h := H.access.tag
  have ha : (BitVec.ofNat 64 aStmt).toNat = aStmt :=
    Nat.mod_eq_of_lt (by have := h.ram_hi; change aStmt + 4 ≤ 0x100000000 at this; omega)
  rw [ha]
  exact h

/-- The incoming statement pointer represents the selected source statement. -/
theorem OwnedInitialExecFacts.stmt
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) :
    StmtRepr after.σ.mem (BitVec.ofNat 64 aStmt).toNat s := by
  have hr := H.access.fields (.word32 0) (by simp [stmtReadFields])
  have ha : (BitVec.ofNat 64 aStmt).toNat = aStmt :=
    Nat.mod_eq_of_lt (by have := hr.ram_hi; change aStmt + 0 + 4 ≤ 0x100000000 at this; omega)
  rw [ha]
  exact H.access.pointer.target.erase

/-- The initialized result slot still contains null at statement entry. -/
theorem OwnedInitialExecFacts.value
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) :
    ValueRepr after.σ.mem N phiC 0x87fffca8 .null :=
  H.mem.symm ▸ H.nullReturn.call.value

/-- Reached output agrees with the initial source state. -/
theorem OwnedInitialExecFacts.out
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) {aLeft : Nat}
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft) :
    OutRepr after.σ initSt := by
  unfold OutRepr
  rw [H.preservation.output]
  exact F.out

/-- The initial ledger proves store survival under arbitrary writes to the full stack. -/
theorem OwnedInitialExecFacts.store_survives_stack
    (H : OwnedInitialExecFacts inp stmts count aStmt before dispatch initialized after
      s ss N A phiF phiC D) (m' : Mem)
    (hag : ∀ k, ¬ (LayoutInstance.stackSL.lo ≤ k ∧ k < LayoutInstance.stackSL.hi) →
      after.σ.mem[k]? = m'[k]?) :
    StoreRepr m' N A phiF phiC initSt.store := by
  have O := H.nullReturn.entered.initial
  apply H.heap.store.repr_transport H.store hag
  · intro role p n hp k hk
    exact fun hs => O.extent_outsideWrites (O.heap.ledger.live role p n hp) hk (Or.inr hs)
  · intro k hk hs
    exact H.heap.immutable.outsideWrites k hk (Or.inr hs)

#print axioms OwnedInitialExecFacts.saved
#print axioms OwnedInitialExecFacts.access
#print axioms OwnedInitialExecFacts.tag
#print axioms OwnedInitialExecFacts.stmt
#print axioms OwnedInitialExecFacts.value
#print axioms OwnedInitialExecFacts.out
#print axioms OwnedInitialExecFacts.store_survives_stack
end Vsa.Sim
