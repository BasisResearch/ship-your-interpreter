import Vsa.Sim.InitialNullOwned
import Vsa.Sim.rows.LoopHeadArgSetupSeg
import Vsa.Sim.EnvGetSpec3

namespace Vsa.Sim
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.Machine Vsa.While Vsa.Alloc

/-- Both argument-setup reads are taken from the reached null-return memory. -/
structure InitialExecArgsData (c : Config) (inp : BitVec 64) (aStmt env : Nat)
    (inputBytes envBytes : List (BitVec 8)) : Prop where
  entry : SegEntryData loopHeadArgSetupSeg
    (loopHeadArgSetupL 0x87fffc50#64 (BitVec.ofNat 64 aStmt))
    [inputBytes, envBytes] c.σ.mem c
  input : bytesVal .ld inputBytes = inp
  environment : bytesVal .ld envBytes = BitVec.ofNat 64 env

/-- Existing initial facts supply both actual reads and their exact loaded values. -/
theorem OwnedInitialNullFacts.argsData
    {inp : BitVec 64} {stmts count aStmt : Nat} {before dispatch after : Config}
    {s : Stmt} {ss : List Stmt} {N : NativeAddrs} {A : Arena}
    {phiF phiC : Addr → Nat} {D : RuntimeOwnership.InitialOwnershipData} {aLeft : Nat}
    (H : OwnedInitialNullFacts inp stmts count aStmt before dispatch after s ss N A phiF phiC D)
    (F : LayoutInstance.InterpRunReadyFacts before stmts count inp N A phiF phiC aLeft) :
    ∃ inputBytes envBytes, InitialExecArgsData after inp aStmt (phiF 0) inputBytes envBytes := by
  let L := loopHeadArgSetupL 0x87fffc50#64 (BitVec.ofNat 64 aStmt)
  let ldInput := mkLine 0x80004460#64 0x00013783#32
  let setRet := mkLine 0x80004464#64 0x05810693#32
  let setStmt := mkLine 0x80004468#64 0x00048593#32
  let ldEnv := mkLine 0x8000446c#64 0x0007b603#32
  obtain ⟨inputBytes, I⟩ := wordLoadFacts_of_read64 after.σ.mem L ldInput inp
    rfl (by change 0x80000000 ≤ (0x87fffc50 : Nat); decide)
    (by change (0x87fffc50 : Nat) + 8 ≤ 0x100000000; decide)
    (by change (0x87fffc50 : Nat) + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ 0x87fffc50; decide)
    H.saved.input
  let Lenv := runGM [ldInput, setRet, setStmt] L [inputBytes]
  have he : (eaddrM ldEnv Lenv).toNat = inp.toNat := by
    change (bytesVal .ld inputBytes + 0#64).toNat = inp.toNat
    rw [I.value, BitVec.add_zero]
  have hg := H.preservation.toReadyPrefixFacts.globals F
  have hv : (BitVec.ofNat 64 (phiF 0)).toNat = phiF 0 :=
    Nat.mod_eq_of_lt (read64_lt_eg4 _ _ _ hg)
  have hi : inp.toNat = 0x87fffe10 := by rw [F.interp_local]; rfl
  obtain ⟨envBytes, E⟩ := wordLoadFacts_of_read64 after.σ.mem Lenv ldEnv
    (BitVec.ofNat 64 (phiF 0)) rfl
    (by rw [he, hi]; decide) (by rw [he, hi]; decide) (by rw [he, hi]; decide)
    (by rw [he, hv]; exact hg)
  refine ⟨inputBytes, envBytes, ⟨rfl, ⟨H.sp, H.statement, trivial⟩,
    by change KeysOK [2, 9]; decide, ?_⟩, I.value, E.value⟩
  have hcode := H.preservation.run_code
  chain_facts hcode with "Vsa.Sim.Code.interp_run_at_"
  all_goals first | exact I.facts | exact E.facts

#print axioms OwnedInitialNullFacts.argsData
end Vsa.Sim
