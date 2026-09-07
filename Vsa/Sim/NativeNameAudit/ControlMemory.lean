import Vsa.Sim.NativeNameAudit.Admission
import Vsa.Sim.NativeNameAudit.Ast
import Vsa.Sim.RuntimeOwnershipInitial

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Machine

namespace Vsa.Sim.NativeNameAudit
namespace Control

open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance

def repair : List WEntry := [(0x81000048, 8, 0x81000210#64)]
def log : List WEntry := nativeNameLog ++ repair
def mem : Mem := writeLog snapshotMem log
def config : Config := physicalConfig mem

theorem lookup (a : Nat) : mem[a]? = logRead snapshotInitialRead log a :=
  snapshot_logRead log a

local macro "control_read" : tactic =>
  `(tactic| (simp only [read32, read64, readLE, lookup]; decide))

theorem unchanged {k : Nat} (hk : k < 0x81000048 ∨ 0x81000050 ≤ k) :
    mem[k]? = nativeNameMem[k]? := by
  change (writeLog snapshotMem (nativeNameLog ++ repair))[k]? = _
  rw [writeLog_append]
  apply writeLog_out
  simp only [repair, OutL, Nat.reduceAdd]
  exact ⟨hk, True.intro⟩

theorem ast_agree : AgreeP AstPage nativeNameMem mem := by
  intro k hk
  exact (unchanged (Or.inr (by unfold AstPage at hk; omega))).symm

theorem astReads : AstReads mem where
  array0 := by control_read
  array1 := by control_read
  stmtTag := by control_read
  stmtExpr := by control_read
  callTag := by control_read
  callCallee := by control_read
  callArgs := by control_read
  callArgc := by control_read
  varTag := by control_read
  varName := by control_read
  astName := cstring_agreeP ast_agree NativeNameAudit.astName (by
    intro k hk; change k ≤ 7 at hk; unfold AstPage; omega)

theorem programWithin : ProgramReprWithin mem AstPage 0x82000000 2 nativeNameProgram :=
  astReads.programWithin

theorem program_owned (p : Program) (hp : ProgramRepr mem 0x82000000 2 p) :
    ProgramReprWithin mem AstPage 0x82000000 2 p := by
  rw [astReads.program_unique hp]
  exact programWithin

theorem reads : StoreReadFacts mem where
  count := by control_read
  capacity := by control_read
  names := by control_read
  values := by control_read
  parent := by control_read
  names0 := by control_read
  names1 := by control_read
  names2 := by control_read
  tag0 := by control_read
  name0 := by control_read
  function0 := by control_read
  tag1 := by control_read
  name1 := by control_read
  function1 := by control_read
  tag2 := by control_read
  name2 := by control_read
  function2 := by control_read

theorem view : StoreView mem where
  toStoreReadFacts := reads
  printName := cstring_agreeP astStringAgree nativeName_printCString (by
    intro k hk; right; omega)
  printlnName := cstring_agreeP astStringAgree nativeName_valueNameCString (by
    intro k hk; right; omega)
  assertName := cstring_agreeP astStringAgree nativeName_assertCString (by
    intro k hk; right; omega)
where
  astStringAgree : AgreeP (fun k => k < 0x81000048 ∨ 0x81000050 ≤ k) nativeNameMem mem :=
    fun _ hk => (unchanged hk).symm

theorem valueBytes : ∀ k, 0x81000080 ≤ k → k < 0x81000140 →
    ∃ b : BitVec 8, mem[k]? = some b := by
  intro k hlo hhi
  rw [unchanged (Or.inr (by omega))]
  have hout : OutL nativeNameLog k := by
    simp only [nativeNameLog, OutL, Nat.reduceAdd, and_true]
    omega
  rw [show nativeNameMem[k]? = snapshotMem[k]? from writeLog_out _ _ _ hout]
  exact ⟨snapshotByte k, ramMemory_get snapshotByte k (by omega) (by omega)⟩

theorem arraysReady : RuntimeOwnership.StoreArraysReady mem phif initSt.store where
  namesAligned := by
    intro fa hf pn hp
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    have e := Option.some.inj (hp.symm.trans reads.names)
    subst pn
    decide
  valuesAligned := by
    intro fa hf pv hp
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    have e := Option.some.inj (hp.symm.trans reads.values)
    subst pv
    decide
  valueWords := by
    intro fa hf pv hp i hi
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    have e := Option.some.inj (hp.symm.trans reads.values)
    subst pv
    change i < 3 at hi
    exact valueWordsTotal_of_interval valueBytes (by omega) (by omega)

#print axioms unchanged
#print axioms programWithin
#print axioms view
#print axioms valueBytes
#print axioms arraysReady

end Control
end Vsa.Sim.NativeNameAudit
