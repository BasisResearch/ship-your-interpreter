import Vsa.Sim.AllocatorBoundary.Store
import Vsa.Sim.NativeNameAudit.ControlLoaded
import Vsa.Sim.RuntimeOwnershipTransport

namespace Vsa.Sim.AllocatorBoundary
open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Alloc Vsa.Machine RuntimeOwnership
open Vsa.Sim.OutputAliasLoaded Vsa.Sim.LayoutInstance Vsa.Sim.NativeNameAudit

/-- Two empty blocks require environment allocation in the binary. -/
def program : Program := [.block [], .block []]
def blockLog : List WEntry :=
  [(0x82000008, 8, 0x82000020#64), (0x82000020, 4, 2#64),
   (0x82000028, 8, 0#64), (0x82000030, 4, 0#64)]
def log : List WEntry := Control.log ++ blockLog
def mem : Mem := writeLog Control.mem blockLog
def config : Config := physicalConfig mem

theorem mem_eq : mem = writeLog snapshotMem log := by
  exact (writeLog_append snapshotMem Control.log blockLog).symm

theorem lookup (k : Nat) : mem[k]? = logRead snapshotInitialRead log k := by
  rw [mem_eq]
  exact snapshot_logRead log k

theorem unchanged {k : Nat} (hk : k < 0x82000000 ∨ 0x82000100 ≤ k) :
    mem[k]? = Control.mem[k]? := by
  apply writeLog_out
  simp only [blockLog, OutL, Nat.reduceAdd, and_true]
  omega

local macro "boundary_read" : tactic =>
  `(tactic| (simp only [read32, read64, readLE, lookup]; decide))

theorem array0 : read64 mem 0x82000000 = some 0x82000020 := by boundary_read
theorem array1 : read64 mem 0x82000008 = some 0x82000020 := by boundary_read
theorem blockTag : read32 mem 0x82000020 = some 2 := by boundary_read
theorem blockArray : read64 mem 0x82000028 = some 0 := by boundary_read
theorem blockCount : read32 mem 0x82000030 = some 0 := by boundary_read

theorem blockWithin : StmtReprWithin mem AstPage 0x82000020 (.block []) := by
  apply StmtReprWithin.block blockTag _ blockArray _ blockCount _ StmtArrayReprWithin.nil
  all_goals intro i hi; unfold AstPage; omega

theorem programWithin : ProgramReprWithin mem AstPage 0x82000000 2 program := by
  refine ⟨StmtArrayReprWithin.cons array0 ?_ blockWithin
    (StmtArrayReprWithin.cons array1 ?_ blockWithin StmtArrayReprWithin.nil), rfl⟩
  all_goals intro i hi; unfold AstPage; omega

theorem block_unique {s : Stmt} (h : StmtRepr mem 0x82000020 s) : s = .block [] := by
  cases h with
  | block ht hp hn hs =>
    rw [Option.some.inj (hp.symm.trans blockArray),
      Option.some.inj (hn.symm.trans blockCount)] at hs
    cases hs
    rfl
  | _ => simp_all [blockTag]

theorem program_unique {p : Program} (h : ProgramRepr mem 0x82000000 2 p) :
    p = program := by
  cases h.1 with
  | cons hp hs ht =>
    rw [Option.some.inj (hp.symm.trans array0)] at hs
    have first := block_unique hs
    cases ht with
    | cons hp hs ht =>
      rw [Option.some.inj (hp.symm.trans array1)] at hs
      have second := block_unique hs
      cases ht
      simp_all [program]

theorem storeAgreement : AgreeP StorePage Control.mem mem := by
  intro k hk
  exact (unchanged (Or.inl (by unfold StorePage at hk; omega))).symm

def view : StoreView mem := Control.view.transport storeAgreement

theorem memoryFacts : SnapshotMemoryFacts mem where
  mainRa := by boundary_read
  text := Control.memoryFacts.text.transport (fun _ _ hhi => unchanged (Or.inl (by omega)))
  rodata := Control.memoryFacts.rodata.transport (fun _ _ hhi => unchanged (Or.inl (by omega)))
  statics := by
    simpa (disch := decide) only [Code.ImageStaticsLoaded, Code.imgLldFmt,
      Code.imgDecPointStr, Code.imgParseSlotD, Code.imgParseSlotL, Code.imgFnSlot,
      Code.imgDecPointPtr, Code.imgMbCurMax, Code.imgImpurePtr, unchanged]
      using Control.memoryFacts.statics
  console := ConsoleStream.of_agree (by
    intro k hk
    apply unchanged
    left
    unfold ConsoleFoot consoleImpurePtrAddr consoleReent consoleStdout consoleBuf at hk
    omega) Control.memoryFacts.console
  exitRuntime := Control.memoryFacts.exitRuntime.transport (by
    intro k hk
    obtain ⟨r, hr, hlo, hhi⟩ := hk
    have hb : ∀ r ∈ exitRuntimeExtraRegions, r.1 + r.2 ≤ 0x82000000 := by decide
    exact (unchanged (Or.inl (by have := hb r hr; omega))).symm)
  globals := by boundary_read
  depth := by boundary_read
  stackBytes := by
    intro k hlo hhi
    rw [unchanged (Or.inr (by change 0x87800000 ≤ k at hlo; omega))]
    exact Control.memoryFacts.stackBytes k hlo hhi
  store := view.store
  storeSurvives := by
    intro m' hag
    exact (view.transport (fun k hk => hag k (storePage_outside_prefix hk))).store

theorem arraysReady : StoreArraysReady mem phif initSt.store where
  namesAligned := by
    intro fa hf pn hp
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    have he := Option.some.inj (hp.symm.trans view.names)
    subst pn
    decide
  valuesAligned := by
    intro fa hf pv hp
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    have he := Option.some.inj (hp.symm.trans view.values)
    subst pv
    decide
  valueWords := by
    intro fa hf pv hp i hi
    change fa < 1 at hf
    have he : fa = 0 := by omega
    subst fa
    have he := Option.some.inj (hp.symm.trans view.values)
    subst pv
    exact valueWordsTotal_transport (Control.arraysReady.valueWords 0 (by decide)
      0x81000080 Control.reads.values i hi) storeAgreement (by
        intro k hk
        change i < 3 at hi
        unfold valHeader StorePage at *
        omega)

theorem initialOwned : InitialOwned mem arena stackSL phif phic 0x82000000 2
    Control.ownershipData where
  heapLower := by decide
  heapUpper := by decide
  heap := ⟨Control.ledger, Control.immutable, Control.reserved, storeOwned view⟩
  arrays := arraysReady
  program := by
    intro p hp
    rw [program_unique hp]
    exact programWithin.mono (fun _ hk => Or.inr (Or.inr (Or.inr hk)))

theorem loaded : Vsa.Refine.Loaded interpRunLayout program config :=
  ⟨0x82000000, 2, programWithin.erase, fixedInp, Nfixed, arena, phif, phic, 0,
    { toInterpRunPhysicalFacts := memoryFacts.physicalFacts
      ownership := ⟨Control.ownershipData, initialOwned⟩ }⟩

theorem source_terminates : BigStep program "" := by
  let st1 : Vsa.While.St := ⟨(initSt.store.allocFrame (some 0)).1, ""⟩
  let st2 : Vsa.While.St := ⟨(st1.store.allocFrame (some 0)).1, ""⟩
  have first : ExecS initSt 0 0 (.block []) st1 .normal :=
    ExecS.block initSt 0 0 [] _ _ st1 .normal rfl (ExecSeq.nil st1 0 _)
  have second : ExecS st1 0 0 (.block []) st2 .normal :=
    ExecS.block st1 0 0 [] _ _ st2 .normal rfl (ExecSeq.nil st2 0 _)
  exact ⟨st2, ExecSeq.consNormal _ _ _ _ _ _ _ _ first
    (ExecSeq.consNormal _ _ _ _ _ _ _ _ second (ExecSeq.nil st2 0 0)), rfl⟩

/-- This admitted snapshot leaves the allocator's top pointer zero. -/
theorem top_zero : read64 mem 0x8001ad20 = some 0 := by boundary_read

#print axioms loaded
#print axioms source_terminates
#print axioms top_zero
end Vsa.Sim.AllocatorBoundary
