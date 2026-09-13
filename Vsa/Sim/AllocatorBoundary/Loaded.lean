import Vsa.Sim.NativeNameAudit.ControlPhysical
import Vsa.Sim.RuntimeOwnershipTransport

/-!
The allocator-metadata audit snapshot: two empty blocks over the control store,
with `__malloc_av_` left zero. Its program is represented and every physical
boundary fact holds, but its top-chunk pointer is zero. A sparse Sail replay of
it faults inside `_malloc_r` after following a zero bin pointer. The dlmalloc
heap field of `InitialOwned` excludes it from `Loaded`.
-/

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

/-- Every physical boundary fact holds at the snapshot. -/
theorem physicalFacts : InterpRunPhysicalFacts config 0x82000000 2 fixedInp
    Nfixed arena phif phic 0 := memoryFacts.physicalFacts

theorem source_terminates : BigStep program "" := by
  let st1 : Vsa.While.St := ⟨(initSt.store.allocFrame (some 0)).1, ""⟩
  let st2 : Vsa.While.St := ⟨(st1.store.allocFrame (some 0)).1, ""⟩
  have first : ExecS initSt 0 0 (.block []) st1 .normal :=
    ExecS.block initSt 0 0 [] _ _ st1 .normal rfl (ExecSeq.nil st1 0 _)
  have second : ExecS st1 0 0 (.block []) st2 .normal :=
    ExecS.block st1 0 0 [] _ _ st2 .normal rfl (ExecSeq.nil st2 0 _)
  exact ⟨st2, ExecSeq.consNormal _ _ _ _ _ _ _ _ first
    (ExecSeq.consNormal _ _ _ _ _ _ _ _ second (ExecSeq.nil st2 0 0)), rfl⟩

/-- The snapshot leaves the allocator's top pointer zero. -/
theorem top_zero : read64 mem DlHeap.topAddr = some 0 := by
  simp only [DlHeap.topAddr, DlHeap.avAddr]
  boundary_read

/-- Address 8, where `_malloc_r` would read the zero top chunk's size, is not memory. -/
theorem top_header_absent : read64 mem (0 + 8) = none := by boundary_read

/-- The strengthened boundary excludes the snapshot. -/
theorem not_loaded : ¬ Vsa.Refine.Loaded interpRunLayout program config := by
  rintro ⟨_, _, -, _, _, _, _, _, _, F⟩
  obtain ⟨_, hD⟩ := F.ownership
  exact DlHeap.not_initialAllocator_of_top top_zero top_header_absent hD.allocator

#print axioms physicalFacts
#print axioms source_terminates
#print axioms not_loaded

end Vsa.Sim.AllocatorBoundary
