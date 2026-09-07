import Vsa.Sim.AstAccessAudit.AccessData
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg006 chain
  [(0x80004460#64, 0x13783#32),
   (0x80004464#64, 0x5810693#32),
   (0x80004468#64, 0x48593#32),
   (0x8000446c#64, 0x7b603#32),
   (0x80004470#64, 0x78513#32)]

def traceLds006 : List (List (BitVec 8)) :=
  [[0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts006 : ChainFacts (writeLog snapshotMem traceD006.log)
    (writeLog snapshotMem traceD006.log) traceD006.regs traceLds006 traceSeg006 := by
  have kind0 : (mkLine 0x80004460#64 0x13783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004464#64 0x5810693#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80004468#64 0x48593#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000446c#64 0x7b603#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80004470#64 0x78513#32).kind = MKind.addi := by decide
  simp only [traceSeg006, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00013783
    | exact DecodeTable.decode_00048593
    | exact DecodeTable.decode_00078513
    | exact DecodeTable.decode_0007b603
    | exact DecodeTable.decode_05810693
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run006 {c : Config} (h : AccessHolds traceD006 c) :
    ∃ c', Steps c c' ∧ AccessHolds traceD007 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg006 traceLds006 (by decide) facts006 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run006
end Vsa.Sim.AstAccessAudit
