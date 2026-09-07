import Vsa.Sim.AstAccessAudit.AccessData
import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch03Part28
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch07Part13
import Vsa.Sim.DecodeTable.Batch07Part14
import Vsa.Sim.DecodeTable.Batch07Part15
import Vsa.Sim.DecodeTable.Batch07Part16
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DecodeTable.Batch08Part08
import Vsa.Sim.DecodeTable.Batch08Part09
import Vsa.Sim.DecodeTable.Batch08Part14
import Vsa.Sim.DecodeTable.Batch08Part25
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg002 chain
  [(0x80006ffc#64, 0x153023#32),
   (0x80007000#64, 0x853423#32),
   (0x80007004#64, 0x953823#32),
   (0x80007008#64, 0x1253c23#32),
   (0x8000700c#64, 0x3353023#32),
   (0x80007010#64, 0x3453423#32),
   (0x80007014#64, 0x3553823#32),
   (0x80007018#64, 0x3653c23#32),
   (0x8000701c#64, 0x5753023#32),
   (0x80007020#64, 0x5853423#32),
   (0x80007024#64, 0x5953823#32),
   (0x80007028#64, 0x5a53c23#32),
   (0x8000702c#64, 0x7b53023#32),
   (0x80007030#64, 0x6253423#32),
   (0x80007034#64, 0x513#32)]
    terminator ⟨0x80007038#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds002 : List (List (BitVec 8)) :=
  []

theorem facts002 : ChainFacts (writeLog snapshotMem traceD002.log)
    (writeLog snapshotMem traceD002.log) traceD002.regs traceLds002 traceSeg002 := by
  have kind0 : (mkLine 0x80006ffc#64 0x153023#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x80007000#64 0x853423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80007004#64 0x953823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80007008#64 0x1253c23#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x8000700c#64 0x3353023#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80007010#64 0x3453423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80007014#64 0x3553823#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x80007018#64 0x3653c23#32).kind = MKind.sd := by decide
  have kind8 : (mkLine 0x8000701c#64 0x5753023#32).kind = MKind.sd := by decide
  have kind9 : (mkLine 0x80007020#64 0x5853423#32).kind = MKind.sd := by decide
  have kind10 : (mkLine 0x80007024#64 0x5953823#32).kind = MKind.sd := by decide
  have kind11 : (mkLine 0x80007028#64 0x5a53c23#32).kind = MKind.sd := by decide
  have kind12 : (mkLine 0x8000702c#64 0x7b53023#32).kind = MKind.sd := by decide
  have kind13 : (mkLine 0x80007030#64 0x6253423#32).kind = MKind.sd := by decide
  have kind14 : (mkLine 0x80007034#64 0x513#32).kind = MKind.addi := by decide
  simp only [traceSeg002, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000513
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00153023
    | exact DecodeTable.decode_00853423
    | exact DecodeTable.decode_00953823
    | exact DecodeTable.decode_01253c23
    | exact DecodeTable.decode_03353023
    | exact DecodeTable.decode_03453423
    | exact DecodeTable.decode_03553823
    | exact DecodeTable.decode_03653c23
    | exact DecodeTable.decode_05753023
    | exact DecodeTable.decode_05853423
    | exact DecodeTable.decode_05953823
    | exact DecodeTable.decode_05a53c23
    | exact DecodeTable.decode_06253423
    | exact DecodeTable.decode_07b53023
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, kind12, kind13, kind14, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run002 {c : Config} (h : AccessHolds traceD002 c) :
    ∃ c', Steps c c' ∧ AccessHolds traceD003 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg002 traceLds002 (by decide) facts002 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run002
end Vsa.Sim.AstAccessAudit
