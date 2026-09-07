import Vsa.Sim.AstAccessAudit.AccessData
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg005 chain
  [(0x800027ec#64, 0x52023#32),
   (0x800027f0#64, 0x53423#32)]
    terminator ⟨0x800027f4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds005 : List (List (BitVec 8)) :=
  []

theorem facts005 : ChainFacts (writeLog snapshotMem traceD005.log)
    (writeLog snapshotMem traceD005.log) traceD005.regs traceLds005 traceSeg005 := by
  have kind0 : (mkLine 0x800027ec#64 0x52023#32).kind = MKind.sw := by decide
  have kind1 : (mkLine 0x800027f0#64 0x53423#32).kind = MKind.sd := by decide
  simp only [traceSeg005, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00052023
    | exact DecodeTable.decode_00053423
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run005 {c : Config} (h : AccessHolds traceD005 c) :
    ∃ c', Steps c c' ∧ AccessHolds traceD006 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg005 traceLds005 (by decide) facts005 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run005
end Vsa.Sim.AstAccessAudit
