import Vsa.Sim.AstAccessAudit.AccessData
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch01Part24
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch09Part01
import Vsa.Sim.DecodeTable.Batch09Part04
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DecodeTable.Batch15Part31
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg008 chain
  [(0x80003fe0#64, 0xf5010113#32),
   (0x80003fe4#64, 0xa813023#32),
   (0x80003fe8#64, 0x8913c23#32),
   (0x80003fec#64, 0x9213823#32),
   (0x80003ff0#64, 0x9313423#32),
   (0x80003ff4#64, 0xa113423#32),
   (0x80003ff8#64, 0x58413#32),
   (0x80003ffc#64, 0x50493#32),
   (0x80004000#64, 0x60993#32),
   (0x80004004#64, 0x68913#32),
   (0x80004008#64, 0x800813#32),
   (0x8000400c#64, 0x16717#32),
   (0x80004010#64, 0xfac70713#32)]

def traceLds008 : List (List (BitVec 8)) :=
  []

theorem facts008 : ChainFacts (writeLog snapshotMem traceD008.log)
    (writeLog snapshotMem traceD008.log) traceD008.regs traceLds008 traceSeg008 := by
  have kind0 : (mkLine 0x80003fe0#64 0xf5010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80003fe4#64 0xa813023#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80003fe8#64 0x8913c23#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80003fec#64 0x9213823#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80003ff0#64 0x9313423#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003ff4#64 0xa113423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80003ff8#64 0x58413#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003ffc#64 0x50493#32).kind = MKind.addi := by decide
  have kind8 : (mkLine 0x80004000#64 0x60993#32).kind = MKind.addi := by decide
  have kind9 : (mkLine 0x80004004#64 0x68913#32).kind = MKind.addi := by decide
  have kind10 : (mkLine 0x80004008#64 0x800813#32).kind = MKind.addi := by decide
  have kind11 : (mkLine 0x8000400c#64 0x16717#32).kind = MKind.auipc := by decide
  have kind12 : (mkLine 0x80004010#64 0xfac70713#32).kind = MKind.addi := by decide
  simp only [traceSeg008, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00016717
    | exact DecodeTable.decode_00050493
    | exact DecodeTable.decode_00058413
    | exact DecodeTable.decode_00060993
    | exact DecodeTable.decode_00068913
    | exact DecodeTable.decode_00800813
    | exact DecodeTable.decode_08913c23
    | exact DecodeTable.decode_09213823
    | exact DecodeTable.decode_09313423
    | exact DecodeTable.decode_0a113423
    | exact DecodeTable.decode_0a813023
    | exact DecodeTable.decode_f5010113
    | exact DecodeTable.decode_fac70713
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, kind12, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run008 {c : Config} (h : AccessHolds traceD008 c) :
    ∃ c', Steps c c' ∧ AccessHolds traceD009 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg008 traceLds008 (by decide) facts008 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run008
end Vsa.Sim.AstAccessAudit
