import Vsa.Sim.AstAccessAudit.AccessData
import Vsa.Sim.DecodeTable.Batch01Part13
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch03Part05
import Vsa.Sim.DecodeTable.Batch03Part07
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part24
import Vsa.Sim.DecodeTable.Batch06Part01
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch08Part07
import Vsa.Sim.DecodeTable.Batch09Part23
import Vsa.Sim.DecodeTable.Batch09Part25
import Vsa.Sim.DecodeTable.Batch12Part05
import Vsa.Sim.DecodeTable.Batch16Part02
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg003 chain
  []
    terminator ⟨0x80004428#64, 0x0e051063#32, 0x63#8, 0x10#8, 0x05#8, 0x0e#8, .br bop.BNE false, 10, 0, 0x00e0#13, 0#21, 0#12⟩ ;;
  [(0x8000442c#64, 0x1013783#32),
   (0x80004430#64, 0x50a93#32)]
    terminator ⟨0x80004434#64, 0x0ef05063#32, 0x63#8, 0x50#8, 0xf0#8, 0x0e#8, .br bop.BGE false, 0, 15, 0x00e0#13, 0#21, 0#12⟩ ;;
  [(0x80004438#64, 0x1013783#32),
   (0x8000443c#64, 0x1813403#32),
   (0x80004440#64, 0x46018b13#32),
   (0x80004444#64, 0x379913#32),
   (0x80004448#64, 0x1240933#32),
   (0x8000444c#64, 0x300993#32),
   (0x80004450#64, 0x100a13#32)]
    terminator ⟨0x80004454#64, 0x0380006f#32, 0x6f#8, 0x00#8, 0x80#8, 0x03#8, .j, 0, 0, 0#13, 0x000038#21, 0#12⟩ ;;
  [(0x8000448c#64, 0x813783#32),
   (0x80004490#64, 0x43483#32)]
    terminator ⟨0x80004494#64, 0xfc0782e3#32, 0xe3#8, 0x82#8, 0x07#8, 0xfc#8, .br bop.BEQ true, 15, 0, 0x1fc4#13, 0#21, 0#12⟩ ;;
  [(0x80004458#64, 0x5810513#32)]

def traceLds003 : List (List (BitVec 8)) :=
  [[0x2#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x2#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x40#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts003 : ChainFacts (writeLog snapshotMem traceD003.log)
    (writeLog snapshotMem traceD003.log) traceD003.regs traceLds003 traceSeg003 := by
  have kind0 : (mkLine 0x8000442c#64 0x1013783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004430#64 0x50a93#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80004438#64 0x1013783#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x8000443c#64 0x1813403#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80004440#64 0x46018b13#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80004444#64 0x379913#32).kind = MKind.slli := by decide
  have kind6 : (mkLine 0x80004448#64 0x1240933#32).kind = MKind.add := by decide
  have kind7 : (mkLine 0x8000444c#64 0x300993#32).kind = MKind.addi := by decide
  have kind8 : (mkLine 0x80004450#64 0x100a13#32).kind = MKind.addi := by decide
  have kind9 : (mkLine 0x8000448c#64 0x813783#32).kind = MKind.ld := by decide
  have kind10 : (mkLine 0x80004490#64 0x43483#32).kind = MKind.ld := by decide
  have kind11 : (mkLine 0x80004458#64 0x5810513#32).kind = MKind.addi := by decide
  simp only [traceSeg003, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00043483
    | exact DecodeTable.decode_00050a93
    | exact DecodeTable.decode_00100a13
    | exact DecodeTable.decode_00300993
    | exact DecodeTable.decode_00379913
    | exact DecodeTable.decode_00813783
    | exact DecodeTable.decode_01013783
    | exact DecodeTable.decode_01240933
    | exact DecodeTable.decode_01813403
    | exact DecodeTable.decode_0380006f
    | exact DecodeTable.decode_05810513
    | exact DecodeTable.decode_0e051063
    | exact DecodeTable.decode_0ef05063
    | exact DecodeTable.decode_46018b13
    | exact DecodeTable.decode_fc0782e3
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run003 {c : Config} (h : AccessHolds traceD003 c) :
    ∃ c', Steps c c' ∧ AccessHolds traceD004 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg003 traceLds003 (by decide) facts003 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run003
end Vsa.Sim.AstAccessAudit
