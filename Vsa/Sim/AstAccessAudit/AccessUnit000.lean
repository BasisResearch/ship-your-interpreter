import Vsa.Sim.AstAccessAudit.AccessData
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part08
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch05Part14
import Vsa.Sim.DecodeTable.Batch08Part23
import Vsa.Sim.DecodeTable.Batch09Part01
import Vsa.Sim.DecodeTable.Batch09Part04
import Vsa.Sim.DecodeTable.Batch09Part09
import Vsa.Sim.DecodeTable.Batch09Part10
import Vsa.Sim.DecodeTable.Batch15Part22
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.AstAccessAudit
open Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg000 chain
  [(0x800043ec#64, 0xf5010113#32),
   (0x800043f0#64, 0xa13023#32),
   (0x800043f4#64, 0x1050513#32),
   (0x800043f8#64, 0xa113423#32),
   (0x800043fc#64, 0xa813023#32),
   (0x80004400#64, 0x8913c23#32),
   (0x80004404#64, 0x9213823#32),
   (0x80004408#64, 0x9313423#32),
   (0x8000440c#64, 0x9413023#32),
   (0x80004410#64, 0x7513c23#32),
   (0x80004414#64, 0x7613823#32),
   (0x80004418#64, 0xb13c23#32),
   (0x8000441c#64, 0xc13823#32),
   (0x80004420#64, 0xd13423#32)]

def traceLds000 : List (List (BitVec 8)) :=
  []

theorem facts000 : ChainFacts (writeLog snapshotMem traceD000.log)
    (writeLog snapshotMem traceD000.log) traceD000.regs traceLds000 traceSeg000 := by
  have kind0 : (mkLine 0x800043ec#64 0xf5010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x800043f0#64 0xa13023#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x800043f4#64 0x1050513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x800043f8#64 0xa113423#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x800043fc#64 0xa813023#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80004400#64 0x8913c23#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80004404#64 0x9213823#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x80004408#64 0x9313423#32).kind = MKind.sd := by decide
  have kind8 : (mkLine 0x8000440c#64 0x9413023#32).kind = MKind.sd := by decide
  have kind9 : (mkLine 0x80004410#64 0x7513c23#32).kind = MKind.sd := by decide
  have kind10 : (mkLine 0x80004414#64 0x7613823#32).kind = MKind.sd := by decide
  have kind11 : (mkLine 0x80004418#64 0xb13c23#32).kind = MKind.sd := by decide
  have kind12 : (mkLine 0x8000441c#64 0xc13823#32).kind = MKind.sd := by decide
  have kind13 : (mkLine 0x80004420#64 0xd13423#32).kind = MKind.sd := by decide
  simp only [traceSeg000, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00a13023
    | exact DecodeTable.decode_00b13c23
    | exact DecodeTable.decode_00c13823
    | exact DecodeTable.decode_00d13423
    | exact DecodeTable.decode_01050513
    | exact DecodeTable.decode_07513c23
    | exact DecodeTable.decode_07613823
    | exact DecodeTable.decode_08913c23
    | exact DecodeTable.decode_09213823
    | exact DecodeTable.decode_09313423
    | exact DecodeTable.decode_09413023
    | exact DecodeTable.decode_0a113423
    | exact DecodeTable.decode_0a813023
    | exact DecodeTable.decode_f5010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, kind12, kind13, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run000 {c : Config} (h : AccessHolds traceD000 c) :
    ∃ c', Steps c c' ∧ AccessHolds traceD001 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg000 traceLds000 (by decide) facts000 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run000
end Vsa.Sim.AstAccessAudit
