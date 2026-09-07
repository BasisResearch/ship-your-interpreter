import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch02Part21
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part05
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part11
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch03Part20
import Vsa.Sim.DecodeTable.Batch03Part21
import Vsa.Sim.DecodeTable.Batch04Part02
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part07
import Vsa.Sim.DecodeTable.Batch04Part08
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch04Part31
import Vsa.Sim.DecodeTable.Batch05Part10
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch06Part14
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part25
import Vsa.Sim.DecodeTable.Batch07Part03
import Vsa.Sim.DecodeTable.Batch07Part04
import Vsa.Sim.DecodeTable.Batch07Part05
import Vsa.Sim.DecodeTable.Batch07Part06
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch07Part24
import Vsa.Sim.DecodeTable.Batch07Part31
import Vsa.Sim.DecodeTable.Batch08Part01
import Vsa.Sim.DecodeTable.Batch08Part04
import Vsa.Sim.DecodeTable.Batch08Part05
import Vsa.Sim.DecodeTable.Batch08Part24
import Vsa.Sim.DecodeTable.Batch08Part27
import Vsa.Sim.DecodeTable.Batch08Part32
import Vsa.Sim.DecodeTable.Batch09Part03
import Vsa.Sim.DecodeTable.Batch09Part05
import Vsa.Sim.DecodeTable.Batch09Part07
import Vsa.Sim.DecodeTable.Batch09Part17
import Vsa.Sim.DecodeTable.Batch11Part15
import Vsa.Sim.DecodeTable.Batch11Part22
import Vsa.Sim.DecodeTable.Batch11Part30
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch12Part21
import Vsa.Sim.DecodeTable.Batch12Part27
import Vsa.Sim.DecodeTable.Batch13Part15
import Vsa.Sim.DecodeTable.Batch13Part20
import Vsa.Sim.DecodeTable.Batch13Part28
import Vsa.Sim.DecodeTable.Batch14Part21
import Vsa.Sim.DecodeTable.Batch15Part05
import Vsa.Sim.DecodeTable.Batch16Part07
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part17
import Vsa.Sim.DecodeTable.Batch16Part19
import Vsa.Sim.DecodeTable.Batch16Part25
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
import Vsa.Sim.OutputAliasTraceAlu
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg101 chain
  [(0x8000281c#64, 0x300793#32),
   (0x80002820#64, 0xb53423#32),
   (0x80002824#64, 0xf52023#32)]
    terminator ⟨0x80002828#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds101 : List (List (BitVec 8)) :=
  []

theorem facts101 : ChainFacts (writeLog snapshotMem traceD101.log)
    (writeLog snapshotMem traceD101.log) traceD101.regs traceLds101 traceSeg101 := by
  have kind0 : (mkLine 0x8000281c#64 0x300793#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002820#64 0xb53423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80002824#64 0xf52023#32).kind = MKind.sw := by decide
  simp only [traceSeg101, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00300793
    | exact DecodeTable.decode_00b53423
    | exact DecodeTable.decode_00f52023
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run101 {c : Config} (h : TraceHolds traceD101 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD102 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg101 traceLds101 (by decide) facts101 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 127 ++ (evalBlocks traceSeg101 (SegEvalState.init traceD101.regs traceLds101)).log = traceStores.take 129
  have hw : (evalBlocks traceSeg101 (SegEvalState.init traceD101.regs traceLds101)).log = (traceStores.drop 127).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run101
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg102 chain
  []
    terminator ⟨0x8000341c#64, 0xfd1ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xfd#8, .j, 0, 0, 0#13, 0x1fffd0#21, 0#12⟩ ;;
  [(0x800033ec#64, 0x43813083#32),
   (0x800033f0#64, 0x43013403#32),
   (0x800033f4#64, 0x42013903#32),
   (0x800033f8#64, 0x48513#32),
   (0x800033fc#64, 0x42813483#32),
   (0x80003400#64, 0x44010113#32)]
    terminator ⟨0x80003404#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds102 : List (List (BitVec 8)) :=
  [[0x1c#8, 0x35#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xc0#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xd8#8, 0xfb#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts102 : ChainFacts (writeLog snapshotMem traceD102.log)
    (writeLog snapshotMem traceD102.log) traceD102.regs traceLds102 traceSeg102 := by
  have kind0 : (mkLine 0x800033ec#64 0x43813083#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800033f0#64 0x43013403#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800033f4#64 0x42013903#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x800033f8#64 0x48513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x800033fc#64 0x42813483#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x80003400#64 0x44010113#32).kind = MKind.addi := by decide
  simp only [traceSeg102, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_42013903
    | exact DecodeTable.decode_42813483
    | exact DecodeTable.decode_43013403
    | exact DecodeTable.decode_43813083
    | exact DecodeTable.decode_44010113
    | exact DecodeTable.decode_fd1ff06f
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run102 {c : Config} (h : TraceHolds traceD102 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD103 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg102 traceLds102 (by decide) facts102 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 129 ++ (evalBlocks traceSeg102 (SegEvalState.init traceD102.regs traceLds102)).log = traceStores.take 129
  have hw : (evalBlocks traceSeg102 (SegEvalState.init traceD102.regs traceLds102)).log = (traceStores.drop 129).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run102
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg103 chain
  [(0x8000351c#64, 0x842603#32),
   (0x80003520#64, 0xc00713#32),
   (0x80003524#64, 0x442403#32),
   (0x80003528#64, 0xff56079b#32),
   (0x8000352c#64, 0x9012503#32),
   (0x80003530#64, 0x9813883#32)]
    terminator ⟨0x80003534#64, 0x3ef76a63#32, 0x63#8, 0x6a#8, 0xf7#8, 0x3e#8, .br bop.BLTU false, 14, 15, 0x03f4#13, 0#21, 0#12⟩ ;;
  [(0x80003538#64, 0x2079713#32),
   (0x8000353c#64, 0x1e75793#32),
   (0x80003540#64, 0x17717#32),
   (0x80003544#64, 0xa4470713#32),
   (0x80003548#64, 0xe787b3#32),
   (0x8000354c#64, 0x7a783#32),
   (0x80003550#64, 0x13803#32),
   (0x80003554#64, 0xe787b3#32)]
    terminator ⟨0x80003558#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds103 : List (List (BitVec 8)) :=
  [[0x13#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x3#8, 0x0#8, 0x0#8, 0x0#8],
   [0x40#8, 0x1#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x60#8, 0x97#8, 0xfe#8, 0xff#8],
   [0x3#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts103 : ChainFacts (writeLog snapshotMem traceD103.log)
    (writeLog snapshotMem traceD103.log) traceD103.regs traceLds103 traceSeg103 := by
  have kind0 : (mkLine 0x8000351c#64 0x842603#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80003520#64 0xc00713#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80003524#64 0x442403#32).kind = MKind.lw := by decide
  have kind3 : (mkLine 0x80003528#64 0xff56079b#32).kind = MKind.addiw := by decide
  have kind4 : (mkLine 0x8000352c#64 0x9012503#32).kind = MKind.lw := by decide
  have kind5 : (mkLine 0x80003530#64 0x9813883#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80003538#64 0x2079713#32).kind = MKind.slli := by decide
  have kind7 : (mkLine 0x8000353c#64 0x1e75793#32).kind = MKind.srli := by decide
  have kind8 : (mkLine 0x80003540#64 0x17717#32).kind = MKind.auipc := by decide
  have kind9 : (mkLine 0x80003544#64 0xa4470713#32).kind = MKind.addi := by decide
  have kind10 : (mkLine 0x80003548#64 0xe787b3#32).kind = MKind.add := by decide
  have kind11 : (mkLine 0x8000354c#64 0x7a783#32).kind = MKind.lw := by decide
  have kind12 : (mkLine 0x80003550#64 0x13803#32).kind = MKind.ld := by decide
  have kind13 : (mkLine 0x80003554#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg103, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00013803
    | exact DecodeTable.decode_00017717
    | exact DecodeTable.decode_00078067
    | exact DecodeTable.decode_0007a783
    | exact DecodeTable.decode_00442403
    | exact DecodeTable.decode_00842603
    | exact DecodeTable.decode_00c00713
    | exact DecodeTable.decode_00e787b3
    | exact DecodeTable.decode_01e75793
    | exact DecodeTable.decode_02079713
    | exact DecodeTable.decode_09012503
    | exact DecodeTable.decode_09813883
    | exact DecodeTable.decode_3ef76a63
    | exact DecodeTable.decode_a4470713
    | exact DecodeTable.decode_ff56079b
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, kind12, kind13, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run103 {c : Config} (h : TraceHolds traceD103 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD104 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg103 traceLds103 (by decide) facts103 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 129 ++ (evalBlocks traceSeg103 (SegEvalState.init traceD103.regs traceLds103)).log = traceStores.take 129
  have hw : (evalBlocks traceSeg103 (SegEvalState.init traceD103.regs traceLds103)).log = (traceStores.drop 129).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run103
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg104 chain
  [(0x800036e4#64, 0x7813883#32),
   (0x800036e8#64, 0x8013803#32),
   (0x800036ec#64, 0x8813603#32),
   (0x800036f0#64, 0x9013683#32),
   (0x800036f4#64, 0x9813703#32),
   (0x800036f8#64, 0xa013783#32),
   (0x800036fc#64, 0x2010593#32),
   (0x80003700#64, 0x4010513#32),
   (0x80003704#64, 0x5113023#32),
   (0x80003708#64, 0x5013423#32),
   (0x8000370c#64, 0x4c13823#32),
   (0x80003710#64, 0x2d13023#32),
   (0x80003714#64, 0x2e13423#32),
   (0x80003718#64, 0x2f13823#32)]

def traceLds104 : List (List (BitVec 8)) :=
  [[0x3#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x7c#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x3#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x40#8, 0x1#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts104 : ChainFacts (writeLog snapshotMem traceD104.log)
    (writeLog snapshotMem traceD104.log) traceD104.regs traceLds104 traceSeg104 := by
  have kind0 : (mkLine 0x800036e4#64 0x7813883#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800036e8#64 0x8013803#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800036ec#64 0x8813603#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x800036f0#64 0x9013683#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x800036f4#64 0x9813703#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x800036f8#64 0xa013783#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x800036fc#64 0x2010593#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003700#64 0x4010513#32).kind = MKind.addi := by decide
  have kind8 : (mkLine 0x80003704#64 0x5113023#32).kind = MKind.sd := by decide
  have kind9 : (mkLine 0x80003708#64 0x5013423#32).kind = MKind.sd := by decide
  have kind10 : (mkLine 0x8000370c#64 0x4c13823#32).kind = MKind.sd := by decide
  have kind11 : (mkLine 0x80003710#64 0x2d13023#32).kind = MKind.sd := by decide
  have kind12 : (mkLine 0x80003714#64 0x2e13423#32).kind = MKind.sd := by decide
  have kind13 : (mkLine 0x80003718#64 0x2f13823#32).kind = MKind.sd := by decide
  simp only [traceSeg104, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_02010593
    | exact DecodeTable.decode_02d13023
    | exact DecodeTable.decode_02e13423
    | exact DecodeTable.decode_02f13823
    | exact DecodeTable.decode_04010513
    | exact DecodeTable.decode_04c13823
    | exact DecodeTable.decode_05013423
    | exact DecodeTable.decode_05113023
    | exact DecodeTable.decode_07813883
    | exact DecodeTable.decode_08013803
    | exact DecodeTable.decode_08813603
    | exact DecodeTable.decode_09013683
    | exact DecodeTable.decode_09813703
    | exact DecodeTable.decode_0a013783
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, kind12, kind13, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run104 {c : Config} (h : TraceHolds traceD104 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD105 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg104 traceLds104 (by decide) facts104 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 129 ++ (evalBlocks traceSeg104 (SegEvalState.init traceD104.regs traceLds104)).log = traceStores.take 135
  have hw : (evalBlocks traceSeg104 (SegEvalState.init traceD104.regs traceLds104)).log = (traceStores.drop 129).take 6 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run104
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts105 : TraceCallFacts traceD105 0x940ff0ef#32
    (instruction.JAL (0x1ff140#21, gprIdx 1)) 0xef#8 0xf0#8 0xf#8 0x94#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_940ff0ef

theorem run105 {c : Config} (h : TraceHolds traceD105 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD106 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x940ff0ef#32 0x1ff140#21 0xef#8 0xf0#8 0xf#8 0x94#8 facts105 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run105
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg106 chain
  [(0x8000285c#64, 0x52703#32),
   (0x80002860#64, 0x5a783#32)]
    terminator ⟨0x80002864#64, 0x02e79463#32, 0x63#8, 0x94#8, 0xe7#8, 0x02#8, .br bop.BNE false, 15, 14, 0x0028#13, 0#21, 0#12⟩ ;;
  [(0x80002868#64, 0x500713#32)]
    terminator ⟨0x8000286c#64, 0x02f76063#32, 0x63#8, 0x60#8, 0xf7#8, 0x02#8, .br bop.BLTU false, 14, 15, 0x0020#13, 0#21, 0#12⟩ ;;
  [(0x80002870#64, 0x17717#32),
   (0x80002874#64, 0x68870713#32),
   (0x80002878#64, 0x279793#32),
   (0x8000287c#64, 0xe787b3#32),
   (0x80002880#64, 0x7a783#32),
   (0x80002884#64, 0xe787b3#32)]
    terminator ⟨0x80002888#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds106 : List (List (BitVec 8)) :=
  [[0x3#8, 0x0#8, 0x0#8, 0x0#8],
   [0x3#8, 0x0#8, 0x0#8, 0x0#8],
   [0xcc#8, 0x89#8, 0xfe#8, 0xff#8]]

theorem facts106 : ChainFacts (writeLog snapshotMem traceD106.log)
    (writeLog snapshotMem traceD106.log) traceD106.regs traceLds106 traceSeg106 := by
  have kind0 : (mkLine 0x8000285c#64 0x52703#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80002860#64 0x5a783#32).kind = MKind.lw := by decide
  have kind2 : (mkLine 0x80002868#64 0x500713#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80002870#64 0x17717#32).kind = MKind.auipc := by decide
  have kind4 : (mkLine 0x80002874#64 0x68870713#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x80002878#64 0x279793#32).kind = MKind.slli := by decide
  have kind6 : (mkLine 0x8000287c#64 0xe787b3#32).kind = MKind.add := by decide
  have kind7 : (mkLine 0x80002880#64 0x7a783#32).kind = MKind.lw := by decide
  have kind8 : (mkLine 0x80002884#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg106, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00017717
    | exact DecodeTable.decode_00052703
    | exact DecodeTable.decode_0005a783
    | exact DecodeTable.decode_00078067
    | exact DecodeTable.decode_0007a783
    | exact DecodeTable.decode_00279793
    | exact DecodeTable.decode_00500713
    | exact DecodeTable.decode_00e787b3
    | exact DecodeTable.decode_02e79463
    | exact DecodeTable.decode_02f76063
    | exact DecodeTable.decode_68870713
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run106 {c : Config} (h : TraceHolds traceD106 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD107 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg106 traceLds106 (by decide) facts106 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 135 ++ (evalBlocks traceSeg106 (SegEvalState.init traceD106.regs traceLds106)).log = traceStores.take 135
  have hw : (evalBlocks traceSeg106 (SegEvalState.init traceD106.regs traceLds106)).log = (traceStores.drop 135).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run106
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg107 chain
  [(0x800028c4#64, 0x85b583#32),
   (0x800028c8#64, 0x853503#32),
   (0x800028cc#64, 0xff010113#32),
   (0x800028d0#64, 0x113423#32)]

def traceLds107 : List (List (BitVec 8)) :=
  [[0x40#8, 0x1#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x97#8, 0xbb#8, 0x1#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts107 : ChainFacts (writeLog snapshotMem traceD107.log)
    (writeLog snapshotMem traceD107.log) traceD107.regs traceLds107 traceSeg107 := by
  have kind0 : (mkLine 0x800028c4#64 0x85b583#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800028c8#64 0x853503#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800028cc#64 0xff010113#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x800028d0#64 0x113423#32).kind = MKind.sd := by decide
  simp only [traceSeg107, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00113423
    | exact DecodeTable.decode_00853503
    | exact DecodeTable.decode_0085b583
    | exact DecodeTable.decode_ff010113
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run107 {c : Config} (h : TraceHolds traceD107 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD108 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg107 traceLds107 (by decide) facts107 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 135 ++ (evalBlocks traceSeg107 (SegEvalState.init traceD107.regs traceLds107)).log = traceStores.take 136
  have hw : (evalBlocks traceSeg107 (SegEvalState.init traceD107.regs traceLds107)).log = (traceStores.drop 135).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run107
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts108 : TraceCallFacts traceD108 0x5cc040ef#32
    (instruction.JAL (0x45cc#21, gprIdx 1)) 0xef#8 0x40#8 0xc0#8 0x5c#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_5cc040ef

theorem run108 {c : Config} (h : TraceHolds traceD108 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD109 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x5cc040ef#32 0x45cc#21 0xef#8 0x40#8 0xc0#8 0x5c#8 facts108 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run108
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD109_01 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x800028d8#64), (2, 0x87fff750#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x87fffbd8#64), (10, 0x8001bb97#64), (11, 0x82000140#64), (12, 0x80002f7c#64), (13, 0x3#64), (14, 0x7#64), (15, 0x800028c4#64), (16, 0x8001bb97#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x8001bb97#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 136,
    out := #["\n"], payload := 0x0#4 }

def traceD109_02 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x800028d8#64), (2, 0x87fff750#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x87fffbd8#64), (10, 0x8001bb98#64), (11, 0x82000141#64), (12, 0xa#64), (13, 0xa#64), (14, 0x7#64), (15, 0x800028c4#64), (16, 0x8001bb97#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x8001bb97#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 136,
    out := #["\n"], payload := 0x0#4 }

def traceD109_03 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x800028d8#64), (2, 0x87fff750#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x87fffbd8#64), (10, 0x8001bb98#64), (11, 0x82000141#64), (12, 0xa#64), (13, 0xa#64), (14, 0x7#64), (15, 0x800028c4#64), (16, 0x8001bb97#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x8001bb97#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 136,
    out := #["\n"], payload := 0x0#4 }

def traceD109_04 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x800028d8#64), (2, 0x87fff750#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x87fffbd8#64), (10, 0x8001bb99#64), (11, 0x82000142#64), (12, 0x0#64), (13, 0x0#64), (14, 0x7#64), (15, 0x800028c4#64), (16, 0x8001bb97#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x8001bb97#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 136,
    out := #["\n"], payload := 0x0#4 }

def traceD109_05 : TraceData :=
  { pc := 0x80006f9c#64,
    regs := [(1, 0x800028d8#64), (2, 0x87fff750#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x87fffbd8#64), (10, 0x8001bb99#64), (11, 0x82000142#64), (12, 0x0#64), (13, 0x0#64), (14, 0x7#64), (15, 0x800028c4#64), (16, 0x8001bb97#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x8001bb97#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 136,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg109_00 chain
  [(0x80006ea0#64, 0xb56733#32),
   (0x80006ea4#64, 0xfff00393#32),
   (0x80006ea8#64, 0x777713#32)]
    terminator ⟨0x80006eac#64, 0x0c071c63#32, 0x63#8, 0x1c#8, 0x07#8, 0x0c#8, .br bop.BNE true, 14, 0, 0x00d8#13, 0#21, 0#12⟩

def traceLds109_00 : List (List (BitVec 8)) :=
  []

theorem facts109_00 : ChainFacts (writeLog snapshotMem traceD109.log)
    (writeLog snapshotMem traceD109.log) traceD109.regs traceLds109_00 traceSeg109_00 := by
  have kind0 : (mkLine 0x80006ea0#64 0xb56733#32).kind = MKind.or := by decide
  have kind1 : (mkLine 0x80006ea4#64 0xfff00393#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80006ea8#64 0x777713#32).kind = MKind.andi := by decide
  simp only [traceSeg109_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00777713
    | exact DecodeTable.decode_00b56733
    | exact DecodeTable.decode_0c071c63
    | exact DecodeTable.decode_fff00393
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run109_00 {c : Config} (h : TraceHolds traceD109 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD109_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg109_00 traceLds109_00 (by decide) facts109_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 136 ++ (evalBlocks traceSeg109_00 (SegEvalState.init traceD109.regs traceLds109_00)).log = traceStores.take 136
  have hw : (evalBlocks traceSeg109_00 (SegEvalState.init traceD109.regs traceLds109_00)).log = (traceStores.drop 136).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run109_00

#derive_case traceSeg109_01 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds109_01 : List (List (BitVec 8)) :=
  [[0xa#8],
   [0xa#8]]

theorem facts109_01 : ChainFacts (writeLog snapshotMem traceD109_01.log)
    (writeLog snapshotMem traceD109_01.log) traceD109_01.regs traceLds109_01 traceSeg109_01 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg109_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00054603
    | exact DecodeTable.decode_0005c683
    | exact DecodeTable.decode_00150513
    | exact DecodeTable.decode_00158593
    | exact DecodeTable.decode_00d61463
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run109_01 {c : Config} (h : TraceHolds traceD109_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD109_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg109_01 traceLds109_01 (by decide) facts109_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 136 ++ (evalBlocks traceSeg109_01 (SegEvalState.init traceD109_01.regs traceLds109_01)).log = traceStores.take 136
  have hw : (evalBlocks traceSeg109_01 (SegEvalState.init traceD109_01.regs traceLds109_01)).log = (traceStores.drop 136).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run109_01

#derive_case traceSeg109_02 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds109_02 : List (List (BitVec 8)) :=
  []

theorem facts109_02 : ChainFacts (writeLog snapshotMem traceD109_02.log)
    (writeLog snapshotMem traceD109_02.log) traceD109_02.regs traceLds109_02 traceSeg109_02 := by
  simp only [traceSeg109_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run109_02 {c : Config} (h : TraceHolds traceD109_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD109_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg109_02 traceLds109_02 (by decide) facts109_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 136 ++ (evalBlocks traceSeg109_02 (SegEvalState.init traceD109_02.regs traceLds109_02)).log = traceStores.take 136
  have hw : (evalBlocks traceSeg109_02 (SegEvalState.init traceD109_02.regs traceLds109_02)).log = (traceStores.drop 136).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run109_02

#derive_case traceSeg109_03 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds109_03 : List (List (BitVec 8)) :=
  [[0x0#8],
   [0x0#8]]

theorem facts109_03 : ChainFacts (writeLog snapshotMem traceD109_03.log)
    (writeLog snapshotMem traceD109_03.log) traceD109_03.regs traceLds109_03 traceSeg109_03 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg109_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00054603
    | exact DecodeTable.decode_0005c683
    | exact DecodeTable.decode_00150513
    | exact DecodeTable.decode_00158593
    | exact DecodeTable.decode_00d61463
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run109_03 {c : Config} (h : TraceHolds traceD109_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD109_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg109_03 traceLds109_03 (by decide) facts109_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 136 ++ (evalBlocks traceSeg109_03 (SegEvalState.init traceD109_03.regs traceLds109_03)).log = traceStores.take 136
  have hw : (evalBlocks traceSeg109_03 (SegEvalState.init traceD109_03.regs traceLds109_03)).log = (traceStores.drop 136).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run109_03

#derive_case traceSeg109_04 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE false, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds109_04 : List (List (BitVec 8)) :=
  []

theorem facts109_04 : ChainFacts (writeLog snapshotMem traceD109_04.log)
    (writeLog snapshotMem traceD109_04.log) traceD109_04.regs traceLds109_04 traceSeg109_04 := by
  simp only [traceSeg109_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run109_04 {c : Config} (h : TraceHolds traceD109_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD109_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg109_04 traceLds109_04 (by decide) facts109_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 136 ++ (evalBlocks traceSeg109_04 (SegEvalState.init traceD109_04.regs traceLds109_04)).log = traceStores.take 136
  have hw : (evalBlocks traceSeg109_04 (SegEvalState.init traceD109_04.regs traceLds109_04)).log = (traceStores.drop 136).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run109_04

#derive_case traceSeg109_05 chain
  [(0x80006f9c#64, 0x40d60533#32)]
    terminator ⟨0x80006fa0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds109_05 : List (List (BitVec 8)) :=
  []

theorem facts109_05 : ChainFacts (writeLog snapshotMem traceD109_05.log)
    (writeLog snapshotMem traceD109_05.log) traceD109_05.regs traceLds109_05 traceSeg109_05 := by
  have kind0 : (mkLine 0x80006f9c#64 0x40d60533#32).kind = MKind.sub := by decide
  simp only [traceSeg109_05, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_40d60533
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run109_05 {c : Config} (h : TraceHolds traceD109_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD110 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg109_05 traceLds109_05 (by decide) facts109_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 136 ++ (evalBlocks traceSeg109_05 (SegEvalState.init traceD109_05.regs traceLds109_05)).log = traceStores.take 136
  have hw : (evalBlocks traceSeg109_05 (SegEvalState.init traceD109_05.regs traceLds109_05)).log = (traceStores.drop 136).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run109_05
theorem run109 {c : Config} (h : TraceHolds traceD109 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD110 c' := by
  obtain ⟨c0, s0, h0⟩ := run109_00 h
  obtain ⟨c1, s1, h1⟩ := run109_01 h0
  obtain ⟨c2, s2, h2⟩ := run109_02 h1
  obtain ⟨c3, s3, h3⟩ := run109_03 h2
  obtain ⟨c4, s4, h4⟩ := run109_04 h3
  obtain ⟨c5, s5, h5⟩ := run109_05 h4
  exact ⟨c5, (((((s0).trans s1).trans s2).trans s3).trans s4).trans s5, h5⟩

#print axioms run109
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg110 chain
  [(0x800028d8#64, 0x813083#32)]

def traceLds110 : List (List (BitVec 8)) :=
  [[0x20#8, 0x37#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts110 : ChainFacts (writeLog snapshotMem traceD110.log)
    (writeLog snapshotMem traceD110.log) traceD110.regs traceLds110 traceSeg110 := by
  have kind0 : (mkLine 0x800028d8#64 0x813083#32).kind = MKind.ld := by decide
  simp only [traceSeg110, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00813083
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run110 {c : Config} (h : TraceHolds traceD110 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD111 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg110 traceLds110 (by decide) facts110 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 136 ++ (evalBlocks traceSeg110 (SegEvalState.init traceD110.regs traceLds110)).log = traceStores.take 136
  have hw : (evalBlocks traceSeg110 (SegEvalState.init traceD110.regs traceLds110)).log = (traceStores.drop 136).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run110
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem run111 {c : Config} (h : TraceHolds traceD111 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD112 c' := by
  obtain ⟨c', hs, hp⟩ := h.sltiu_800028dc 0x0#64
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run111
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg112 chain
  [(0x800028e0#64, 0x1010113#32)]
    terminator ⟨0x800028e4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds112 : List (List (BitVec 8)) :=
  []

theorem facts112 : ChainFacts (writeLog snapshotMem traceD112.log)
    (writeLog snapshotMem traceD112.log) traceD112.regs traceLds112 traceSeg112 := by
  have kind0 : (mkLine 0x800028e0#64 0x1010113#32).kind = MKind.addi := by decide
  simp only [traceSeg112, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_01010113
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run112 {c : Config} (h : TraceHolds traceD112 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD113 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg112 traceLds112 (by decide) facts112 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 136 ++ (evalBlocks traceSeg112 (SegEvalState.init traceD112.regs traceLds112)).log = traceStores.take 136
  have hw : (evalBlocks traceSeg112 (SegEvalState.init traceD112.regs traceLds112)).log = (traceStores.drop 136).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run112
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg113 chain
  [(0x80003720#64, 0x50593#32),
   (0x80003724#64, 0x48513#32)]

def traceLds113 : List (List (BitVec 8)) :=
  []

theorem facts113 : ChainFacts (writeLog snapshotMem traceD113.log)
    (writeLog snapshotMem traceD113.log) traceD113.regs traceLds113 traceSeg113 := by
  have kind0 : (mkLine 0x80003720#64 0x50593#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80003724#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg113, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_00050593
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run113 {c : Config} (h : TraceHolds traceD113 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD114 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg113 traceLds113 (by decide) facts113 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 136 ++ (evalBlocks traceSeg113 (SegEvalState.init traceD113.regs traceLds113)).log = traceStores.take 136
  have hw : (evalBlocks traceSeg113 (SegEvalState.init traceD113.regs traceLds113)).log = (traceStores.drop 136).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run113
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts114 : TraceCallFacts traceD114 0x8d0ff0ef#32
    (instruction.JAL (0x1ff0d0#21, gprIdx 1)) 0xef#8 0xf0#8 0xf#8 0x8d#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_8d0ff0ef

theorem run114 {c : Config} (h : TraceHolds traceD114 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD115 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x8d0ff0ef#32 0x1ff0d0#21 0xef#8 0xf0#8 0xf#8 0x8d#8 facts114 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run114
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem run115 {c : Config} (h : TraceHolds traceD115 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD116 c' := by
  obtain ⟨c', hs, hp⟩ := h.sltu_800027f8 0x1#64
    (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run115
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg116 chain
  [(0x800027fc#64, 0x100793#32),
   (0x80002800#64, 0xb52423#32),
   (0x80002804#64, 0xf52023#32)]
    terminator ⟨0x80002808#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds116 : List (List (BitVec 8)) :=
  []

theorem facts116 : ChainFacts (writeLog snapshotMem traceD116.log)
    (writeLog snapshotMem traceD116.log) traceD116.regs traceLds116 traceSeg116 := by
  have kind0 : (mkLine 0x800027fc#64 0x100793#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002800#64 0xb52423#32).kind = MKind.sw := by decide
  have kind2 : (mkLine 0x80002804#64 0xf52023#32).kind = MKind.sw := by decide
  simp only [traceSeg116, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00100793
    | exact DecodeTable.decode_00b52423
    | exact DecodeTable.decode_00f52023
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run116 {c : Config} (h : TraceHolds traceD116 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD117 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg116 traceLds116 (by decide) facts116 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 136 ++ (evalBlocks traceSeg116 (SegEvalState.init traceD116.regs traceLds116)).log = traceStores.take 138
  have hw : (evalBlocks traceSeg116 (SegEvalState.init traceD116.regs traceLds116)).log = (traceStores.drop 136).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run116
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg117 chain
  [(0x8000372c#64, 0x41813983#32)]
    terminator ⟨0x80003730#64, 0xcbdff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xcb#8, .j, 0, 0, 0#13, 0x1ffcbc#21, 0#12⟩ ;;
  [(0x800033ec#64, 0x43813083#32),
   (0x800033f0#64, 0x43013403#32),
   (0x800033f4#64, 0x42013903#32),
   (0x800033f8#64, 0x48513#32),
   (0x800033fc#64, 0x42813483#32),
   (0x80003400#64, 0x44010113#32)]
    terminator ⟨0x80003404#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds117 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xfc#8, 0x41#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x40#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa8#8, 0xfc#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts117 : ChainFacts (writeLog snapshotMem traceD117.log)
    (writeLog snapshotMem traceD117.log) traceD117.regs traceLds117 traceSeg117 := by
  have kind0 : (mkLine 0x8000372c#64 0x41813983#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800033ec#64 0x43813083#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800033f0#64 0x43013403#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x800033f4#64 0x42013903#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x800033f8#64 0x48513#32).kind = MKind.addi := by decide
  have kind5 : (mkLine 0x800033fc#64 0x42813483#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80003400#64 0x44010113#32).kind = MKind.addi := by decide
  simp only [traceSeg117, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_41813983
    | exact DecodeTable.decode_42013903
    | exact DecodeTable.decode_42813483
    | exact DecodeTable.decode_43013403
    | exact DecodeTable.decode_43813083
    | exact DecodeTable.decode_44010113
    | exact DecodeTable.decode_cbdff06f
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run117 {c : Config} (h : TraceHolds traceD117 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD118 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg117 traceLds117 (by decide) facts117 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 138 ++ (evalBlocks traceSeg117 (SegEvalState.init traceD117.regs traceLds117)).log = traceStores.take 138
  have hw : (evalBlocks traceSeg117 (SegEvalState.init traceD117.regs traceLds117)).log = (traceStores.drop 138).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run117
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg118 chain
  [(0x800041fc#64, 0x3813603#32),
   (0x80004200#64, 0x4013683#32),
   (0x80004204#64, 0x4813783#32),
   (0x80004208#64, 0x1010513#32),
   (0x8000420c#64, 0xc13823#32),
   (0x80004210#64, 0xd13c23#32),
   (0x80004214#64, 0x2f13023#32)]

def traceLds118 : List (List (BitVec 8)) :=
  [[0x1#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts118 : ChainFacts (writeLog snapshotMem traceD118.log)
    (writeLog snapshotMem traceD118.log) traceD118.regs traceLds118 traceSeg118 := by
  have kind0 : (mkLine 0x800041fc#64 0x3813603#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004200#64 0x4013683#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80004204#64 0x4813783#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80004208#64 0x1010513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000420c#64 0xc13823#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80004210#64 0xd13c23#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80004214#64 0x2f13023#32).kind = MKind.sd := by decide
  simp only [traceSeg118, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00c13823
    | exact DecodeTable.decode_00d13c23
    | exact DecodeTable.decode_01010513
    | exact DecodeTable.decode_02f13023
    | exact DecodeTable.decode_03813603
    | exact DecodeTable.decode_04013683
    | exact DecodeTable.decode_04813783
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run118 {c : Config} (h : TraceHolds traceD118 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD119 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg118 traceLds118 (by decide) facts118 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 138 ++ (evalBlocks traceSeg118 (SegEvalState.init traceD118.regs traceLds118)).log = traceStores.take 141
  have hw : (evalBlocks traceSeg118 (SegEvalState.init traceD118.regs traceLds118)).log = (traceStores.drop 138).take 3 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run118
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts119 : TraceCallFacts traceD119 0xe14fe0ef#32
    (instruction.JAL (0x1fe614#21, gprIdx 1)) 0xef#8 0xe0#8 0x4f#8 0xe1#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_e14fe0ef

theorem run119 {c : Config} (h : TraceHolds traceD119 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD120 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xe14fe0ef#32 0x1fe614#21 0xef#8 0xe0#8 0x4f#8 0xe1#8 facts119 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run119
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg120 chain
  [(0x8000282c#64, 0x52783#32),
   (0x80002830#64, 0x100713#32)]
    terminator ⟨0x80002834#64, 0x02e78063#32, 0x63#8, 0x80#8, 0xe7#8, 0x02#8, .br bop.BEQ true, 15, 14, 0x0020#13, 0#21, 0#12⟩ ;;
  [(0x80002854#64, 0x852503#32)]
    terminator ⟨0x80002858#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds120 : List (List (BitVec 8)) :=
  [[0x1#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts120 : ChainFacts (writeLog snapshotMem traceD120.log)
    (writeLog snapshotMem traceD120.log) traceD120.regs traceLds120 traceSeg120 := by
  have kind0 : (mkLine 0x8000282c#64 0x52783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80002830#64 0x100713#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002854#64 0x852503#32).kind = MKind.lw := by decide
  simp only [traceSeg120, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00052783
    | exact DecodeTable.decode_00100713
    | exact DecodeTable.decode_00852503
    | exact DecodeTable.decode_02e78063
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run120 {c : Config} (h : TraceHolds traceD120 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD121 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg120 traceLds120 (by decide) facts120 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 141 ++ (evalBlocks traceSeg120 (SegEvalState.init traceD120.regs traceLds120)).log = traceStores.take 141
  have hw : (evalBlocks traceSeg120 (SegEvalState.init traceD120.regs traceLds120)).log = (traceStores.drop 141).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run120
end Vsa.Sim.OutputAliasLoaded
