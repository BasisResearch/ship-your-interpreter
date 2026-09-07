import Vsa.Sim.DecodeTable.Batch01Part01
import Vsa.Sim.DecodeTable.Batch01Part04
import Vsa.Sim.DecodeTable.Batch01Part06
import Vsa.Sim.DecodeTable.Batch01Part08
import Vsa.Sim.DecodeTable.Batch01Part09
import Vsa.Sim.DecodeTable.Batch01Part10
import Vsa.Sim.DecodeTable.Batch01Part13
import Vsa.Sim.DecodeTable.Batch01Part14
import Vsa.Sim.DecodeTable.Batch01Part15
import Vsa.Sim.DecodeTable.Batch01Part16
import Vsa.Sim.DecodeTable.Batch01Part18
import Vsa.Sim.DecodeTable.Batch01Part19
import Vsa.Sim.DecodeTable.Batch01Part20
import Vsa.Sim.DecodeTable.Batch01Part21
import Vsa.Sim.DecodeTable.Batch01Part22
import Vsa.Sim.DecodeTable.Batch01Part23
import Vsa.Sim.DecodeTable.Batch01Part29
import Vsa.Sim.DecodeTable.Batch01Part32
import Vsa.Sim.DecodeTable.Batch02Part01
import Vsa.Sim.DecodeTable.Batch02Part03
import Vsa.Sim.DecodeTable.Batch02Part04
import Vsa.Sim.DecodeTable.Batch02Part06
import Vsa.Sim.DecodeTable.Batch02Part20
import Vsa.Sim.DecodeTable.Batch02Part22
import Vsa.Sim.DecodeTable.Batch02Part23
import Vsa.Sim.DecodeTable.Batch03Part03
import Vsa.Sim.DecodeTable.Batch03Part06
import Vsa.Sim.DecodeTable.Batch03Part09
import Vsa.Sim.DecodeTable.Batch03Part11
import Vsa.Sim.DecodeTable.Batch03Part13
import Vsa.Sim.DecodeTable.Batch03Part16
import Vsa.Sim.DecodeTable.Batch03Part17
import Vsa.Sim.DecodeTable.Batch03Part18
import Vsa.Sim.DecodeTable.Batch03Part19
import Vsa.Sim.DecodeTable.Batch03Part22
import Vsa.Sim.DecodeTable.Batch03Part23
import Vsa.Sim.DecodeTable.Batch03Part25
import Vsa.Sim.DecodeTable.Batch03Part26
import Vsa.Sim.DecodeTable.Batch03Part30
import Vsa.Sim.DecodeTable.Batch04Part03
import Vsa.Sim.DecodeTable.Batch04Part14
import Vsa.Sim.DecodeTable.Batch04Part16
import Vsa.Sim.DecodeTable.Batch04Part21
import Vsa.Sim.DecodeTable.Batch04Part24
import Vsa.Sim.DecodeTable.Batch04Part28
import Vsa.Sim.DecodeTable.Batch04Part30
import Vsa.Sim.DecodeTable.Batch05Part01
import Vsa.Sim.DecodeTable.Batch05Part07
import Vsa.Sim.DecodeTable.Batch05Part09
import Vsa.Sim.DecodeTable.Batch05Part11
import Vsa.Sim.DecodeTable.Batch05Part12
import Vsa.Sim.DecodeTable.Batch05Part13
import Vsa.Sim.DecodeTable.Batch05Part19
import Vsa.Sim.DecodeTable.Batch05Part20
import Vsa.Sim.DecodeTable.Batch05Part26
import Vsa.Sim.DecodeTable.Batch05Part27
import Vsa.Sim.DecodeTable.Batch05Part29
import Vsa.Sim.DecodeTable.Batch06Part02
import Vsa.Sim.DecodeTable.Batch06Part03
import Vsa.Sim.DecodeTable.Batch06Part16
import Vsa.Sim.DecodeTable.Batch06Part17
import Vsa.Sim.DecodeTable.Batch06Part28
import Vsa.Sim.DecodeTable.Batch06Part29
import Vsa.Sim.DecodeTable.Batch06Part30
import Vsa.Sim.DecodeTable.Batch06Part31
import Vsa.Sim.DecodeTable.Batch07Part07
import Vsa.Sim.DecodeTable.Batch07Part12
import Vsa.Sim.DecodeTable.Batch07Part17
import Vsa.Sim.DecodeTable.Batch07Part23
import Vsa.Sim.DecodeTable.Batch08Part11
import Vsa.Sim.DecodeTable.Batch08Part16
import Vsa.Sim.DecodeTable.Batch08Part19
import Vsa.Sim.DecodeTable.Batch08Part20
import Vsa.Sim.DecodeTable.Batch08Part22
import Vsa.Sim.DecodeTable.Batch09Part01
import Vsa.Sim.DecodeTable.Batch09Part03
import Vsa.Sim.DecodeTable.Batch09Part04
import Vsa.Sim.DecodeTable.Batch09Part08
import Vsa.Sim.DecodeTable.Batch09Part17
import Vsa.Sim.DecodeTable.Batch09Part18
import Vsa.Sim.DecodeTable.Batch09Part26
import Vsa.Sim.DecodeTable.Batch09Part28
import Vsa.Sim.DecodeTable.Batch09Part29
import Vsa.Sim.DecodeTable.Batch10Part12
import Vsa.Sim.DecodeTable.Batch10Part24
import Vsa.Sim.DecodeTable.Batch11Part04
import Vsa.Sim.DecodeTable.Batch11Part15
import Vsa.Sim.DecodeTable.Batch11Part22
import Vsa.Sim.DecodeTable.Batch12Part01
import Vsa.Sim.DecodeTable.Batch12Part02
import Vsa.Sim.DecodeTable.Batch12Part03
import Vsa.Sim.DecodeTable.Batch12Part22
import Vsa.Sim.DecodeTable.Batch13Part02
import Vsa.Sim.DecodeTable.Batch14Part09
import Vsa.Sim.DecodeTable.Batch14Part31
import Vsa.Sim.DecodeTable.Batch15Part01
import Vsa.Sim.DecodeTable.Batch15Part02
import Vsa.Sim.DecodeTable.Batch15Part03
import Vsa.Sim.DecodeTable.Batch15Part31
import Vsa.Sim.DecodeTable.Batch16Part01
import Vsa.Sim.DecodeTable.Batch16Part05
import Vsa.Sim.DecodeTable.Batch16Part06
import Vsa.Sim.DecodeTable.Batch16Part07
import Vsa.Sim.DecodeTable.Batch16Part09
import Vsa.Sim.DecodeTable.Batch16Part11
import Vsa.Sim.DecodeTable.Batch16Part25
import Vsa.Sim.DeriveCase
import Vsa.Sim.OutputAliasCalls
import Vsa.Sim.OutputAliasDecode
import Vsa.Sim.OutputAliasRun.Data
-- discipline: allow(R7-conj-tower-def) Generated independent transition endpoints; each post is the named TraceHolds structure. Existentials bind reached configurations for Steps composition, not anonymous representation towers.

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg121 chain
  [(0x8000421c#64, 0x800813#32),
   (0x80004220#64, 0x16717#32),
   (0x80004224#64, 0xd9870713#32)]
    terminator ⟨0x80004228#64, 0x0a050263#32, 0x63#8, 0x02#8, 0x05#8, 0x0a#8, .br bop.BEQ false, 10, 0, 0x00a4#13, 0#21, 0#12⟩ ;;
  [(0x8000422c#64, 0x1043403#32)]
    terminator ⟨0x80004230#64, 0xde5ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xde#8, .j, 0, 0, 0#13, 0x1ffde4#21, 0#12⟩ ;;
  [(0x80004014#64, 0x42783#32)]
    terminator ⟨0x80004018#64, 0x06f86c63#32, 0x63#8, 0x6c#8, 0xf8#8, 0x06#8, .br bop.BLTU false, 16, 15, 0x0078#13, 0#21, 0#12⟩ ;;
  [(0x8000401c#64, 0x46783#32),
   (0x80004020#64, 0x279793#32),
   (0x80004024#64, 0xe787b3#32),
   (0x80004028#64, 0x7a783#32),
   (0x8000402c#64, 0xe787b3#32)]
    terminator ⟨0x80004030#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds121 : List (List (BitVec 8)) :=
  [[0x20#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xb8#8, 0xa1#8, 0xfe#8, 0xff#8]]

theorem facts121 : ChainFacts (writeLog snapshotMem traceD121.log)
    (writeLog snapshotMem traceD121.log) traceD121.regs traceLds121 traceSeg121 := by
  have kind0 : (mkLine 0x8000421c#64 0x800813#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80004220#64 0x16717#32).kind = MKind.auipc := by decide
  have kind2 : (mkLine 0x80004224#64 0xd9870713#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000422c#64 0x1043403#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80004014#64 0x42783#32).kind = MKind.lw := by decide
  have kind5 : (mkLine 0x8000401c#64 0x46783#32).kind = MKind.lwu := by decide
  have kind6 : (mkLine 0x80004020#64 0x279793#32).kind = MKind.slli := by decide
  have kind7 : (mkLine 0x80004024#64 0xe787b3#32).kind = MKind.add := by decide
  have kind8 : (mkLine 0x80004028#64 0x7a783#32).kind = MKind.lw := by decide
  have kind9 : (mkLine 0x8000402c#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg121, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00016717
    | exact DecodeTable.decode_00042783
    | exact DecodeTable.decode_00046783
    | exact DecodeTable.decode_00078067
    | exact DecodeTable.decode_0007a783
    | exact DecodeTable.decode_00279793
    | exact DecodeTable.decode_00800813
    | exact DecodeTable.decode_00e787b3
    | exact DecodeTable.decode_01043403
    | exact DecodeTable.decode_06f86c63
    | exact DecodeTable.decode_0a050263
    | exact DecodeTable.decode_d9870713
    | exact DecodeTable.decode_de5ff06f
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run121 {c : Config} (h : TraceHolds traceD121 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD122 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg121 traceLds121 (by decide) facts121 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 141 ++ (evalBlocks traceSeg121 (SegEvalState.init traceD121.regs traceLds121)).log = traceStores.take 141
  have hw : (evalBlocks traceSeg121 (SegEvalState.init traceD121.regs traceLds121)).log = (traceStores.drop 141).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run121
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg122 chain
  [(0x80004170#64, 0x843603#32),
   (0x80004174#64, 0x1010513#32),
   (0x80004178#64, 0x98693#32),
   (0x8000417c#64, 0x48593#32)]

def traceLds122 : List (List (BitVec 8)) :=
  [[0x80#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts122 : ChainFacts (writeLog snapshotMem traceD122.log)
    (writeLog snapshotMem traceD122.log) traceD122.regs traceLds122 traceSeg122 := by
  have kind0 : (mkLine 0x80004170#64 0x843603#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80004174#64 0x1010513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80004178#64 0x98693#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x8000417c#64 0x48593#32).kind = MKind.addi := by decide
  simp only [traceSeg122, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00048593
    | exact DecodeTable.decode_00098693
    | exact DecodeTable.decode_00843603
    | exact DecodeTable.decode_01010513
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run122 {c : Config} (h : TraceHolds traceD122 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD123 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg122 traceLds122 (by decide) facts122 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 141 ++ (evalBlocks traceSeg122 (SegEvalState.init traceD122.regs traceLds122)).log = traceStores.take 141
  have hw : (evalBlocks traceSeg122 (SegEvalState.init traceD122.regs traceLds122)).log = (traceStores.drop 141).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run122
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts123 : TraceCallFacts traceD123 0xfe5fe0ef#32
    (instruction.JAL (0x1fefe4#21, gprIdx 1)) 0xef#8 0xe0#8 0x5f#8 0xfe#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_fe5fe0ef

theorem run123 {c : Config} (h : TraceHolds traceD123 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD124 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xfe5fe0ef#32 0x1fefe4#21 0xef#8 0xe0#8 0x5f#8 0xfe#8 facts123 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run123
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD124_01 : TraceData :=
  { pc := 0x80003184#64,
    regs := [(1, 0x80004184#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000080#64), (9, 0x87fffe10#64), (10, 0x87fffbb0#64), (11, 0x87fffe10#64), (12, 0x82000080#64), (13, 0x81000000#64), (14, 0x9#64), (15, 0xa#64), (16, 0x8#64), (17, 0x3#64), (18, 0x87fffca8#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 145,
    out := #["\n"], payload := 0x0#4 }

def traceD124_02 : TraceData :=
  { pc := 0x8000318c#64,
    regs := [(1, 0x80004184#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x82000080#64), (9, 0x87fffe10#64), (10, 0x87fffbb0#64), (11, 0x87fffe10#64), (12, 0x82000080#64), (13, 0x81000000#64), (14, 0x9#64), (15, 0xa#64), (16, 0x8#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 145,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg124_00 chain
  [(0x80003164#64, 0x62703#32),
   (0x80003168#64, 0xbc010113#32),
   (0x8000316c#64, 0x42813823#32),
   (0x80003170#64, 0x43213023#32),
   (0x80003174#64, 0x42113c23#32),
   (0x80003178#64, 0x42913423#32),
   (0x8000317c#64, 0xa00793#32),
   (0x80003180#64, 0x60413#32)]

def traceLds124_00 : List (List (BitVec 8)) :=
  [[0x9#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts124_00 : ChainFacts (writeLog snapshotMem traceD124.log)
    (writeLog snapshotMem traceD124.log) traceD124.regs traceLds124_00 traceSeg124_00 := by
  have kind0 : (mkLine 0x80003164#64 0x62703#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80003168#64 0xbc010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000316c#64 0x42813823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80003170#64 0x43213023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80003174#64 0x42113c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003178#64 0x42913423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x8000317c#64 0xa00793#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003180#64 0x60413#32).kind = MKind.addi := by decide
  simp only [traceSeg124_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00060413
    | exact DecodeTable.decode_00062703
    | exact DecodeTable.decode_00a00793
    | exact DecodeTable.decode_42113c23
    | exact DecodeTable.decode_42813823
    | exact DecodeTable.decode_42913423
    | exact DecodeTable.decode_43213023
    | exact DecodeTable.decode_bc010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run124_00 {c : Config} (h : TraceHolds traceD124 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD124_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg124_00 traceLds124_00 (by decide) facts124_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 141 ++ (evalBlocks traceSeg124_00 (SegEvalState.init traceD124.regs traceLds124_00)).log = traceStores.take 145
  have hw : (evalBlocks traceSeg124_00 (SegEvalState.init traceD124.regs traceLds124_00)).log = (traceStores.drop 141).take 4 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run124_00

#derive_case traceSeg124_01 chain
  [(0x80003184#64, 0x58913#32)]
    terminator ⟨0x80003188#64, 0x1ae7e0e3#32, 0xe3#8, 0xe0#8, 0xe7#8, 0x1a#8, .br bop.BLTU false, 15, 14, 0x09a0#13, 0#21, 0#12⟩

def traceLds124_01 : List (List (BitVec 8)) :=
  []

theorem facts124_01 : ChainFacts (writeLog snapshotMem traceD124_01.log)
    (writeLog snapshotMem traceD124_01.log) traceD124_01.regs traceLds124_01 traceSeg124_01 := by
  have kind0 : (mkLine 0x80003184#64 0x58913#32).kind = MKind.addi := by decide
  simp only [traceSeg124_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00058913
    | exact DecodeTable.decode_1ae7e0e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run124_01 {c : Config} (h : TraceHolds traceD124_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD124_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg124_01 traceLds124_01 (by decide) facts124_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 145 ++ (evalBlocks traceSeg124_01 (SegEvalState.init traceD124_01.regs traceLds124_01)).log = traceStores.take 145
  have hw : (evalBlocks traceSeg124_01 (SegEvalState.init traceD124_01.regs traceLds124_01)).log = (traceStores.drop 145).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run124_01

#derive_case traceSeg124_02 chain
  [(0x8000318c#64, 0x66783#32),
   (0x80003190#64, 0x17717#32),
   (0x80003194#64, 0xdc870713#32),
   (0x80003198#64, 0x50493#32),
   (0x8000319c#64, 0x279793#32),
   (0x800031a0#64, 0xe787b3#32),
   (0x800031a4#64, 0x7a783#32),
   (0x800031a8#64, 0xe787b3#32)]
    terminator ⟨0x800031ac#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds124_02 : List (List (BitVec 8)) :=
  [[0x9#8, 0x0#8, 0x0#8, 0x0#8],
   [0x58#8, 0x92#8, 0xfe#8, 0xff#8]]

theorem facts124_02 : ChainFacts (writeLog snapshotMem traceD124_02.log)
    (writeLog snapshotMem traceD124_02.log) traceD124_02.regs traceLds124_02 traceSeg124_02 := by
  have kind0 : (mkLine 0x8000318c#64 0x66783#32).kind = MKind.lwu := by decide
  have kind1 : (mkLine 0x80003190#64 0x17717#32).kind = MKind.auipc := by decide
  have kind2 : (mkLine 0x80003194#64 0xdc870713#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80003198#64 0x50493#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000319c#64 0x279793#32).kind = MKind.slli := by decide
  have kind5 : (mkLine 0x800031a0#64 0xe787b3#32).kind = MKind.add := by decide
  have kind6 : (mkLine 0x800031a4#64 0x7a783#32).kind = MKind.lw := by decide
  have kind7 : (mkLine 0x800031a8#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg124_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00017717
    | exact DecodeTable.decode_00050493
    | exact DecodeTable.decode_00066783
    | exact DecodeTable.decode_00078067
    | exact DecodeTable.decode_0007a783
    | exact DecodeTable.decode_00279793
    | exact DecodeTable.decode_00e787b3
    | exact DecodeTable.decode_dc870713
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run124_02 {c : Config} (h : TraceHolds traceD124_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD125 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg124_02 traceLds124_02 (by decide) facts124_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 145 ++ (evalBlocks traceSeg124_02 (SegEvalState.init traceD124_02.regs traceLds124_02)).log = traceStores.take 145
  have hw : (evalBlocks traceSeg124_02 (SegEvalState.init traceD124_02.regs traceLds124_02)).log = (traceStores.drop 145).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run124_02
theorem run124 {c : Config} (h : TraceHolds traceD124 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD125 c' := by
  obtain ⟨c0, s0, h0⟩ := run124_00 h
  obtain ⟨c1, s1, h1⟩ := run124_01 h0
  obtain ⟨c2, s2, h2⟩ := run124_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run124
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg125 chain
  [(0x800031b0#64, 0x863603#32),
   (0x800031b4#64, 0x6010513#32),
   (0x800031b8#64, 0xd13023#32)]

def traceLds125 : List (List (BitVec 8)) :=
  [[0xa0#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts125 : ChainFacts (writeLog snapshotMem traceD125.log)
    (writeLog snapshotMem traceD125.log) traceD125.regs traceLds125 traceSeg125 := by
  have kind0 : (mkLine 0x800031b0#64 0x863603#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x800031b4#64 0x6010513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x800031b8#64 0xd13023#32).kind = MKind.sd := by decide
  simp only [traceSeg125, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00863603
    | exact DecodeTable.decode_00d13023
    | exact DecodeTable.decode_06010513
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run125 {c : Config} (h : TraceHolds traceD125 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD126 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg125 traceLds125 (by decide) facts125 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 145 ++ (evalBlocks traceSeg125 (SegEvalState.init traceD125.regs traceLds125)).log = traceStores.take 146
  have hw : (evalBlocks traceSeg125 (SegEvalState.init traceD125.regs traceLds125)).log = (traceStores.drop 145).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run125
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts126 : TraceCallFacts traceD126 0xfa9ff0ef#32
    (instruction.JAL (0x1fffa8#21, gprIdx 1)) 0xef#8 0xf0#8 0x9f#8 0xfa#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_fa9ff0ef

theorem run126 {c : Config} (h : TraceHolds traceD126 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD127 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xfa9ff0ef#32 0x1fffa8#21 0xef#8 0xf0#8 0x9f#8 0xfa#8 facts126 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run126
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD127_01 : TraceData :=
  { pc := 0x80003184#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff320#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x820000a0#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x87fffe10#64), (12, 0x820000a0#64), (13, 0x81000000#64), (14, 0x4#64), (15, 0xa#64), (16, 0x8#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 150,
    out := #["\n"], payload := 0x0#4 }

def traceD127_02 : TraceData :=
  { pc := 0x8000318c#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff320#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x820000a0#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x87fffe10#64), (12, 0x820000a0#64), (13, 0x81000000#64), (14, 0x4#64), (15, 0xa#64), (16, 0x8#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 150,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg127_00 chain
  [(0x80003164#64, 0x62703#32),
   (0x80003168#64, 0xbc010113#32),
   (0x8000316c#64, 0x42813823#32),
   (0x80003170#64, 0x43213023#32),
   (0x80003174#64, 0x42113c23#32),
   (0x80003178#64, 0x42913423#32),
   (0x8000317c#64, 0xa00793#32),
   (0x80003180#64, 0x60413#32)]

def traceLds127_00 : List (List (BitVec 8)) :=
  [[0x4#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts127_00 : ChainFacts (writeLog snapshotMem traceD127.log)
    (writeLog snapshotMem traceD127.log) traceD127.regs traceLds127_00 traceSeg127_00 := by
  have kind0 : (mkLine 0x80003164#64 0x62703#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x80003168#64 0xbc010113#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000316c#64 0x42813823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80003170#64 0x43213023#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80003174#64 0x42113c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003178#64 0x42913423#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x8000317c#64 0xa00793#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80003180#64 0x60413#32).kind = MKind.addi := by decide
  simp only [traceSeg127_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00060413
    | exact DecodeTable.decode_00062703
    | exact DecodeTable.decode_00a00793
    | exact DecodeTable.decode_42113c23
    | exact DecodeTable.decode_42813823
    | exact DecodeTable.decode_42913423
    | exact DecodeTable.decode_43213023
    | exact DecodeTable.decode_bc010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run127_00 {c : Config} (h : TraceHolds traceD127 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD127_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg127_00 traceLds127_00 (by decide) facts127_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 146 ++ (evalBlocks traceSeg127_00 (SegEvalState.init traceD127.regs traceLds127_00)).log = traceStores.take 150
  have hw : (evalBlocks traceSeg127_00 (SegEvalState.init traceD127.regs traceLds127_00)).log = (traceStores.drop 146).take 4 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run127_00

#derive_case traceSeg127_01 chain
  [(0x80003184#64, 0x58913#32)]
    terminator ⟨0x80003188#64, 0x1ae7e0e3#32, 0xe3#8, 0xe0#8, 0xe7#8, 0x1a#8, .br bop.BLTU false, 15, 14, 0x09a0#13, 0#21, 0#12⟩

def traceLds127_01 : List (List (BitVec 8)) :=
  []

theorem facts127_01 : ChainFacts (writeLog snapshotMem traceD127_01.log)
    (writeLog snapshotMem traceD127_01.log) traceD127_01.regs traceLds127_01 traceSeg127_01 := by
  have kind0 : (mkLine 0x80003184#64 0x58913#32).kind = MKind.addi := by decide
  simp only [traceSeg127_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00058913
    | exact DecodeTable.decode_1ae7e0e3
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run127_01 {c : Config} (h : TraceHolds traceD127_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD127_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg127_01 traceLds127_01 (by decide) facts127_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 150 ++ (evalBlocks traceSeg127_01 (SegEvalState.init traceD127_01.regs traceLds127_01)).log = traceStores.take 150
  have hw : (evalBlocks traceSeg127_01 (SegEvalState.init traceD127_01.regs traceLds127_01)).log = (traceStores.drop 150).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run127_01

#derive_case traceSeg127_02 chain
  [(0x8000318c#64, 0x66783#32),
   (0x80003190#64, 0x17717#32),
   (0x80003194#64, 0xdc870713#32),
   (0x80003198#64, 0x50493#32),
   (0x8000319c#64, 0x279793#32),
   (0x800031a0#64, 0xe787b3#32),
   (0x800031a4#64, 0x7a783#32),
   (0x800031a8#64, 0xe787b3#32)]
    terminator ⟨0x800031ac#64, 0x00078067#32, 0x67#8, 0x80#8, 0x07#8, 0x00#8, .jr, 15, 0, 0#13, 0#21, 0x000#12⟩

def traceLds127_02 : List (List (BitVec 8)) :=
  [[0x4#8, 0x0#8, 0x0#8, 0x0#8],
   [0xdc#8, 0x94#8, 0xfe#8, 0xff#8]]

theorem facts127_02 : ChainFacts (writeLog snapshotMem traceD127_02.log)
    (writeLog snapshotMem traceD127_02.log) traceD127_02.regs traceLds127_02 traceSeg127_02 := by
  have kind0 : (mkLine 0x8000318c#64 0x66783#32).kind = MKind.lwu := by decide
  have kind1 : (mkLine 0x80003190#64 0x17717#32).kind = MKind.auipc := by decide
  have kind2 : (mkLine 0x80003194#64 0xdc870713#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80003198#64 0x50493#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x8000319c#64 0x279793#32).kind = MKind.slli := by decide
  have kind5 : (mkLine 0x800031a0#64 0xe787b3#32).kind = MKind.add := by decide
  have kind6 : (mkLine 0x800031a4#64 0x7a783#32).kind = MKind.lw := by decide
  have kind7 : (mkLine 0x800031a8#64 0xe787b3#32).kind = MKind.add := by decide
  simp only [traceSeg127_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00017717
    | exact DecodeTable.decode_00050493
    | exact DecodeTable.decode_00066783
    | exact DecodeTable.decode_00078067
    | exact DecodeTable.decode_0007a783
    | exact DecodeTable.decode_00279793
    | exact DecodeTable.decode_00e787b3
    | exact DecodeTable.decode_dc870713
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run127_02 {c : Config} (h : TraceHolds traceD127_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD128 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg127_02 traceLds127_02 (by decide) facts127_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 150 ++ (evalBlocks traceSeg127_02 (SegEvalState.init traceD127_02.regs traceLds127_02)).log = traceStores.take 150
  have hw : (evalBlocks traceSeg127_02 (SegEvalState.init traceD127_02.regs traceLds127_02)).log = (traceStores.drop 150).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run127_02
theorem run127 {c : Config} (h : TraceHolds traceD127 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD128 c' := by
  obtain ⟨c0, s0, h0⟩ := run127_00 h
  obtain ⟨c1, s1, h1⟩ := run127_01 h0
  obtain ⟨c2, s2, h2⟩ := run127_02 h1
  exact ⟨c2, ((s0).trans s1).trans s2, h2⟩

#print axioms run127
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg128 chain
  [(0x80003434#64, 0x863583#32),
   (0x80003438#64, 0x68513#32),
   (0x8000343c#64, 0xf010613#32)]

def traceLds128 : List (List (BitVec 8)) :=
  [[0x10#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts128 : ChainFacts (writeLog snapshotMem traceD128.log)
    (writeLog snapshotMem traceD128.log) traceD128.regs traceLds128 traceSeg128 := by
  have kind0 : (mkLine 0x80003434#64 0x863583#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80003438#64 0x68513#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x8000343c#64 0xf010613#32).kind = MKind.addi := by decide
  simp only [traceSeg128, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00068513
    | exact DecodeTable.decode_00863583
    | exact DecodeTable.decode_0f010613
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run128 {c : Config} (h : TraceHolds traceD128 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD129 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg128 traceLds128 (by decide) facts128 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 150 ++ (evalBlocks traceSeg128 (SegEvalState.init traceD128.regs traceLds128)).log = traceStores.take 150
  have hw : (evalBlocks traceSeg128 (SegEvalState.init traceD128.regs traceLds128)).log = (traceStores.drop 150).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run128
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts129 : TraceCallFacts traceD129 0xfd0ff0ef#32
    (instruction.JAL (0x1ff7d0#21, gprIdx 1)) 0xef#8 0xf0#8 0xf#8 0xfd#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_fd0ff0ef

theorem run129 {c : Config} (h : TraceHolds traceD129 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD130 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0xfd0ff0ef#32 0x1ff7d0#21 0xef#8 0xf0#8 0xf#8 0xfd#8 facts129 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run129
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD130_01 : TraceData :=
  { pc := 0x80002c14#64,
    regs := [(1, 0x80003444#64), (2, 0x87fff320#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x820000a0#64), (9, 0x87fff7c0#64), (10, 0x81000000#64), (11, 0x81000210#64), (12, 0x87fff410#64), (13, 0x81000000#64), (14, 0x80019f58#64), (15, 0x80003434#64), (16, 0x8#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 150,
    out := #["\n"], payload := 0x0#4 }

def traceD130_02 : TraceData :=
  { pc := 0x80002c34#64,
    regs := [(1, 0x80003444#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x820000a0#64), (9, 0x87fff7c0#64), (10, 0x81000000#64), (11, 0x81000210#64), (12, 0x87fff410#64), (13, 0x81000000#64), (14, 0x80019f58#64), (15, 0x80003434#64), (16, 0x8#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD130_03 : TraceData :=
  { pc := 0x80002c48#64,
    regs := [(1, 0x80003444#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x820000a0#64), (9, 0x87fff7c0#64), (10, 0x81000000#64), (11, 0x81000210#64), (12, 0x87fff410#64), (13, 0x81000000#64), (14, 0x80019f58#64), (15, 0x80003434#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD130_04 : TraceData :=
  { pc := 0x80002c60#64,
    regs := [(1, 0x80003444#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000000#64), (11, 0x81000210#64), (12, 0x87fff410#64), (13, 0x81000000#64), (14, 0x80019f58#64), (15, 0x80003434#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg130_00 chain
  []
    terminator ⟨0x80002c10#64, 0x0c050263#32, 0x63#8, 0x02#8, 0x05#8, 0x0c#8, .br bop.BEQ false, 10, 0, 0x00c4#13, 0#21, 0#12⟩

def traceLds130_00 : List (List (BitVec 8)) :=
  []

theorem facts130_00 : ChainFacts (writeLog snapshotMem traceD130.log)
    (writeLog snapshotMem traceD130.log) traceD130.regs traceLds130_00 traceSeg130_00 := by
  simp only [traceSeg130_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0c050263
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run130_00 {c : Config} (h : TraceHolds traceD130 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD130_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg130_00 traceLds130_00 (by decide) facts130_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 150 ++ (evalBlocks traceSeg130_00 (SegEvalState.init traceD130.regs traceLds130_00)).log = traceStores.take 150
  have hw : (evalBlocks traceSeg130_00 (SegEvalState.init traceD130.regs traceLds130_00)).log = (traceStores.drop 150).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run130_00

#derive_case traceSeg130_01 chain
  [(0x80002c14#64, 0xfc010113#32),
   (0x80002c18#64, 0x1313c23#32),
   (0x80002c1c#64, 0x1413823#32),
   (0x80002c20#64, 0x1513423#32),
   (0x80002c24#64, 0x2113c23#32),
   (0x80002c28#64, 0x2813823#32),
   (0x80002c2c#64, 0x2913423#32),
   (0x80002c30#64, 0x3213023#32)]

def traceLds130_01 : List (List (BitVec 8)) :=
  []

theorem facts130_01 : ChainFacts (writeLog snapshotMem traceD130_01.log)
    (writeLog snapshotMem traceD130_01.log) traceD130_01.regs traceLds130_01 traceSeg130_01 := by
  have kind0 : (mkLine 0x80002c14#64 0xfc010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002c18#64 0x1313c23#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80002c1c#64 0x1413823#32).kind = MKind.sd := by decide
  have kind3 : (mkLine 0x80002c20#64 0x1513423#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80002c24#64 0x2113c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80002c28#64 0x2813823#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80002c2c#64 0x2913423#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x80002c30#64 0x3213023#32).kind = MKind.sd := by decide
  simp only [traceSeg130_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01313c23
    | exact DecodeTable.decode_01413823
    | exact DecodeTable.decode_01513423
    | exact DecodeTable.decode_02113c23
    | exact DecodeTable.decode_02813823
    | exact DecodeTable.decode_02913423
    | exact DecodeTable.decode_03213023
    | exact DecodeTable.decode_fc010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run130_01 {c : Config} (h : TraceHolds traceD130_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD130_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg130_01 traceLds130_01 (by decide) facts130_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 150 ++ (evalBlocks traceSeg130_01 (SegEvalState.init traceD130_01.regs traceLds130_01)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg130_01 (SegEvalState.init traceD130_01.regs traceLds130_01)).log = (traceStores.drop 150).take 7 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run130_01

#derive_case traceSeg130_02 chain
  [(0x80002c34#64, 0x50a13#32),
   (0x80002c38#64, 0x58993#32),
   (0x80002c3c#64, 0x60a93#32),
   (0x80002c40#64, 0xa2903#32)]
    terminator ⟨0x80002c44#64, 0x09205063#32, 0x63#8, 0x50#8, 0x20#8, 0x09#8, .br bop.BGE false, 0, 18, 0x0080#13, 0#21, 0#12⟩

def traceLds130_02 : List (List (BitVec 8)) :=
  [[0x3#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts130_02 : ChainFacts (writeLog snapshotMem traceD130_02.log)
    (writeLog snapshotMem traceD130_02.log) traceD130_02.regs traceLds130_02 traceSeg130_02 := by
  have kind0 : (mkLine 0x80002c34#64 0x50a13#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002c38#64 0x58993#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002c3c#64 0x60a93#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80002c40#64 0xa2903#32).kind = MKind.lw := by decide
  simp only [traceSeg130_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00050a13
    | exact DecodeTable.decode_00058993
    | exact DecodeTable.decode_00060a93
    | exact DecodeTable.decode_000a2903
    | exact DecodeTable.decode_09205063
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run130_02 {c : Config} (h : TraceHolds traceD130_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD130_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg130_02 traceLds130_02 (by decide) facts130_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg130_02 (SegEvalState.init traceD130_02.regs traceLds130_02)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg130_02 (SegEvalState.init traceD130_02.regs traceLds130_02)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run130_02

#derive_case traceSeg130_03 chain
  [(0x80002c48#64, 0x8a3483#32),
   (0x80002c4c#64, 0x413#32)]
    terminator ⟨0x80002c50#64, 0x0100006f#32, 0x6f#8, 0x00#8, 0x00#8, 0x01#8, .j, 0, 0, 0#13, 0x000010#21, 0#12⟩

def traceLds130_03 : List (List (BitVec 8)) :=
  [[0x40#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts130_03 : ChainFacts (writeLog snapshotMem traceD130_03.log)
    (writeLog snapshotMem traceD130_03.log) traceD130_03.regs traceLds130_03 traceSeg130_03 := by
  have kind0 : (mkLine 0x80002c48#64 0x8a3483#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002c4c#64 0x413#32).kind = MKind.addi := by decide
  simp only [traceSeg130_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000413
    | exact DecodeTable.decode_008a3483
    | exact DecodeTable.decode_0100006f
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run130_03 {c : Config} (h : TraceHolds traceD130_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD130_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg130_03 traceLds130_03 (by decide) facts130_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg130_03 (SegEvalState.init traceD130_03.regs traceLds130_03)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg130_03 (SegEvalState.init traceD130_03.regs traceLds130_03)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run130_03

#derive_case traceSeg130_04 chain
  [(0x80002c60#64, 0x4b503#32),
   (0x80002c64#64, 0x98593#32)]

def traceLds130_04 : List (List (BitVec 8)) :=
  [[0x0#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts130_04 : ChainFacts (writeLog snapshotMem traceD130_04.log)
    (writeLog snapshotMem traceD130_04.log) traceD130_04.regs traceLds130_04 traceSeg130_04 := by
  have kind0 : (mkLine 0x80002c60#64 0x4b503#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002c64#64 0x98593#32).kind = MKind.addi := by decide
  simp only [traceSeg130_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0004b503
    | exact DecodeTable.decode_00098593
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run130_04 {c : Config} (h : TraceHolds traceD130_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD131 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg130_04 traceLds130_04 (by decide) facts130_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg130_04 (SegEvalState.init traceD130_04.regs traceLds130_04)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg130_04 (SegEvalState.init traceD130_04.regs traceLds130_04)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run130_04
theorem run130 {c : Config} (h : TraceHolds traceD130 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD131 c' := by
  obtain ⟨c0, s0, h0⟩ := run130_00 h
  obtain ⟨c1, s1, h1⟩ := run130_01 h0
  obtain ⟨c2, s2, h2⟩ := run130_02 h1
  obtain ⟨c3, s3, h3⟩ := run130_03 h2
  obtain ⟨c4, s4, h4⟩ := run130_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run130
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts131 : TraceCallFacts traceD131 0x238040ef#32
    (instruction.JAL (0x4238#21, gprIdx 1)) 0xef#8 0x40#8 0x80#8 0x23#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_238040ef

theorem run131 {c : Config} (h : TraceHolds traceD131 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x238040ef#32 0x4238#21 0xef#8 0x40#8 0x80#8 0x23#8 facts131 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run131
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD132_01 : TraceData :=
  { pc := 0x80006eb0#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x1#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000200#64), (11, 0x81000210#64), (12, 0x87fff410#64), (13, 0x81000000#64), (14, 0x0#64), (15, 0x80003434#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_02 : TraceData :=
  { pc := 0x80006fac#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000200#64), (11, 0x81000210#64), (12, 0x746e697270#64), (13, 0x6e6c746e697270#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_03 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000200#64), (11, 0x81000210#64), (12, 0x746e697270#64), (13, 0x6e6c746e697270#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_04 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000201#64), (11, 0x81000211#64), (12, 0x70#64), (13, 0x70#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_05 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000201#64), (11, 0x81000211#64), (12, 0x70#64), (13, 0x70#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_06 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000202#64), (11, 0x81000212#64), (12, 0x72#64), (13, 0x72#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_07 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000202#64), (11, 0x81000212#64), (12, 0x72#64), (13, 0x72#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_08 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000203#64), (11, 0x81000213#64), (12, 0x69#64), (13, 0x69#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_09 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000203#64), (11, 0x81000213#64), (12, 0x69#64), (13, 0x69#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_10 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000204#64), (11, 0x81000214#64), (12, 0x6e#64), (13, 0x6e#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_11 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000204#64), (11, 0x81000214#64), (12, 0x6e#64), (13, 0x6e#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_12 : TraceData :=
  { pc := 0x80006f98#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000205#64), (11, 0x81000215#64), (12, 0x74#64), (13, 0x74#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_13 : TraceData :=
  { pc := 0x80006f84#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000205#64), (11, 0x81000215#64), (12, 0x74#64), (13, 0x74#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD132_14 : TraceData :=
  { pc := 0x80006f9c#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7f7f7fffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x0#64), (9, 0x81000040#64), (10, 0x81000206#64), (11, 0x81000216#64), (12, 0x0#64), (13, 0x6c#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg132_00 chain
  [(0x80006ea0#64, 0xb56733#32),
   (0x80006ea4#64, 0xfff00393#32),
   (0x80006ea8#64, 0x777713#32)]
    terminator ⟨0x80006eac#64, 0x0c071c63#32, 0x63#8, 0x1c#8, 0x07#8, 0x0c#8, .br bop.BNE false, 14, 0, 0x00d8#13, 0#21, 0#12⟩

def traceLds132_00 : List (List (BitVec 8)) :=
  []

theorem facts132_00 : ChainFacts (writeLog snapshotMem traceD132.log)
    (writeLog snapshotMem traceD132.log) traceD132.regs traceLds132_00 traceSeg132_00 := by
  have kind0 : (mkLine 0x80006ea0#64 0xb56733#32).kind = MKind.or := by decide
  have kind1 : (mkLine 0x80006ea4#64 0xfff00393#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80006ea8#64 0x777713#32).kind = MKind.andi := by decide
  simp only [traceSeg132_00, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run132_00 {c : Config} (h : TraceHolds traceD132 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_00 traceLds132_00 (by decide) facts132_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_00 (SegEvalState.init traceD132.regs traceLds132_00)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_00 (SegEvalState.init traceD132.regs traceLds132_00)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_00

#derive_case traceSeg132_01 chain
  [(0x80006eb0#64, 0x14797#32),
   (0x80006eb4#64, 0xdd07b783#32),
   (0x80006eb8#64, 0x53603#32),
   (0x80006ebc#64, 0x5b683#32),
   (0x80006ec0#64, 0xf672b3#32),
   (0x80006ec4#64, 0xf66333#32),
   (0x80006ec8#64, 0xf282b3#32),
   (0x80006ecc#64, 0x62e2b3#32)]
    terminator ⟨0x80006ed0#64, 0x0c729e63#32, 0x63#8, 0x9e#8, 0x72#8, 0x0c#8, .br bop.BNE true, 5, 7, 0x00dc#13, 0#21, 0#12⟩

def traceLds132_01 : List (List (BitVec 8)) :=
  [[0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8],
   [0x70#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8, 0x0#8, 0x0#8, 0x0#8],
   [0x70#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8, 0x6c#8, 0x6e#8, 0x0#8]]

theorem facts132_01 : ChainFacts (writeLog snapshotMem traceD132_01.log)
    (writeLog snapshotMem traceD132_01.log) traceD132_01.regs traceLds132_01 traceSeg132_01 := by
  have kind0 : (mkLine 0x80006eb0#64 0x14797#32).kind = MKind.auipc := by decide
  have kind1 : (mkLine 0x80006eb4#64 0xdd07b783#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80006eb8#64 0x53603#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80006ebc#64 0x5b683#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80006ec0#64 0xf672b3#32).kind = MKind.and := by decide
  have kind5 : (mkLine 0x80006ec4#64 0xf66333#32).kind = MKind.or := by decide
  have kind6 : (mkLine 0x80006ec8#64 0xf282b3#32).kind = MKind.add := by decide
  have kind7 : (mkLine 0x80006ecc#64 0x62e2b3#32).kind = MKind.or := by decide
  simp only [traceSeg132_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00014797
    | exact DecodeTable.decode_00053603
    | exact DecodeTable.decode_0005b683
    | exact DecodeTable.decode_0062e2b3
    | exact DecodeTable.decode_00f282b3
    | exact DecodeTable.decode_00f66333
    | exact DecodeTable.decode_00f672b3
    | exact DecodeTable.decode_0c729e63
    | exact DecodeTable.decode_dd07b783
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run132_01 {c : Config} (h : TraceHolds traceD132_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_01 traceLds132_01 (by decide) facts132_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_01 (SegEvalState.init traceD132_01.regs traceLds132_01)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_01 (SegEvalState.init traceD132_01.regs traceLds132_01)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_01

#derive_case traceSeg132_02 chain
  []
    terminator ⟨0x80006fac#64, 0xfcd61ce3#32, 0xe3#8, 0x1c#8, 0xd6#8, 0xfc#8, .br bop.BNE true, 12, 13, 0x1fd8#13, 0#21, 0#12⟩

def traceLds132_02 : List (List (BitVec 8)) :=
  []

theorem facts132_02 : ChainFacts (writeLog snapshotMem traceD132_02.log)
    (writeLog snapshotMem traceD132_02.log) traceD132_02.regs traceLds132_02 traceSeg132_02 := by
  simp only [traceSeg132_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fcd61ce3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run132_02 {c : Config} (h : TraceHolds traceD132_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_02 traceLds132_02 (by decide) facts132_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_02 (SegEvalState.init traceD132_02.regs traceLds132_02)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_02 (SegEvalState.init traceD132_02.regs traceLds132_02)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_02

#derive_case traceSeg132_03 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds132_03 : List (List (BitVec 8)) :=
  [[0x70#8],
   [0x70#8]]

theorem facts132_03 : ChainFacts (writeLog snapshotMem traceD132_03.log)
    (writeLog snapshotMem traceD132_03.log) traceD132_03.regs traceLds132_03 traceSeg132_03 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg132_03, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run132_03 {c : Config} (h : TraceHolds traceD132_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_03 traceLds132_03 (by decide) facts132_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_03 (SegEvalState.init traceD132_03.regs traceLds132_03)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_03 (SegEvalState.init traceD132_03.regs traceLds132_03)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_03

#derive_case traceSeg132_04 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds132_04 : List (List (BitVec 8)) :=
  []

theorem facts132_04 : ChainFacts (writeLog snapshotMem traceD132_04.log)
    (writeLog snapshotMem traceD132_04.log) traceD132_04.regs traceLds132_04 traceSeg132_04 := by
  simp only [traceSeg132_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run132_04 {c : Config} (h : TraceHolds traceD132_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_05 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_04 traceLds132_04 (by decide) facts132_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_04 (SegEvalState.init traceD132_04.regs traceLds132_04)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_04 (SegEvalState.init traceD132_04.regs traceLds132_04)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_04

#derive_case traceSeg132_05 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds132_05 : List (List (BitVec 8)) :=
  [[0x72#8],
   [0x72#8]]

theorem facts132_05 : ChainFacts (writeLog snapshotMem traceD132_05.log)
    (writeLog snapshotMem traceD132_05.log) traceD132_05.regs traceLds132_05 traceSeg132_05 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg132_05, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run132_05 {c : Config} (h : TraceHolds traceD132_05 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_06 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_05 traceLds132_05 (by decide) facts132_05 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_05 (SegEvalState.init traceD132_05.regs traceLds132_05)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_05 (SegEvalState.init traceD132_05.regs traceLds132_05)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_05

#derive_case traceSeg132_06 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds132_06 : List (List (BitVec 8)) :=
  []

theorem facts132_06 : ChainFacts (writeLog snapshotMem traceD132_06.log)
    (writeLog snapshotMem traceD132_06.log) traceD132_06.regs traceLds132_06 traceSeg132_06 := by
  simp only [traceSeg132_06, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run132_06 {c : Config} (h : TraceHolds traceD132_06 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_07 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_06 traceLds132_06 (by decide) facts132_06 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_06 (SegEvalState.init traceD132_06.regs traceLds132_06)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_06 (SegEvalState.init traceD132_06.regs traceLds132_06)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_06

#derive_case traceSeg132_07 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds132_07 : List (List (BitVec 8)) :=
  [[0x69#8],
   [0x69#8]]

theorem facts132_07 : ChainFacts (writeLog snapshotMem traceD132_07.log)
    (writeLog snapshotMem traceD132_07.log) traceD132_07.regs traceLds132_07 traceSeg132_07 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg132_07, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run132_07 {c : Config} (h : TraceHolds traceD132_07 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_08 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_07 traceLds132_07 (by decide) facts132_07 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_07 (SegEvalState.init traceD132_07.regs traceLds132_07)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_07 (SegEvalState.init traceD132_07.regs traceLds132_07)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_07

#derive_case traceSeg132_08 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds132_08 : List (List (BitVec 8)) :=
  []

theorem facts132_08 : ChainFacts (writeLog snapshotMem traceD132_08.log)
    (writeLog snapshotMem traceD132_08.log) traceD132_08.regs traceLds132_08 traceSeg132_08 := by
  simp only [traceSeg132_08, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run132_08 {c : Config} (h : TraceHolds traceD132_08 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_09 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_08 traceLds132_08 (by decide) facts132_08 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_08 (SegEvalState.init traceD132_08.regs traceLds132_08)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_08 (SegEvalState.init traceD132_08.regs traceLds132_08)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_08

#derive_case traceSeg132_09 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds132_09 : List (List (BitVec 8)) :=
  [[0x6e#8],
   [0x6e#8]]

theorem facts132_09 : ChainFacts (writeLog snapshotMem traceD132_09.log)
    (writeLog snapshotMem traceD132_09.log) traceD132_09.regs traceLds132_09 traceSeg132_09 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg132_09, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run132_09 {c : Config} (h : TraceHolds traceD132_09 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_10 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_09 traceLds132_09 (by decide) facts132_09 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_09 (SegEvalState.init traceD132_09.regs traceLds132_09)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_09 (SegEvalState.init traceD132_09.regs traceLds132_09)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_09

#derive_case traceSeg132_10 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds132_10 : List (List (BitVec 8)) :=
  []

theorem facts132_10 : ChainFacts (writeLog snapshotMem traceD132_10.log)
    (writeLog snapshotMem traceD132_10.log) traceD132_10.regs traceLds132_10 traceSeg132_10 := by
  simp only [traceSeg132_10, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run132_10 {c : Config} (h : TraceHolds traceD132_10 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_11 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_10 traceLds132_10 (by decide) facts132_10 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_10 (SegEvalState.init traceD132_10.regs traceLds132_10)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_10 (SegEvalState.init traceD132_10.regs traceLds132_10)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_10

#derive_case traceSeg132_11 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE false, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds132_11 : List (List (BitVec 8)) :=
  [[0x74#8],
   [0x74#8]]

theorem facts132_11 : ChainFacts (writeLog snapshotMem traceD132_11.log)
    (writeLog snapshotMem traceD132_11.log) traceD132_11.regs traceLds132_11 traceSeg132_11 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg132_11, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run132_11 {c : Config} (h : TraceHolds traceD132_11 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_12 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_11 traceLds132_11 (by decide) facts132_11 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_11 (SegEvalState.init traceD132_11.regs traceLds132_11)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_11 (SegEvalState.init traceD132_11.regs traceLds132_11)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_11

#derive_case traceSeg132_12 chain
  []
    terminator ⟨0x80006f98#64, 0xfe0616e3#32, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8, .br bop.BNE true, 12, 0, 0x1fec#13, 0#21, 0#12⟩

def traceLds132_12 : List (List (BitVec 8)) :=
  []

theorem facts132_12 : ChainFacts (writeLog snapshotMem traceD132_12.log)
    (writeLog snapshotMem traceD132_12.log) traceD132_12.regs traceLds132_12 traceSeg132_12 := by
  simp only [traceSeg132_12, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0616e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run132_12 {c : Config} (h : TraceHolds traceD132_12 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_13 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_12 traceLds132_12 (by decide) facts132_12 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_12 (SegEvalState.init traceD132_12.regs traceLds132_12)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_12 (SegEvalState.init traceD132_12.regs traceLds132_12)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_12

#derive_case traceSeg132_13 chain
  [(0x80006f84#64, 0x54603#32),
   (0x80006f88#64, 0x5c683#32),
   (0x80006f8c#64, 0x150513#32),
   (0x80006f90#64, 0x158593#32)]
    terminator ⟨0x80006f94#64, 0x00d61463#32, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, .br bop.BNE true, 12, 13, 0x0008#13, 0#21, 0#12⟩

def traceLds132_13 : List (List (BitVec 8)) :=
  [[0x0#8],
   [0x6c#8]]

theorem facts132_13 : ChainFacts (writeLog snapshotMem traceD132_13.log)
    (writeLog snapshotMem traceD132_13.log) traceD132_13.regs traceLds132_13 traceSeg132_13 := by
  have kind0 : (mkLine 0x80006f84#64 0x54603#32).kind = MKind.lbu := by decide
  have kind1 : (mkLine 0x80006f88#64 0x5c683#32).kind = MKind.lbu := by decide
  have kind2 : (mkLine 0x80006f8c#64 0x150513#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80006f90#64 0x158593#32).kind = MKind.addi := by decide
  simp only [traceSeg132_13, ChainFacts, BBlockFacts, ProgFactsM,
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

theorem run132_13 {c : Config} (h : TraceHolds traceD132_13 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD132_14 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_13 traceLds132_13 (by decide) facts132_13 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_13 (SegEvalState.init traceD132_13.regs traceLds132_13)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_13 (SegEvalState.init traceD132_13.regs traceLds132_13)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_13

#derive_case traceSeg132_14 chain
  [(0x80006f9c#64, 0x40d60533#32)]
    terminator ⟨0x80006fa0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds132_14 : List (List (BitVec 8)) :=
  []

theorem facts132_14 : ChainFacts (writeLog snapshotMem traceD132_14.log)
    (writeLog snapshotMem traceD132_14.log) traceD132_14.regs traceLds132_14 traceSeg132_14 := by
  have kind0 : (mkLine 0x80006f9c#64 0x40d60533#32).kind = MKind.sub := by decide
  simp only [traceSeg132_14, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_40d60533
    | (simp only [kind0, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run132_14 {c : Config} (h : TraceHolds traceD132_14 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD133 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg132_14 traceLds132_14 (by decide) facts132_14 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg132_14 (SegEvalState.init traceD132_14.regs traceLds132_14)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg132_14 (SegEvalState.init traceD132_14.regs traceLds132_14)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run132_14
theorem run132 {c : Config} (h : TraceHolds traceD132 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD133 c' := by
  obtain ⟨c0, s0, h0⟩ := run132_00 h
  obtain ⟨c1, s1, h1⟩ := run132_01 h0
  obtain ⟨c2, s2, h2⟩ := run132_02 h1
  obtain ⟨c3, s3, h3⟩ := run132_03 h2
  obtain ⟨c4, s4, h4⟩ := run132_04 h3
  obtain ⟨c5, s5, h5⟩ := run132_05 h4
  obtain ⟨c6, s6, h6⟩ := run132_06 h5
  obtain ⟨c7, s7, h7⟩ := run132_07 h6
  obtain ⟨c8, s8, h8⟩ := run132_08 h7
  obtain ⟨c9, s9, h9⟩ := run132_09 h8
  obtain ⟨c10, s10, h10⟩ := run132_10 h9
  obtain ⟨c11, s11, h11⟩ := run132_11 h10
  obtain ⟨c12, s12, h12⟩ := run132_12 h11
  obtain ⟨c13, s13, h13⟩ := run132_13 h12
  obtain ⟨c14, s14, h14⟩ := run132_14 h13
  exact ⟨c14, ((((((((((((((s0).trans s1).trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8).trans s9).trans s10).trans s11).trans s12).trans s13).trans s14, h14⟩

#print axioms run132
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg133 chain
  []
    terminator ⟨0x80002c6c#64, 0xfe0514e3#32, 0xe3#8, 0x14#8, 0x05#8, 0xfe#8, .br bop.BNE true, 10, 0, 0x1fe8#13, 0#21, 0#12⟩ ;;
  [(0x80002c54#64, 0x140413#32),
   (0x80002c58#64, 0x848493#32)]
    terminator ⟨0x80002c5c#64, 0x07240463#32, 0x63#8, 0x04#8, 0x24#8, 0x07#8, .br bop.BEQ false, 8, 18, 0x0068#13, 0#21, 0#12⟩ ;;
  [(0x80002c60#64, 0x4b503#32),
   (0x80002c64#64, 0x98593#32)]

def traceLds133 : List (List (BitVec 8)) :=
  [[0x10#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts133 : ChainFacts (writeLog snapshotMem traceD133.log)
    (writeLog snapshotMem traceD133.log) traceD133.regs traceLds133 traceSeg133 := by
  have kind0 : (mkLine 0x80002c54#64 0x140413#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002c58#64 0x848493#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80002c60#64 0x4b503#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80002c64#64 0x98593#32).kind = MKind.addi := by decide
  simp only [traceSeg133, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0004b503
    | exact DecodeTable.decode_00098593
    | exact DecodeTable.decode_00140413
    | exact DecodeTable.decode_00848493
    | exact DecodeTable.decode_07240463
    | exact DecodeTable.decode_fe0514e3
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run133 {c : Config} (h : TraceHolds traceD133 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD134 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg133 traceLds133 (by decide) facts133 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg133 (SegEvalState.init traceD133.regs traceLds133)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg133 (SegEvalState.init traceD133.regs traceLds133)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run133
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts134 : TraceCallFacts traceD134 0x238040ef#32
    (instruction.JAL (0x4238#21, gprIdx 1)) 0xef#8 0x40#8 0x80#8 0x23#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_238040ef

theorem run134 {c : Config} (h : TraceHolds traceD134 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD135 c' := by
  obtain ⟨c', hs, hp⟩ := h.jal 0x238040ef#32 0x4238#21 0xef#8 0x40#8 0x80#8 0x23#8 facts134 (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run134
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg135 chain
  [(0x80006ea0#64, 0xb56733#32),
   (0x80006ea4#64, 0xfff00393#32),
   (0x80006ea8#64, 0x777713#32)]
    terminator ⟨0x80006eac#64, 0x0c071c63#32, 0x63#8, 0x1c#8, 0x07#8, 0x0c#8, .br bop.BNE false, 14, 0, 0x00d8#13, 0#21, 0#12⟩ ;;
  [(0x80006eb0#64, 0x14797#32),
   (0x80006eb4#64, 0xdd07b783#32),
   (0x80006eb8#64, 0x53603#32),
   (0x80006ebc#64, 0x5b683#32),
   (0x80006ec0#64, 0xf672b3#32),
   (0x80006ec4#64, 0xf66333#32),
   (0x80006ec8#64, 0xf282b3#32),
   (0x80006ecc#64, 0x62e2b3#32)]
    terminator ⟨0x80006ed0#64, 0x0c729e63#32, 0x63#8, 0x9e#8, 0x72#8, 0x0c#8, .br bop.BNE true, 5, 7, 0x00dc#13, 0#21, 0#12⟩ ;;
  []
    terminator ⟨0x80006fac#64, 0xfcd61ce3#32, 0xe3#8, 0x1c#8, 0xd6#8, 0xfc#8, .br bop.BNE false, 12, 13, 0x1fd8#13, 0#21, 0#12⟩ ;;
  [(0x80006fb0#64, 0x513#32)]
    terminator ⟨0x80006fb4#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds135 : List (List (BitVec 8)) :=
  [[0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8, 0x7f#8],
   [0x70#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8, 0x6c#8, 0x6e#8, 0x0#8],
   [0x70#8, 0x72#8, 0x69#8, 0x6e#8, 0x74#8, 0x6c#8, 0x6e#8, 0x0#8]]

theorem facts135 : ChainFacts (writeLog snapshotMem traceD135.log)
    (writeLog snapshotMem traceD135.log) traceD135.regs traceLds135 traceSeg135 := by
  have kind0 : (mkLine 0x80006ea0#64 0xb56733#32).kind = MKind.or := by decide
  have kind1 : (mkLine 0x80006ea4#64 0xfff00393#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x80006ea8#64 0x777713#32).kind = MKind.andi := by decide
  have kind3 : (mkLine 0x80006eb0#64 0x14797#32).kind = MKind.auipc := by decide
  have kind4 : (mkLine 0x80006eb4#64 0xdd07b783#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x80006eb8#64 0x53603#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80006ebc#64 0x5b683#32).kind = MKind.ld := by decide
  have kind7 : (mkLine 0x80006ec0#64 0xf672b3#32).kind = MKind.and := by decide
  have kind8 : (mkLine 0x80006ec4#64 0xf66333#32).kind = MKind.or := by decide
  have kind9 : (mkLine 0x80006ec8#64 0xf282b3#32).kind = MKind.add := by decide
  have kind10 : (mkLine 0x80006ecc#64 0x62e2b3#32).kind = MKind.or := by decide
  have kind11 : (mkLine 0x80006fb0#64 0x513#32).kind = MKind.addi := by decide
  simp only [traceSeg135, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000513
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00014797
    | exact DecodeTable.decode_00053603
    | exact DecodeTable.decode_0005b683
    | exact DecodeTable.decode_0062e2b3
    | exact DecodeTable.decode_00777713
    | exact DecodeTable.decode_00b56733
    | exact DecodeTable.decode_00f282b3
    | exact DecodeTable.decode_00f66333
    | exact DecodeTable.decode_00f672b3
    | exact DecodeTable.decode_0c071c63
    | exact DecodeTable.decode_0c729e63
    | exact DecodeTable.decode_dd07b783
    | exact DecodeTable.decode_fcd61ce3
    | exact DecodeTable.decode_fff00393
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run135 {c : Config} (h : TraceHolds traceD135 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD136 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg135 traceLds135 (by decide) facts135 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg135 (SegEvalState.init traceD135.regs traceLds135)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg135 (SegEvalState.init traceD135.regs traceLds135)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run135
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD136_01 : TraceData :=
  { pc := 0x80002c70#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x1#64), (9, 0x81000048#64), (10, 0x0#64), (11, 0x81000210#64), (12, 0x6e6c746e697270#64), (13, 0x6e6c746e697270#64), (14, 0x0#64), (15, 0x7f7f7f7f7f7f7f7f#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 157,
    out := #["\n"], payload := 0x0#4 }

def traceD136_02 : TraceData :=
  { pc := 0x80002c90#64,
    regs := [(1, 0x80002c6c#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x1#64), (9, 0x81000048#64), (10, 0x1#64), (11, 0x81000210#64), (12, 0x6e6c746e697270#64), (13, 0x6e6c746e697270#64), (14, 0x5#64), (15, 0x81000098#64), (16, 0x8#64), (17, 0x3#64), (18, 0x3#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 158,
    out := #["\n"], payload := 0x0#4 }

def traceD136_03 : TraceData :=
  { pc := 0x80002cb0#64,
    regs := [(1, 0x80003444#64), (2, 0x87fff2e0#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x820000a0#64), (9, 0x87fff7c0#64), (10, 0x1#64), (11, 0x81000210#64), (12, 0x6e6c746e697270#64), (13, 0x6e6c746e697270#64), (14, 0x81000210#64), (15, 0x80002f7c#64), (16, 0x8#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000210#64), (20, 0x81000000#64), (21, 0x87fff410#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 160,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg136_00 chain
  []
    terminator ⟨0x80002c6c#64, 0xfe0514e3#32, 0xe3#8, 0x14#8, 0x05#8, 0xfe#8, .br bop.BNE false, 10, 0, 0x1fe8#13, 0#21, 0#12⟩

def traceLds136_00 : List (List (BitVec 8)) :=
  []

theorem facts136_00 : ChainFacts (writeLog snapshotMem traceD136.log)
    (writeLog snapshotMem traceD136.log) traceD136.regs traceLds136_00 traceSeg136_00 := by
  simp only [traceSeg136_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_fe0514e3
    | (simp only [stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run136_00 {c : Config} (h : TraceHolds traceD136 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD136_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg136_00 traceLds136_00 (by decide) facts136_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg136_00 (SegEvalState.init traceD136.regs traceLds136_00)).log = traceStores.take 157
  have hw : (evalBlocks traceSeg136_00 (SegEvalState.init traceD136.regs traceLds136_00)).log = (traceStores.drop 157).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run136_00

#derive_case traceSeg136_01 chain
  [(0x80002c70#64, 0x10a3783#32),
   (0x80002c74#64, 0x141713#32),
   (0x80002c78#64, 0x870733#32),
   (0x80002c7c#64, 0x371713#32),
   (0x80002c80#64, 0xe787b3#32),
   (0x80002c84#64, 0x7b703#32),
   (0x80002c88#64, 0x100513#32),
   (0x80002c8c#64, 0xeab023#32)]

def traceLds136_01 : List (List (BitVec 8)) :=
  [[0x80#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x5#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts136_01 : ChainFacts (writeLog snapshotMem traceD136_01.log)
    (writeLog snapshotMem traceD136_01.log) traceD136_01.regs traceLds136_01 traceSeg136_01 := by
  have kind0 : (mkLine 0x80002c70#64 0x10a3783#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002c74#64 0x141713#32).kind = MKind.slli := by decide
  have kind2 : (mkLine 0x80002c78#64 0x870733#32).kind = MKind.add := by decide
  have kind3 : (mkLine 0x80002c7c#64 0x371713#32).kind = MKind.slli := by decide
  have kind4 : (mkLine 0x80002c80#64 0xe787b3#32).kind = MKind.add := by decide
  have kind5 : (mkLine 0x80002c84#64 0x7b703#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80002c88#64 0x100513#32).kind = MKind.addi := by decide
  have kind7 : (mkLine 0x80002c8c#64 0xeab023#32).kind = MKind.sd := by decide
  simp only [traceSeg136_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0007b703
    | exact DecodeTable.decode_00100513
    | exact DecodeTable.decode_00141713
    | exact DecodeTable.decode_00371713
    | exact DecodeTable.decode_00870733
    | exact DecodeTable.decode_00e787b3
    | exact DecodeTable.decode_00eab023
    | exact DecodeTable.decode_010a3783
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run136_01 {c : Config} (h : TraceHolds traceD136_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD136_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg136_01 traceLds136_01 (by decide) facts136_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 157 ++ (evalBlocks traceSeg136_01 (SegEvalState.init traceD136_01.regs traceLds136_01)).log = traceStores.take 158
  have hw : (evalBlocks traceSeg136_01 (SegEvalState.init traceD136_01.regs traceLds136_01)).log = (traceStores.drop 157).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run136_01

#derive_case traceSeg136_02 chain
  [(0x80002c90#64, 0x87b703#32),
   (0x80002c94#64, 0xeab423#32),
   (0x80002c98#64, 0x107b783#32),
   (0x80002c9c#64, 0xfab823#32),
   (0x80002ca0#64, 0x3813083#32),
   (0x80002ca4#64, 0x3013403#32),
   (0x80002ca8#64, 0x2813483#32),
   (0x80002cac#64, 0x2013903#32)]

def traceLds136_02 : List (List (BitVec 8)) :=
  [[0x10#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x7c#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x44#8, 0x34#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xa0#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xc0#8, 0xf7#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts136_02 : ChainFacts (writeLog snapshotMem traceD136_02.log)
    (writeLog snapshotMem traceD136_02.log) traceD136_02.regs traceLds136_02 traceSeg136_02 := by
  have kind0 : (mkLine 0x80002c90#64 0x87b703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002c94#64 0xeab423#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80002c98#64 0x107b783#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80002c9c#64 0xfab823#32).kind = MKind.sd := by decide
  have kind4 : (mkLine 0x80002ca0#64 0x3813083#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x80002ca4#64 0x3013403#32).kind = MKind.ld := by decide
  have kind6 : (mkLine 0x80002ca8#64 0x2813483#32).kind = MKind.ld := by decide
  have kind7 : (mkLine 0x80002cac#64 0x2013903#32).kind = MKind.ld := by decide
  simp only [traceSeg136_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_0087b703
    | exact DecodeTable.decode_00eab423
    | exact DecodeTable.decode_00fab823
    | exact DecodeTable.decode_0107b783
    | exact DecodeTable.decode_02013903
    | exact DecodeTable.decode_02813483
    | exact DecodeTable.decode_03013403
    | exact DecodeTable.decode_03813083
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run136_02 {c : Config} (h : TraceHolds traceD136_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD136_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg136_02 traceLds136_02 (by decide) facts136_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 158 ++ (evalBlocks traceSeg136_02 (SegEvalState.init traceD136_02.regs traceLds136_02)).log = traceStores.take 160
  have hw : (evalBlocks traceSeg136_02 (SegEvalState.init traceD136_02.regs traceLds136_02)).log = (traceStores.drop 158).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run136_02

#derive_case traceSeg136_03 chain
  [(0x80002cb0#64, 0x1813983#32),
   (0x80002cb4#64, 0x1013a03#32),
   (0x80002cb8#64, 0x813a83#32),
   (0x80002cbc#64, 0x4010113#32)]
    terminator ⟨0x80002cc0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds136_03 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x1#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts136_03 : ChainFacts (writeLog snapshotMem traceD136_03.log)
    (writeLog snapshotMem traceD136_03.log) traceD136_03.regs traceLds136_03 traceSeg136_03 := by
  have kind0 : (mkLine 0x80002cb0#64 0x1813983#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80002cb4#64 0x1013a03#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80002cb8#64 0x813a83#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80002cbc#64 0x4010113#32).kind = MKind.addi := by decide
  simp only [traceSeg136_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00813a83
    | exact DecodeTable.decode_01013a03
    | exact DecodeTable.decode_01813983
    | exact DecodeTable.decode_04010113
    | (simp only [kind0, kind1, kind2, kind3, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run136_03 {c : Config} (h : TraceHolds traceD136_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD137 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg136_03 traceLds136_03 (by decide) facts136_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 160 ++ (evalBlocks traceSeg136_03 (SegEvalState.init traceD136_03.regs traceLds136_03)).log = traceStores.take 160
  have hw : (evalBlocks traceSeg136_03 (SegEvalState.init traceD136_03.regs traceLds136_03)).log = (traceStores.drop 160).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run136_03
theorem run136 {c : Config} (h : TraceHolds traceD136 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD137 c' := by
  obtain ⟨c0, s0, h0⟩ := run136_00 h
  obtain ⟨c1, s1, h1⟩ := run136_01 h0
  obtain ⟨c2, s2, h2⟩ := run136_02 h1
  obtain ⟨c3, s3, h3⟩ := run136_03 h2
  exact ⟨c3, (((s0).trans s1).trans s2).trans s3, h3⟩

#print axioms run136
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg137 chain
  []
    terminator ⟨0x80003444#64, 0x32050ee3#32, 0xe3#8, 0x0e#8, 0x05#8, 0x32#8, .br bop.BEQ false, 10, 0, 0x0b3c#13, 0#21, 0#12⟩ ;;
  [(0x80003448#64, 0xf013683#32),
   (0x8000344c#64, 0xf813703#32),
   (0x80003450#64, 0x10013783#32),
   (0x80003454#64, 0x43813083#32),
   (0x80003458#64, 0x43013403#32),
   (0x8000345c#64, 0xd4b023#32),
   (0x80003460#64, 0xe4b423#32),
   (0x80003464#64, 0xf4b823#32),
   (0x80003468#64, 0x42013903#32),
   (0x8000346c#64, 0x48513#32),
   (0x80003470#64, 0x42813483#32),
   (0x80003474#64, 0x44010113#32)]
    terminator ⟨0x80003478#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

def traceLds137 : List (List (BitVec 8)) :=
  [[0x5#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x7c#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xc0#8, 0x31#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x80#8, 0x0#8, 0x0#8, 0x82#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0xfe#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0xb0#8, 0xfb#8, 0xff#8, 0x87#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts137 : ChainFacts (writeLog snapshotMem traceD137.log)
    (writeLog snapshotMem traceD137.log) traceD137.regs traceLds137 traceSeg137 := by
  have kind0 : (mkLine 0x80003448#64 0xf013683#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x8000344c#64 0xf813703#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x80003450#64 0x10013783#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80003454#64 0x43813083#32).kind = MKind.ld := by decide
  have kind4 : (mkLine 0x80003458#64 0x43013403#32).kind = MKind.ld := by decide
  have kind5 : (mkLine 0x8000345c#64 0xd4b023#32).kind = MKind.sd := by decide
  have kind6 : (mkLine 0x80003460#64 0xe4b423#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x80003464#64 0xf4b823#32).kind = MKind.sd := by decide
  have kind8 : (mkLine 0x80003468#64 0x42013903#32).kind = MKind.ld := by decide
  have kind9 : (mkLine 0x8000346c#64 0x48513#32).kind = MKind.addi := by decide
  have kind10 : (mkLine 0x80003470#64 0x42813483#32).kind = MKind.ld := by decide
  have kind11 : (mkLine 0x80003474#64 0x44010113#32).kind = MKind.addi := by decide
  simp only [traceSeg137, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00008067
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_00d4b023
    | exact DecodeTable.decode_00e4b423
    | exact DecodeTable.decode_00f4b823
    | exact DecodeTable.decode_0f013683
    | exact DecodeTable.decode_0f813703
    | exact DecodeTable.decode_10013783
    | exact DecodeTable.decode_32050ee3
    | exact DecodeTable.decode_42013903
    | exact DecodeTable.decode_42813483
    | exact DecodeTable.decode_43013403
    | exact DecodeTable.decode_43813083
    | exact DecodeTable.decode_44010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, kind8, kind9, kind10, kind11, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run137 {c : Config} (h : TraceHolds traceD137 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD138 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg137 traceLds137 (by decide) facts137 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 160 ++ (evalBlocks traceSeg137 (SegEvalState.init traceD137.regs traceLds137)).log = traceStores.take 163
  have hw : (evalBlocks traceSeg137 (SegEvalState.init traceD137.regs traceLds137)).log = (traceStores.drop 160).take 3 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run137
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

def traceD138_01 : TraceData :=
  { pc := 0x800031cc#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x82000080#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x81000210#64), (12, 0x6e6c746e697270#64), (13, 0x5#64), (14, 0x20#64), (15, 0x0#64), (16, 0x8#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 163,
    out := #["\n"], payload := 0x0#4 }

def traceD138_02 : TraceData :=
  { pc := 0x80003254#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x82000080#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x81000210#64), (12, 0x6e6c746e697270#64), (13, 0x81000000#64), (14, 0x20#64), (15, 0x0#64), (16, 0x0#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 164,
    out := #["\n"], payload := 0x0#4 }

def traceD138_03 : TraceData :=
  { pc := 0x80003274#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x82000080#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x0#64), (12, 0x6e6c746e697270#64), (13, 0x81000210#64), (14, 0x5#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 167,
    out := #["\n"], payload := 0x0#4 }

def traceD138_04 : TraceData :=
  { pc := 0x800039e0#64,
    regs := [(1, 0x800031c0#64), (2, 0x87fff760#64), (3, 0x8001b510#64), (4, 0x0#64), (5, 0x7fffffffffffffff#64), (6, 0x7f7f7f7f7f7f7f7f#64), (7, 0xffffffffffffffff#64), (8, 0x82000080#64), (9, 0x87fffbb0#64), (10, 0x87fff7c0#64), (11, 0x0#64), (12, 0x5#64), (13, 0x81000210#64), (14, 0x5#64), (15, 0x0#64), (16, 0x80002f7c#64), (17, 0x3#64), (18, 0x87fffe10#64), (19, 0x81000000#64), (20, 0x1#64), (21, 0x0#64), (22, 0x8001b970#64), (23, 0x0#64), (24, 0x0#64), (25, 0x0#64), (26, 0x0#64), (27, 0x0#64), (28, 0x0#64), (29, 0x0#64), (30, 0x0#64), (31, 0x0#64)],
    log := traceStores.take 167,
    out := #["\n"], payload := 0x0#4 }


#derive_case traceSeg138_00 chain
  [(0x800031c0#64, 0x1842783#32),
   (0x800031c4#64, 0x2000713#32)]
    terminator ⟨0x800031c8#64, 0x5ef744e3#32, 0xe3#8, 0x44#8, 0xf7#8, 0x5e#8, .br bop.BLT false, 14, 15, 0x0de8#13, 0#21, 0#12⟩

def traceLds138_00 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts138_00 : ChainFacts (writeLog snapshotMem traceD138.log)
    (writeLog snapshotMem traceD138.log) traceD138.regs traceLds138_00 traceSeg138_00 := by
  have kind0 : (mkLine 0x800031c0#64 0x1842783#32).kind = MKind.lw := by decide
  have kind1 : (mkLine 0x800031c4#64 0x2000713#32).kind = MKind.addi := by decide
  simp only [traceSeg138_00, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_01842783
    | exact DecodeTable.decode_02000713
    | exact DecodeTable.decode_5ef744e3
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run138_00 {c : Config} (h : TraceHolds traceD138 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD138_01 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg138_00 traceLds138_00 (by decide) facts138_00 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 163 ++ (evalBlocks traceSeg138_00 (SegEvalState.init traceD138.regs traceLds138_00)).log = traceStores.take 163
  have hw : (evalBlocks traceSeg138_00 (SegEvalState.init traceD138.regs traceLds138_00)).log = (traceStores.drop 163).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run138_00

#derive_case traceSeg138_01 chain
  [(0x800031cc#64, 0x3f713c23#32),
   (0x800031d0#64, 0x13683#32),
   (0x800031d4#64, 0x813#32)]
    terminator ⟨0x800031d8#64, 0x06f05e63#32, 0x63#8, 0x5e#8, 0xf0#8, 0x06#8, .br bop.BGE true, 0, 15, 0x007c#13, 0#21, 0#12⟩

def traceLds138_01 : List (List (BitVec 8)) :=
  [[0x0#8, 0x0#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts138_01 : ChainFacts (writeLog snapshotMem traceD138_01.log)
    (writeLog snapshotMem traceD138_01.log) traceD138_01.regs traceLds138_01 traceSeg138_01 := by
  have kind0 : (mkLine 0x800031cc#64 0x3f713c23#32).kind = MKind.sd := by decide
  have kind1 : (mkLine 0x800031d0#64 0x13683#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x800031d4#64 0x813#32).kind = MKind.addi := by decide
  simp only [traceSeg138_01, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00000813
    | exact DecodeTable.decode_00013683
    | exact DecodeTable.decode_06f05e63
    | exact DecodeTable.decode_3f713c23
    | (simp only [kind0, kind1, kind2, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run138_01 {c : Config} (h : TraceHolds traceD138_01 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD138_02 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg138_01 traceLds138_01 (by decide) facts138_01 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 163 ++ (evalBlocks traceSeg138_01 (SegEvalState.init traceD138_01.regs traceLds138_01)).log = traceStores.take 164
  have hw : (evalBlocks traceSeg138_01 (SegEvalState.init traceD138_01.regs traceLds138_01)).log = (traceStores.drop 163).take 1 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run138_01

#derive_case traceSeg138_02 chain
  [(0x80003254#64, 0x6013703#32),
   (0x80003258#64, 0x6813683#32),
   (0x8000325c#64, 0x7013803#32),
   (0x80003260#64, 0x442583#32),
   (0x80003264#64, 0x6e13c23#32),
   (0x80003268#64, 0x6012703#32),
   (0x8000326c#64, 0x8d13023#32),
   (0x80003270#64, 0x9013423#32)]

def traceLds138_02 : List (List (BitVec 8)) :=
  [[0x5#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x10#8, 0x2#8, 0x0#8, 0x81#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x7c#8, 0x2f#8, 0x0#8, 0x80#8, 0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x0#8, 0x0#8, 0x0#8, 0x0#8],
   [0x5#8, 0x0#8, 0x0#8, 0x0#8]]

theorem facts138_02 : ChainFacts (writeLog snapshotMem traceD138_02.log)
    (writeLog snapshotMem traceD138_02.log) traceD138_02.regs traceLds138_02 traceSeg138_02 := by
  have kind0 : (mkLine 0x80003254#64 0x6013703#32).kind = MKind.ld := by decide
  have kind1 : (mkLine 0x80003258#64 0x6813683#32).kind = MKind.ld := by decide
  have kind2 : (mkLine 0x8000325c#64 0x7013803#32).kind = MKind.ld := by decide
  have kind3 : (mkLine 0x80003260#64 0x442583#32).kind = MKind.lw := by decide
  have kind4 : (mkLine 0x80003264#64 0x6e13c23#32).kind = MKind.sd := by decide
  have kind5 : (mkLine 0x80003268#64 0x6012703#32).kind = MKind.lw := by decide
  have kind6 : (mkLine 0x8000326c#64 0x8d13023#32).kind = MKind.sd := by decide
  have kind7 : (mkLine 0x80003270#64 0x9013423#32).kind = MKind.sd := by decide
  simp only [traceSeg138_02, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00442583
    | exact DecodeTable.decode_06012703
    | exact DecodeTable.decode_06013703
    | exact DecodeTable.decode_06813683
    | exact DecodeTable.decode_06e13c23
    | exact DecodeTable.decode_07013803
    | exact DecodeTable.decode_08d13023
    | exact DecodeTable.decode_09013423
    | (simp only [kind0, kind1, kind2, kind3, kind4, kind5, kind6, kind7, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run138_02 {c : Config} (h : TraceHolds traceD138_02 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD138_03 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg138_02 traceLds138_02 (by decide) facts138_02 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 164 ++ (evalBlocks traceSeg138_02 (SegEvalState.init traceD138_02.regs traceLds138_02)).log = traceStores.take 167
  have hw : (evalBlocks traceSeg138_02 (SegEvalState.init traceD138_02.regs traceLds138_02)).log = (traceStores.drop 164).take 3 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run138_02

#derive_case traceSeg138_03 chain
  [(0x80003274#64, 0x500613#32),
   (0x80003278#64, 0x58b93#32)]
    terminator ⟨0x8000327c#64, 0x76c70263#32, 0x63#8, 0x02#8, 0xc7#8, 0x76#8, .br bop.BEQ true, 14, 12, 0x0764#13, 0#21, 0#12⟩

def traceLds138_03 : List (List (BitVec 8)) :=
  []

theorem facts138_03 : ChainFacts (writeLog snapshotMem traceD138_03.log)
    (writeLog snapshotMem traceD138_03.log) traceD138_03.regs traceLds138_03 traceSeg138_03 := by
  have kind0 : (mkLine 0x80003274#64 0x500613#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80003278#64 0x58b93#32).kind = MKind.addi := by decide
  simp only [traceSeg138_03, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00058b93
    | exact DecodeTable.decode_00500613
    | exact DecodeTable.decode_76c70263
    | (simp only [kind0, kind1, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run138_03 {c : Config} (h : TraceHolds traceD138_03 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD138_04 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg138_03 traceLds138_03 (by decide) facts138_03 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 167 ++ (evalBlocks traceSeg138_03 (SegEvalState.init traceD138_03.regs traceLds138_03)).log = traceStores.take 167
  have hw : (evalBlocks traceSeg138_03 (SegEvalState.init traceD138_03.regs traceLds138_03)).log = (traceStores.drop 167).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run138_03

#derive_case traceSeg138_04 chain
  [(0x800039e0#64, 0x58713#32),
   (0x800039e4#64, 0x78613#32),
   (0x800039e8#64, 0x90593#32),
   (0x800039ec#64, 0xf010693#32),
   (0x800039f0#64, 0x48513#32)]

def traceLds138_04 : List (List (BitVec 8)) :=
  []

theorem facts138_04 : ChainFacts (writeLog snapshotMem traceD138_04.log)
    (writeLog snapshotMem traceD138_04.log) traceD138_04.regs traceLds138_04 traceSeg138_04 := by
  have kind0 : (mkLine 0x800039e0#64 0x58713#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x800039e4#64 0x78613#32).kind = MKind.addi := by decide
  have kind2 : (mkLine 0x800039e8#64 0x90593#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x800039ec#64 0xf010693#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x800039f0#64 0x48513#32).kind = MKind.addi := by decide
  simp only [traceSeg138_04, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00048513
    | exact DecodeTable.decode_00058713
    | exact DecodeTable.decode_00078613
    | exact DecodeTable.decode_00090593
    | exact DecodeTable.decode_0f010693
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run138_04 {c : Config} (h : TraceHolds traceD138_04 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD139 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg138_04 traceLds138_04 (by decide) facts138_04 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 167 ++ (evalBlocks traceSeg138_04 (SegEvalState.init traceD138_04.regs traceLds138_04)).log = traceStores.take 167
  have hw : (evalBlocks traceSeg138_04 (SegEvalState.init traceD138_04.regs traceLds138_04)).log = (traceStores.drop 167).take 0 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run138_04
theorem run138 {c : Config} (h : TraceHolds traceD138 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD139 c' := by
  obtain ⟨c0, s0, h0⟩ := run138_00 h
  obtain ⟨c1, s1, h1⟩ := run138_01 h0
  obtain ⟨c2, s2, h2⟩ := run138_02 h1
  obtain ⟨c3, s3, h3⟩ := run138_03 h2
  obtain ⟨c4, s4, h4⟩ := run138_04 h3
  exact ⟨c4, ((((s0).trans s1).trans s2).trans s3).trans s4, h4⟩

#print axioms run138
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

theorem facts139 : TraceCallFacts traceD139 0x800e7#32
    (instruction.JALR (0x0#12, gprIdx 16, gprIdx 1)) 0xe7#8 0x0#8 0x8#8 0x0#8 where
  byte0 := by rw [snapshot_logRead]; decide
  byte1 := by rw [snapshot_logRead]; decide
  byte2 := by rw [snapshot_logRead]; decide
  byte3 := by rw [snapshot_logRead]; decide
  lower := by decide
  upper := by decide
  aligned := by decide
  uncompressed := by decide
  word := by decide
  decode := DecodeTable.decode_000800e7

theorem run139 {c : Config} (h : TraceHolds traceD139 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD140 c' := by
  obtain ⟨c', hs, hp⟩ := h.jalr 0x800e7#32 0x0#12 16 0x80002f7c#64
    0xe7#8 0x0#8 0x8#8 0x0#8 facts139
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨c', hs, hp.rebase (by constructor <;> first | rfl | decide)⟩

#print axioms run139
end Vsa.Sim.OutputAliasLoaded

open LeanRV64DExecutable Vsa Vsa.Machine Vsa.MemRepr
namespace Vsa.Sim.OutputAliasLoaded

#derive_case traceSeg140 chain
  [(0x80002f7c#64, 0xfd010113#32),
   (0x80002f80#64, 0x2813023#32),
   (0x80002f84#64, 0x50413#32),
   (0x80002f88#64, 0x10513#32),
   (0x80002f8c#64, 0x2113423#32)]

def traceLds140 : List (List (BitVec 8)) :=
  []

theorem facts140 : ChainFacts (writeLog snapshotMem traceD140.log)
    (writeLog snapshotMem traceD140.log) traceD140.regs traceLds140 traceSeg140 := by
  have kind0 : (mkLine 0x80002f7c#64 0xfd010113#32).kind = MKind.addi := by decide
  have kind1 : (mkLine 0x80002f80#64 0x2813023#32).kind = MKind.sd := by decide
  have kind2 : (mkLine 0x80002f84#64 0x50413#32).kind = MKind.addi := by decide
  have kind3 : (mkLine 0x80002f88#64 0x10513#32).kind = MKind.addi := by decide
  have kind4 : (mkLine 0x80002f8c#64 0x2113423#32).kind = MKind.sd := by decide
  simp only [traceSeg140, ChainFacts, BBlockFacts, ProgFactsM,
    BytePinsM, MemFacts, LPins4, LPins8, TermPins, TermFactsO, BytePinsT, TermFactsT, and_true]
  repeat' apply And.intro
  all_goals first
    | exact True.intro
    | exact DecodeTable.decode_00010513
    | exact DecodeTable.decode_00050413
    | exact DecodeTable.decode_02113423
    | exact DecodeTable.decode_02813023
    | exact DecodeTable.decode_fd010113
    | (simp only [kind0, kind1, kind2, kind3, kind4, stepMemM, applyW_getElem?_entryRead, writeLog_getElem?_logRead, snapshot_lookup]; decide)
    | decide

theorem run140 {c : Config} (h : TraceHolds traceD140 c) :
    ∃ c', Steps c c' ∧ TraceHolds traceD141 c' := by
  obtain ⟨c', hs, hp⟩ := h.segment traceSeg140 traceLds140 (by decide) facts140 (by decide) (by decide)
  refine ⟨c', hs, hp.rebase ?_⟩
  refine { pc := by decide, log := ?_, out := rfl, payload := rfl, regs := by decide }
  change traceStores.take 167 ++ (evalBlocks traceSeg140 (SegEvalState.init traceD140.regs traceLds140)).log = traceStores.take 169
  have hw : (evalBlocks traceSeg140 (SegEvalState.init traceD140.regs traceLds140)).log = (traceStores.drop 167).take 2 := by decide
  rw [hw]
  exact List.take_add.symm

#print axioms run140
end Vsa.Sim.OutputAliasLoaded
